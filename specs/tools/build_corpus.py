#!/usr/bin/env python3
"""Assemble spec/*/spec.lean files into corpus.lean (the registry).

Numeric directories cannot be Lean module names, so the corpus is a
concatenation with #line directives mapping errors back to the
original files. Each spec file contributes an AO_<Name> : AOReg def.
"""
import os, re, sys

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
specdir = os.path.join(root, "spec")
files = []
for dirpath, _, fnames in os.walk(specdir):
    for fn in fnames:
        if fn == "spec.lean":
            files.append(os.path.join(dirpath, fn))
files.sort()

SMOKE = '''
def theReg : AOReg := {entries}

def exampleF : List FStep := [alg|
  1. If true, then
    ┊ a. Let x be 1.
  2. Return x.
]

def callDemoF : List FStep := [alg|
  1. Let c be IsCallable(true).
  2. Return c.
]

def retDemoF : List FStep := [alg|
  1. Let r be IsCallable(true).
  2. Return true.
]

def primDemoF : List FStep := [alg|
  1. Let p be ToPrimitive(undefined).
  2. Return p.
]


/- For each over a spec List: iterate to the 2nd element, return through
   the loop (the pending kLoopS marker is discarded by the return). -/
def forEachDemoF : List FStep := [alg|
  1. Let xs be « "a", "b" ».
  2. For each element x of xs, do
    ┊ a. If x is ~b~, Return x.
  3. Return undefined.
]


/- A real two-argument call: OrdinaryToPrimitive(undefined, ~string~) enters
   the registry with both params bound; the loop iterates over both
   method names; stubbed Get -> undefined -> IsCallable false; the
   loop exhausts; step 4 throws. -/
def otpDemoF : List FStep := [alg|
  1. Let r be OrdinaryToPrimitive(undefined, ~string~).
  2. Return r.
]

#eval checkRun (renest otpDemoF)

/- Omission: fewer args than params — preferredType stays unbound,
   the not-present defaulting path runs (already shown by primDemoF). -/
def omitDemoF : List FStep := [alg|
  1. Let q be ToPrimitive(undefined).
  2. Return q.
]
#eval agree2 theReg (build exampleF)

/- Frame machine on the same corpus -/
#eval fsteps theReg 100 (fmOf (build exampleF))
#eval fsteps theReg 100 (fmOf (build callDemoF))
#eval fsteps theReg 100 (fmOf (build retDemoF))
#eval fsteps theReg 100 (fmOf (build primDemoF))
#eval fsteps theReg 100 (fmOf (build forEachDemoF))
/- otpDemoF: 2-arg call, loop over both names, Throw at step 4 —
   the throw is now a VALUE: pThrowC + kRet returns the completion
   through the call, the self-test at the call site propagates it -/
#eval fsteps theReg 300 (fmOf (build otpDemoF))
#eval agree2 theReg (build exampleF)
#eval agree2 theReg (build forEachDemoF)

/- original KM agreement -/

/- 5.2.4.1 Completion, live: the completion is returned UNCHANGED by
   the bare Return (kWrapIfBare) — normal in → normal out, abrupt in
   → abrupt out (identity, as the spec says) -/
def completionDemoF : List FStep := [alg|
  1. Let c be ? «Completion»(x).
  2. Return c.
]
#eval fsteps theReg 100 (.frames [⟨compileSteps (build completionDemoF),
    [("x", .compl Bool.false (JSValue.number 5))], [], "«top»"⟩] emptyHeap 0)
#eval fsteps theReg 100 (.frames [⟨compileSteps (build completionDemoF),
    [("x", .compl Bool.true JSValue.undefined)], [], "«top»"⟩] emptyHeap 0)

/- The full lookup chain, live: GetV -> ToObject -> OrdinaryGet ->
    native MOP. A heap object with own property "x" = 42,
    reached via propertyKey "x". -/
def lookupDemoF : List FStep := [alg|
  1. Let m be GetV(input, propertyKey).
  2. Return m.
]

/- Issue #1 regression: kRepeatTest must preserve `rest` across loop
   iterations. The loop body binds "done" on its first (only) run, the
   condition then goes false, and the machine must fall THROUGH to the
   return of 42 — before the fix, rest was dropped at the first
   iteration and the machine felled. -/
def loopBody : List Instr := [.kEval (.const JSValue.undefined), .kSet "done"]
def loopRest : List Instr :=
  [.kEval (.const (JSValue.number 42)), .kPrim1 .pWrapC, .kRet]
#eval fsteps theReg 100
    (.frames [⟨.kRepeatWhile (Expr.varNotPresent "done") loopBody :: loopRest, [], [], "«top»"⟩]
      emptyHeap 0)
/- GetMethod on a non-callable, non-undefined value: spec says
   step 4 throws a TypeError (compl true undefined). -/
def getMethodDemoF : List FStep := [alg|
  1. Let m be GetMethod(input, propertyKey).
  2. Return m.
]

def demoHeap : Heap :=
  heapSet emptyHeap 0 {
    (objWith .ordinary none) with
      props := [(PKey.str "x",
        Descriptor.mk (some (JSValue.number 42)) (some Bool.true)
          none none (some Bool.true) (some Bool.true))] }

#eval checkRun (renest lookupDemoF)
#eval fsteps theReg
    1000 (.frames [⟨compileSteps (build lookupDemoF),
        [("input", .obj 0), ("propertyKey", .str "x")], [], "«top»"⟩] demoHeap 1)
#eval fsteps theReg
    1000 (.frames [⟨compileSteps (build getMethodDemoF),
         [("input", .obj 0), ("propertyKey", .str "x")], [], "«top»"⟩] demoHeap 1)

/- proto-chain live: GetV on the child misses, the zero-arg
   obj.[[GetPrototypeOf]]() call dispatches (new in this corpus: the
   old field-read workaround returned undefined at runtime), and
   parent.[[Get]] returns 42 from the parent's own property. -/
def protoHeap : Heap :=
  heapSet (heapSet emptyHeap 0 {
    (objWith .ordinary none) with
      props := [(PKey.str "x",
        Descriptor.mk (some (JSValue.number 42)) (some Bool.true)
          none none (some Bool.true) (some Bool.true))]}) 1
    {(objWith .ordinary (some 0)) with props := []}
#eval fsteps theReg 1000 (.frames [⟨compileSteps (build lookupDemoF),
    [("input", .obj 1), ("propertyKey", .str "x")], [], "«top»"⟩] protoHeap 2)

/- upward conversions, end to end: all-registry chains -/
def rocDemoF : List FStep := [alg|
  1. Let m be RequireObjectCoercible(true).
  2. Return m.
]
#eval fsteps theReg 100 (fmOf (build rocDemoF))

def tpkDemoF : List FStep := [alg|
  1. Let k be ToPropertyKey(key).
  2. Return k.
]
/- ToPrimitive("hi") -> "hi"; not a Symbol; ! ToString("hi") -> "hi" -/
#eval fsteps theReg 200 (.frames [⟨compileSteps (build tpkDemoF),
    [("key", .str "hi")], [], "«top»"⟩] emptyHeap 0)

def toStringDemoF : List FStep := [alg|
  1. Let s be ToString(x).
  2. Return s.
]
/- string input: step 1 directly -/
#eval fsteps theReg 200 (.frames [⟨compileSteps (build toStringDemoF),
    [("x", .str "hi")], [], "«top»"⟩] emptyHeap 0)
/- object receiver: the full chain — GetMethod -> GetV -> ToObject ->
   [[Get]] -> OrdinaryGet -> [[GetOwnProperty]] / [[GetPrototypeOf]]
   -> OrdinaryToPrimitive -> Throw at step 4 (no methods on a bare
   object), propagated back out -/
#eval fsteps theReg 1000 (.frames [⟨compileSteps (build toStringDemoF),
    [("x", .obj 0)], [], "«top»"⟩] demoHeap 1)

def toNumericDemoF : List FStep := [alg|
  1. Let n be ToNumeric(value).
  2. Return n.
]
/- ToPrimitive(5) -> 5; not a BigInt; ToNumber -> native stub (undefined) -/
#eval fsteps theReg 200 (.frames [⟨compileSteps (build toNumericDemoF),
    [("value", .number 5)], [], "«top»"⟩] emptyHeap 0)

/- ===== static typing: signature table (payload types) =====
   Delivery is always a completion; the table types the payload.
   To be extracted from spec.html headers eventually (diff_spec-style). -/
def corpusSigs : SigTable := [
  -- set-typed signatures (params: language values unless noted)
  -- boolean returns are the canonical singleton union (boolU), never
  -- a mask: any-bool − is-true = is-false in every spelling
  ("IsCallable",          ([.val langV], boolU)),
  ("IsConstructor",       ([.val langV], boolU)),
  ("IsDataDescriptor",    ([.descAny], boolU)),
  ("IsAccessorDescriptor",([.descAny], boolU)),
  ("IsGenericDescriptor", ([.descAny], boolU)),
  -- the coercers provably return non-objects or throw (every return
  -- is refined by an is-not-an-Object split or a throw): the tight
  -- return type is a fact, and it discharges ToString's step 11
  ("OrdinaryToPrimitive", ([.val langV, .oneOf [.str "string", .str "number"]], .val (langV - cObj))),
  ("ToPrimitive",         ([.val langV, .union [.notPresent, .oneOf [.str "string", .str "number"]]], .val (langV - cObj))),
  ("ToObject",            ([.val langV], .val cObj)),
  ("GetV",                ([.val langV, .val cStr], .val langV)),
  ("GetMethod",           ([.val langV, .val cStr], .val langV)),
  ("OrdinaryGet",         ([.val cObj, .val langV, .val langV], .val langV)),
  -- the spec's first AO (5.2.4.1): completion in, same completion
  -- out (identity); the ?-delivery yields the payload. The assert
  -- discharges via the completion-record split (false-world empty).
  ("Completion",          ([.complN (.val anyV)], .val anyV)),
  ("RequireObjectCoercible", ([.val langV], .val cUndef)),   -- unused ~ undefined
  ("ToNumeric",           ([.val langV], .val cNum)),        -- no BigInts: Number path only
  ("ToString",            ([.val langV], .val cStr)),
  ("ToPropertyKey",       ([.val langV], .val cStr)),        -- no Symbols: String path only
  -- prim-named calls the machine handles natively on registry miss:
  ("Get",                 ([.val langV, .val langV], .val langV)),
  ("Call",                ([.val langV, .val langV, .val cList], .val langV)),
  -- number-tower stubs until the registry grows them
  ("ToNumber",            ([.val langV], .val cNum)),
  ("Number::toString",    ([.val cNum, .val cNum], .val cStr)),
  ("BigInt::toString",    ([.val cNum, .val cNum], .val cStr))
]

/- the issue-#1 regression loop typechecks too: body neutral, cond boolean -/
#eval typecheckSeq corpusSigs (.val langV) []
    (.kRepeatWhile (Expr.varNotPresent "done") loopBody :: loopRest)

-- every registry body typechecks against its declared signature
-- (prints the first rejection with reason + stack, or none)
#eval typecheckReg corpusSigs theReg
#eval typecheckRegOk corpusSigs theReg

-- signature well-formedness: every desc atom in the table obeys the
-- disjointness invariant (no data field together with an accessor field)
def sigWf : SigTable → Bool := fun sigs =>
  sigs.all (fun (_, (ps, _)) =>
    (ps ++ []).all (fun t =>
      (atoms t).all (fun atom => match atom with
        | .desc fs => wfFs fs
        | _ => Bool.true)))
#eval sigWf corpusSigs

-- per-AO: certificate AND assumption-freedom — a nonzero debt must
-- fail the gate loudly, not just certify-with-debt invisibly.
-- Current state: 16/16 assumption-free. History: ToPrimitive-iii and
-- OrdinaryGet-4 fell to the correlated predicate splits and the
-- completed-descriptor GetOwnProperty result; Completion-1 to the
-- completion-record split; ToString-9 to canonical singleton
-- booleans (any-bool − is-true = is-false); ToString-11 to the
-- honest non-object return types of the coercers.
def assumesOf (sigs : SigTable) (name : «String») (ps : List «String»)
    (body : List Instr) : Nat :=
  match checkSeq sigs (sigRetTy sigs name) [{ Γ := zipTy ps (sigParams sigs name), σ := [] }] body with
  | .flows f => f.assumes.length
  | _ => 999
#eval assumesOf corpusSigs "IsCallable" ["arg"] (compileSteps (build isCallable7_2_3))
#eval assumesOf corpusSigs "IsConstructor" ["arg"] (compileSteps (build isConstructor7_2_4))
#eval assumesOf corpusSigs "IsDataDescriptor" ["propertyDesc"] (compileSteps (build isDataDescriptor6_2_6_2))
#eval assumesOf corpusSigs "IsAccessorDescriptor" ["propertyDesc"] (compileSteps (build isAccessorDescriptor6_2_6_1))
#eval assumesOf corpusSigs "IsGenericDescriptor" ["propertyDesc"] (compileSteps (build isGenericDescriptor6_2_6_3))
#eval assumesOf corpusSigs "Completion" ["completionRecord"] (compileSteps (build completion5_2_4_1))
#eval assumesOf corpusSigs "OrdinaryToPrimitive" ["obj", "hint"] (compileSteps (build ordinaryToPrimitive7_1_1_1))
#eval assumesOf corpusSigs "ToPrimitive" ["input", "preferredType"] (compileSteps (build toPrimitive7_1_1))
#eval assumesOf corpusSigs "RequireObjectCoercible" ["arg"] (compileSteps (build requireObjectCoercible7_2_1))
#eval assumesOf corpusSigs "ToNumeric" ["arg"] (compileSteps (build toNumeric7_1_3))
#eval assumesOf corpusSigs "ToString" ["arg"] (compileSteps (build toString7_1_19))
#eval assumesOf corpusSigs "ToPropertyKey" ["arg"] (compileSteps (build toPropertyKey7_1_21))
#eval assumesOf corpusSigs "ToObject" ["arg"] (compileSteps (build toObject7_1_20))
#eval assumesOf corpusSigs "GetV" ["value", "propertyKey"] (compileSteps (build getV7_3_3))
#eval assumesOf corpusSigs "GetMethod" ["value", "propertyKey"] (compileSteps (build getMethod7_3_10))
#eval assumesOf corpusSigs "OrdinaryGet" ["obj", "propertyKey", "receiver"] (compileSteps (build ordinaryGet10_1_8_1))
-- the demos typecheck as frames (Γ = params, or empty for top-level)
#eval typecheckSeq corpusSigs (.val langV) [("input", .val langV), ("propertyKey", .val cStr)] (compileSteps (build lookupDemoF))
#eval typecheckSeq corpusSigs (.val langV) [("input", .val langV), ("propertyKey", .val cStr)] (compileSteps (build getMethodDemoF))
#eval typecheckSeq corpusSigs (.val langV) [("key", .val cStr)] (compileSteps (build tpkDemoF))
#eval typecheckSeq corpusSigs (.val langV) [("x", .val cStr)] (compileSteps (build toStringDemoF))
#eval typecheckSeq corpusSigs (.val langV) [("x", .val cObj)] (compileSteps (build toStringDemoF))
/- Completion as a frame: ?-delivery of a complN-typed variable
   (bug1 below is the hand-written UNWRAP-then-kRet shape, rejected:
   kRet demands a completion) -/
#eval typecheckSeq corpusSigs (.val anyV)
    [("x", .complN (.val anyV))] (compileSteps (build completionDemoF))

/- negative tests: the two historical bugs must be REJECTED.
   Bug 1 (missing rewrap): the Return-?-of-a-completion-variable shape:
   kUnwrap leaves raw, kRet demands compl. -/
def bug1 : List Instr :=
  [.kEval (Expr.nv "x"), .kTest,
   .kIte [.kRet] [.kUnwrap, .kRet]]
#eval typecheckSeq corpusSigs (.val langV) [("x", .complN (.val anyV))] bug1
/- Bug 2 (double self-test): kEval of a call yields the payload type
   (raw), a stray kTest demands a completion. -/
def bug2 : List Instr :=
  [.kEval (Expr.call "GetV" [Expr.nv "v", Expr.nv "p"]), .kTest,
   .kIte [.kRet] [.kUnwrap, .kPrim1 .pWrapC, .kRet]]
#eval typecheckSeq corpusSigs (.val langV) [("v", .val langV), ("p", .val langV)] bug2
/- Signature-driven argument checking: IteratorClose-style param
   (raw, compl). -/
def closeSigs : SigTable := [("FakeClose", ([.val langV, .complT], .val langV))]
def badArg : List Instr :=
  [.kEval (Expr.call "FakeClose" [Expr.nv "r", Expr.nv "c"]), .kPrim1 .pWrapC, .kRet]
def goodArg : List Instr := badArg
#eval typecheckSeq closeSigs (.val langV) [("r", .val langV), ("c", .val langV)] badArg
#eval typecheckSeq closeSigs (.val langV) [("r", .val langV), ("c", .complT)] goodArg
/- Stricter typing: a number where kIte demands a boolean. This is the
   class of bug runtime smoke tests miss on dead paths. -/
def bug3 : List Instr :=
  [.kEval (.const (JSValue.number 5)), .kIte [] []]
#eval typecheckSeq corpusSigs (.val langV) [] bug3
'''

out = ["import metalanguage", ""]
entries = []
for f in files:
    src = open(f).read()
    src = re.sub(r"^import metalanguage\s*$", "", src, flags=re.M)
    out.append(src)
    entries += re.findall(r"^def (AO_\w+)", src, flags=re.M)

out.append(SMOKE.replace("{entries}", " ++ ".join(entries) if entries else "[]"))
open(os.path.join(root, "corpus.lean"), "w").write("\n".join(out) + "\n")
print(f"corpus.lean: {len(files)} spec files, {len(entries)} registry entries")
for i, f in enumerate(files):
    print(f"  chunk {i+1}: {f}")