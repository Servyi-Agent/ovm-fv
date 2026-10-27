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
    (.frames [⟨.kRepeatWhile (Expr.varNotPresent "done") loopBody :: loopRest, [], []⟩]
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
        [("input", .obj 0), ("propertyKey", .str "x")], []⟩] demoHeap 1)
#eval fsteps theReg
    1000 (.frames [⟨compileSteps (build getMethodDemoF),
         [("input", .obj 0), ("propertyKey", .str "x")], []⟩] demoHeap 1)

/- ===== static typing: signature table (payload types) =====
   Delivery is always a completion; the table types the payload.
   To be extracted from spec.html headers eventually (diff_spec-style). -/
def corpusSigs : SigTable := [
  -- value-refined signatures (payload types; delivery is always compl)
  ("IsCallable",          ([.any], .boolean)),
  ("IsConstructor",       ([.any], .boolean)),
  ("IsDataDescriptor",    ([.any], .boolean)),
  ("IsAccessorDescriptor",([.any], .boolean)),
  ("OrdinaryToPrimitive", ([.any, .any], .any)),
  ("ToPrimitive",         ([.any, .any], .any)),
  ("ToObject",            ([.any], .obj)),
  ("GetV",                ([.any, .any], .any)),
  ("GetMethod",           ([.any, .any], .any)),
  ("OrdinaryGet",         ([.any, .any, .any], .any)),
  -- prim-named calls the machine handles natively on registry miss:
  ("Get",                 ([.any, .any], .any)),
  ("Call",                ([.any, .any, .any], .any))  -- trailing argsList optional (7.1.1.1 elides it)
]

/- the issue-#1 regression loop typechecks too: body neutral, cond boolean -/
#eval typecheckSeq corpusSigs []
    (.kRepeatWhile (Expr.varNotPresent "done") loopBody :: loopRest)

-- every registry body typechecks against its declared signature
-- (prints the first rejection with reason + stack, or none)
#eval typecheckReg corpusSigs theReg
#eval typecheckRegOk corpusSigs theReg
-- the demos typecheck as frames (Γ = params, or empty for top-level)
#eval typecheckSeq corpusSigs [("input", .any), ("propertyKey", .any)] (compileSteps (build lookupDemoF))
#eval typecheckSeq corpusSigs [("input", .any), ("propertyKey", .any)] (compileSteps (build getMethodDemoF))

/- negative tests: the two historical bugs must be REJECTED.
   Bug 1 (missing rewrap): the Return-?-of-a-completion-variable shape:
   kUnwrap leaves raw, kRet demands compl. -/
def bug1 : List Instr :=
  [.kEval (Expr.nv "x"), .kTest,
   .kIte [.kRet] [.kUnwrap, .kRet]]
#eval typecheckSeq corpusSigs [("x", .compl)] bug1
/- Bug 2 (double self-test): kEval of a call yields the payload type
   (raw), a stray kTest demands a completion. -/
def bug2 : List Instr :=
  [.kEval (Expr.call "GetV" [Expr.nv "v", Expr.nv "p"]), .kTest,
   .kIte [.kRet] [.kUnwrap, .kPrim1 .pWrapC, .kRet]]
#eval typecheckSeq corpusSigs [("v", .any), ("p", .any)] bug2
/- Signature-driven argument checking: IteratorClose-style param
   (raw, compl). -/
def closeSigs : SigTable := [("FakeClose", ([.any, .compl], .any))]
def badArg : List Instr :=
  [.kEval (Expr.call "FakeClose" [Expr.nv "r", Expr.nv "c"]), .kPrim1 .pWrapC, .kRet]
def goodArg : List Instr := badArg
#eval typecheckSeq closeSigs [("r", .any), ("c", .any)] badArg
#eval typecheckSeq closeSigs [("r", .any), ("c", .compl)] goodArg
/- Stricter typing: a number where kIte demands a boolean. This is the
   class of bug runtime smoke tests miss on dead paths. -/
def bug3 : List Instr :=
  [.kEval (.const (JSValue.number 5)), .kIte [] []]
#eval typecheckSeq corpusSigs [] bug3
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
