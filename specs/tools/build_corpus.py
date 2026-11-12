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

/- ===== static typing: signature table (payload types) =====
   Delivery is always a completion; the table types the payload.
   To be extracted from spec.html headers eventually (diff_spec-style). -/
def corpusSigs : SigTable := [
  -- flat-lattice signatures: each slot is a flat disjunction of
  -- atoms; returns are COMPLETION JUDGEMENTS. The corpus bodies are
  -- total: single-normal judgements, no throw alternatives.
  ("IsCallable",          ([langT], [.normal [.anyValue .bool]])),
  ("IsConstructor",       ([langT], [.normal [.anyValue .bool]])),
  ("IsDataDescriptor",    ([[.anyValue .desc]], [.normal [.anyValue .bool]])),
  ("IsAccessorDescriptor",([[.anyValue .desc]], [.normal [.anyValue .bool]])),
  -- the two AOs whose spec bodies genuinely throw (TypeError when
  -- no conversion applies; the otp demo answers compl true):
  -- the coercers provably return non-objects or throw (every return
  -- is guarded by an is-not-an-Object split): the tight return is a
  -- FACT, and it discharges ToString step 11's assert
  ("OrdinaryToPrimitive", ([langT, [.isValue (.str "string"), .isValue (.str "number")]],
      [.normal [.anyValue .undef, .anyValue .null, .anyValue .bool, .anyValue .num, .anyValue .str], .throw])),
  ("ToPrimitive",         ([langT, [.notPresent, .isValue (.str "string"), .isValue (.str "number")]],
      [.normal [.anyValue .undef, .anyValue .null, .anyValue .bool, .anyValue .num, .anyValue .str], .throw])),
  -- ToObject throws TypeError on undefined/null (spec 7.1.13):
  ("ToObject",            ([langT], [.normal [.anyValue .obj], .throw])),
  -- GetV propagates ? ToObject(V); GetMethod propagates ? GetV:
  ("GetV",                ([langT, [.anyValue .str]], [.normal langT, .throw])),
  ("GetMethod",           ([langT, [.anyValue .str]], [.normal langT, .throw])),
  ("OrdinaryGet",         ([[.anyValue .obj], langT, langT], [.normal langT])),
  -- 6/2/6/3: generic descriptor test (fused pPred calls to the other two)
  ("IsGenericDescriptor", ([[.anyValue .desc]], [.normal [.anyValue .bool]])),
  -- 5.2.4.1: completion in, same completion out; the delivered
  -- payload is the record's payload (any value)
  ("Completion",          ([complTy [.normal anyT]], [.normal anyT])),
  -- coercers: honest throws where the spec throws or ? propagates
  ("RequireObjectCoercible", ([langT], [.normal [.anyValue .undef], .throw])),
  ("ToNumeric",           ([langT], [.normal [.anyValue .num], .throw])),
  ("ToString",            ([langT], [.normal [.anyValue .str], .throw])),
  ("ToPropertyKey",       ([langT], [.normal [.anyValue .str], .throw])),
  -- number-tower natives (stubs until the tower lands)
  ("ToNumber",            ([langT], [.normal [.anyValue .num]])),
  ("Number::toString",    ([[.anyValue .num], [.anyValue .num]], [.normal [.anyValue .str]])),
  ("BigInt::toString",    ([[.anyValue .num], [.anyValue .num]], [.normal [.anyValue .str]])),
  ("«Number::toString»",    ([[.anyValue .num], [.anyValue .num]], [.normal [.anyValue .str]])),
  ("«BigInt::toString»",    ([[.anyValue .num], [.anyValue .num]], [.normal [.anyValue .str]])),
  ("IteratorNext",        ([[.anyValue .obj], [.notPresent] ++ langT], [.normal [.anyValue .obj], .throw])),
  ("IteratorComplete",    ([[.anyValue .obj]], [.normal [.anyValue .bool], .throw])),
  ("ToBoolean",           ([langT], [.normal [.anyValue .bool]])),
  -- returns "either an Object or done"; done is the spec's marker,
  -- typed as the true singleton (step 5.b's Return done).
  ("IteratorStep",        ([[.anyValue .obj]], [.normal [.anyValue .obj, .isValue (.boolean Bool.true)], .throw])),
  ("IteratorClose",       ([[.anyValue .obj], complTy [.normal langT, .throw]], [.normal langT, .throw])),
  -- prim-named calls the machine handles natively on registry miss:
  ("Get",                 ([langT, langT], [.normal langT])),
  -- deviation: the spec's « argList » is written bare (list
  -- brackets are Lean identifier delimiters) in IteratorNext but
  -- compiled as a list literal in ToPrimitive — the third Call
  -- parameter accepts either.
  ("Call",                ([langT, langT, langT ++ [.anyValue .list]], [.normal langT]))
]

/- Gate helpers: the #evals are for humans; the examples below make
    every load-bearing claim EXIT-CHECKED - a regression fails the
    build, not the reading. -/
def liftC (t : Ty) : Ty := t.map VTy.complN
/-- language values minus Object: the coercers' honest return
    (every return guarded by an is-not-an-Object split or a throw) -/
def primT : Ty := [.anyValue .undef, .anyValue .null, .anyValue .bool,
  .anyValue .num, .anyValue .str]
/-- the standard ?-dust destiny: any payload, may throw -/
def langCT : Ty := complTy [Pending.normal langT, Pending.throw]

def tcOk (sigs : SigTable) (r : Ty) (Γ : TyEnv) (seq : List Instr) : Bool :=
  match typecheckSeq sigs r Γ seq with
  | .flows f => terminal f && f.assumes.isEmpty
  | _ => Bool.false

def tcReject (sigs : SigTable) (r : Ty) (Γ : TyEnv) (seq : List Instr) : Bool :=
  match typecheckSeq sigs r Γ seq with
  | .reject _ _ => Bool.true
  | _ => Bool.false

/- the issue-#1 regression loop typechecks too: body neutral, cond boolean -/
#eval typecheckSeq corpusSigs (liftC langT) []
    (.kRepeatWhile (Expr.varNotPresent "done") loopBody :: loopRest)
example : tcOk corpusSigs (liftC langT) []
    (.kRepeatWhile (Expr.varNotPresent "done") loopBody :: loopRest) = Bool.true := by native_decide

-- every registry body typechecks against its declared signature
-- (prints the first rejection with reason + stack, or none)
#eval typecheckReg corpusSigs theReg

#eval typecheckSeq corpusSigs (sigRetTy corpusSigs "IteratorClose")
    (zipTy ["iteratorRecord", "completion"]
      [[.anyValue .obj], complTy [.normal langT, .throw]])
    (compileSteps (build iteratorClose7_4_11))
#eval typeOfE corpusSigs
    (zipTy ["iteratorRecord", "completion"]
      [[.anyValue .obj], complTy [.normal langT, .throw]])
    (Expr.completionOf (Expr.call "GetMethod" [Expr.nv "iterator", Expr.const (JSValue.str "return")]))
#eval typeOfE corpusSigs
    (zipTy ["iteratorRecord", "completion"]
      [[.anyValue .obj], complTy [.normal langT, .throw]])
    (Expr.call "GetMethod" [Expr.nv "iterator", Expr.const (JSValue.str "return")])
#eval typecheckRegOk corpusSigs theReg

-- signature well-formedness: every desc atom in the table obeys the
-- disjointness invariant (no data field together with an accessor field)
def sigWf : SigTable → Bool := fun sigs =>
  sigs.all (fun (_, (ps, _)) =>
    ps.all (fun t =>
      t.all (fun atm => match atm with
        | .desc fs => wfFields fs
        | _ => Bool.true)))
#eval sigWf corpusSigs
example : sigWf corpusSigs = Bool.true := by native_decide
-- ToString certified via the boolean puncture (removeAtom: the
-- bool class punctures into the complementary singleton verdict).
example : typecheckRegOk corpusSigs theReg = Bool.true := by
  native_decide

-- per-AO: certificate AND assumption-freedom — a nonzero debt must
-- fail the gate loudly, not just certify-with-debt invisibly.
-- CLOSED (flat lattice): all 10/10 assumption-free. The exact desc
-- field-set atoms (data-complete / accessor-complete) make the
-- descriptor asserts decidable per atom — the old mask lattice could
-- not split data-ness out of the desc constructor bit.
def assumesOf (sigs : SigTable) (name : «String») (ps : List «String»)
    (body : List Instr) : Nat :=
  match typecheckSeq sigs (sigRetTy sigs name) (zipTy ps (sigParams sigs name)) body with
  | .flows f => f.assumes.length
  | _ => 999
#eval assumesOf corpusSigs "IsCallable" ["arg"] (compileSteps (build isCallable7_2_3))
#eval assumesOf corpusSigs "IsConstructor" ["arg"] (compileSteps (build isConstructor7_2_4))
#eval assumesOf corpusSigs "IsDataDescriptor" ["propertyDesc"] (compileSteps (build isDataDescriptor6_2_6_2))
#eval assumesOf corpusSigs "IsAccessorDescriptor" ["propertyDesc"] (compileSteps (build isAccessorDescriptor6_2_6_1))
#eval assumesOf corpusSigs "OrdinaryToPrimitive" ["obj", "hint"] (compileSteps (build ordinaryToPrimitive7_1_1_1))
#eval assumesOf corpusSigs "ToPrimitive" ["input", "preferredType"] (compileSteps (build toPrimitive7_1_1))
#eval assumesOf corpusSigs "ToObject" ["arg"] (compileSteps (build toObject7_1_20))
#eval assumesOf corpusSigs "GetV" ["value", "propertyKey"] (compileSteps (build getV7_3_3))
#eval assumesOf corpusSigs "GetMethod" ["value", "propertyKey"] (compileSteps (build getMethod7_3_10))
#eval assumesOf corpusSigs "OrdinaryGet" ["obj", "propertyKey", "receiver"] (compileSteps (build ordinaryGet10_1_8_1))
#eval assumesOf corpusSigs "IsGenericDescriptor" ["propertyDesc"] (compileSteps (build isGenericDescriptor6_2_6_3))
#eval assumesOf corpusSigs "Completion" ["completionRecord"] (compileSteps (build completion5_2_4_1))
#eval assumesOf corpusSigs "RequireObjectCoercible" ["arg"] (compileSteps (build requireObjectCoercible7_2_1))
#eval assumesOf corpusSigs "ToNumeric" ["arg"] (compileSteps (build toNumeric7_1_3))
#eval assumesOf corpusSigs "ToString" ["arg"] (compileSteps (build toString7_1_19))
#eval assumesOf corpusSigs "ToPropertyKey" ["arg"] (compileSteps (build toPropertyKey7_1_21))
example : assumesOf corpusSigs "IsCallable" ["arg"]
    (compileSteps (build isCallable7_2_3)) = 0 := by native_decide
example : assumesOf corpusSigs "IsConstructor" ["arg"]
    (compileSteps (build isConstructor7_2_4)) = 0 := by native_decide
example : assumesOf corpusSigs "IsDataDescriptor" ["propertyDesc"]
    (compileSteps (build isDataDescriptor6_2_6_2)) = 0 := by native_decide
example : assumesOf corpusSigs "IsAccessorDescriptor" ["propertyDesc"]
    (compileSteps (build isAccessorDescriptor6_2_6_1)) = 0 := by native_decide
example : assumesOf corpusSigs "OrdinaryToPrimitive" ["obj", "hint"]
    (compileSteps (build ordinaryToPrimitive7_1_1_1)) = 0 := by native_decide
example : assumesOf corpusSigs "ToPrimitive" ["input", "preferredType"]
    (compileSteps (build toPrimitive7_1_1)) = 0 := by native_decide
example : assumesOf corpusSigs "ToObject" ["arg"]
    (compileSteps (build toObject7_1_20)) = 0 := by native_decide
example : assumesOf corpusSigs "GetV" ["value", "propertyKey"]
    (compileSteps (build getV7_3_3)) = 0 := by native_decide
example : assumesOf corpusSigs "GetMethod" ["value", "propertyKey"]
    (compileSteps (build getMethod7_3_10)) = 0 := by native_decide
example : assumesOf corpusSigs "OrdinaryGet" ["obj", "propertyKey", "receiver"]
    (compileSteps (build ordinaryGet10_1_8_1)) = 0 := by native_decide
example : assumesOf corpusSigs "IsGenericDescriptor" ["propertyDesc"]
    (compileSteps (build isGenericDescriptor6_2_6_3)) = 0 := by native_decide
-- Completion carries ONE debt today: the step-1 Assert
-- (completionRecord is a Completion Record) is not yet discharged -
-- the assert sees [anyValue bool] (the fused pIsCompletion split
-- pushes undecided verdicts for bare atoms of the complN-wrapped
-- param type). Discharging needs the verdict to be the singleton
-- true; FINDING for review.
example : assumesOf corpusSigs "Completion" ["completionRecord"]
    (compileSteps (build completion5_2_4_1)) = 1 := by native_decide
example : assumesOf corpusSigs "RequireObjectCoercible" ["arg"]
    (compileSteps (build requireObjectCoercible7_2_1)) = 0 := by native_decide
example : assumesOf corpusSigs "ToNumeric" ["arg"]
    (compileSteps (build toNumeric7_1_3)) = 0 := by native_decide
example : assumesOf corpusSigs "ToPropertyKey" ["arg"]
    (compileSteps (build toPropertyKey7_1_21)) = 0 := by native_decide
-- ToString carries ONE recorded debt today: step 11 asserts
-- primitiveValue is not an Object, but our ToPrimitive judgement is
-- langT (objects included) - the tightening to langT-minus-obj is a
-- JUDGEMENT-DESIGN question (their branch tightens; our corpus'
-- OrdinaryToPrimitive returns langT via Call). FINDING for review.
-- ToString REJECTS today: step 7 calls Number::toString(arg, 10),
-- but step 9-11 narrowed arg to Object-only... see the discussion;
-- the sigs keep ToPrimitive returning langT (objects included) so
-- step 11 Assert (primitiveValue is not an Object) cannot discharge.
-- FINDING for review (their branch tightens ToPrimitive to
-- langV-minus-cObj; our corpus keeps langT).
example : assumesOf corpusSigs "ToString" ["arg"]
    (compileSteps (build toString7_1_19)) = 0 := by native_decide
-- the demos typecheck as frames (Γ = params, or empty for top-level)
#eval typecheckSeq corpusSigs (liftC langT) [("input", langT), ("propertyKey", [.anyValue .str])] (compileSteps (build lookupDemoF))
#eval typecheckSeq corpusSigs (liftC langT) [("input", langT), ("propertyKey", [.anyValue .str])] (compileSteps (build getMethodDemoF))
example : tcOk corpusSigs (liftC langT)
    [("input", langT), ("propertyKey", [.anyValue .str])]
    (compileSteps (build lookupDemoF)) = Bool.true := by native_decide
example : tcOk corpusSigs (liftC langT)
    [("input", langT), ("propertyKey", [.anyValue .str])]
    (compileSteps (build getMethodDemoF)) = Bool.true := by native_decide

/- negative tests: the two historical bugs must be REJECTED.
   Bug 1 (missing rewrap): kUnwrap extracts the payload raw; kRet
   demands a parked completion - reject. -/
def bug1 : List Instr :=
  [.kEval (.const (.compl Bool.false (JSValue.number 5))), .kTest,
   .kIte [.kRet] [.kUnwrap, .kRet]]
#eval typecheckSeq corpusSigs (liftC langT) [] bug1
example : tcReject corpusSigs (liftC langT) [] bug1 = Bool.true := by native_decide
/- Bug 2 (double self-test): kEval of a call yields the payload type
   (raw), a stray kTest demands a completion. -/
def bug2 : List Instr :=
  [.kEval (Expr.call "GetV" [Expr.nv "v", Expr.nv "p"]), .kTest,
   .kIte [.kRet] [.kUnwrap, .kPrim1 .pWrapC, .kRet]]
#eval typecheckSeq corpusSigs (liftC langT) [("v", langT), ("p", langT)] bug2
example : tcReject corpusSigs (liftC langT) [("v", langT), ("p", langT)] bug2 = Bool.true := by native_decide
/- Signature-driven argument checking: args must be BELOW the
   callee's parameters (fit the contract), never supersets. -/
def closeSigs : SigTable := [("FakeClose", ([langT, [.anyValue .desc]], [.normal langT]))]
def badArg : List Instr :=
  [.kEval (Expr.call "FakeClose" [Expr.nv "r", Expr.nv "c"]), .kPrim1 .pWrapC, .kRet]
def goodArg : List Instr := badArg
#eval typecheckSeq closeSigs langT [("r", langT), ("c", [.anyValue .num])] badArg
example : tcReject closeSigs langT [("r", langT), ("c", [.anyValue .num])] badArg
    = Bool.true := by native_decide
/- kCall parks BOTH deliveries (normal payload + throw) as separate
   worlds: the self-test idiom must check in each. -/
def callSigs : SigTable := [("FakeCall", ([langT], [.normal langT, .throw]))]
def callBoth : List Instr :=
  [.kEval (.const (JSValue.number 5)), .kCall "FakeCall" 1,
   .kTest, .kIte [.kRet] [.kUnwrap, .kPrim1 .pWrapC, .kRet]]
#eval typecheckSeq callSigs langCT [] callBoth
example : tcOk callSigs langCT [] callBoth = Bool.true := by native_decide
/- Negative control: the throw delivery is REALLY explored - a
   then-branch that falls through (kPop, then end) must fail
   terminality. If parking were normal-only, this would certify. -/
def callThrowBlind : List Instr :=
  [.kEval (.const (JSValue.number 5)), .kCall "FakeCall" 1,
   .kTest, .kIte [.kPop] [.kUnwrap, .kPrim1 .pWrapC, .kRet]]
#eval typecheckSeq callSigs langT [] callThrowBlind
example : tcOk callSigs langT [] callThrowBlind = Bool.false := by native_decide
/- Dual control: a TOTAL callee ([normal t], no throw) parks no
   throw world - the same blind then-branch certifies, proving no
   spurious throw exploration. -/
def neverSigs : SigTable := [("FakeTotal", ([langT], [.normal langT]))]
def callNeverBlind : List Instr :=
  [.kEval (.const (JSValue.number 5)), .kCall "FakeTotal" 1,
   .kTest, .kIte [.kPop] [.kUnwrap, .kPrim1 .pWrapC, .kRet]]
#eval typecheckSeq neverSigs (liftC langT) [] callNeverBlind
example : tcOk neverSigs (liftC langT) [] callNeverBlind = Bool.true := by native_decide
/- Judgement consistency: a body that CAN throw must declare it.
   BadThrow's judgement omits throw - its pThrowC exit must fail
   certification. -/
def badThrowBody : List Instr :=
  [.kEval (.const JSValue.undefined), .kPrim1 .pThrowC, .kRet]
def badThrowSigs : SigTable := [("BadThrow", ([langT], [.normal langT]))]
def goodThrowSigs : SigTable := [("GoodThrow", ([langT], [.normal langT, .throw]))]
#eval typecheckAO badThrowSigs "BadThrow" ["x"] badThrowBody
#eval typecheckAO goodThrowSigs "GoodThrow" ["x"] badThrowBody
example : (typecheckAO goodThrowSigs "GoodThrow" ["x"] badThrowBody).isNone
  = Bool.true := by native_decide
/- Argument-position throws: FakeCall(ThrowingArg()) aborts before
   the callee runs - the frame can throw even though FakeCall itself
   is total. The judgement must say so. -/
def argThrowSigs : SigTable :=
  [("FakeCall", ([langT], [.normal langT])),
   ("FakeThrow", ([], [.normal [.anyValue .bool], .throw]))]
def argThrowGoodSigs : SigTable :=
  [("FakeCall", ([langT], [.normal langT, .throw])),
   ("FakeThrow", ([], [.normal [.anyValue .bool], .throw]))]
def argThrowBody : List Instr :=
  [.kEval (Expr.call "FakeCall" [Expr.call "FakeThrow" []]),
   .kPrim1 .pWrapC, .kRet]
#eval typecheckAO argThrowSigs "FakeCall" ["x"] argThrowBody
#eval typecheckAO argThrowGoodSigs "FakeCall" ["x"] argThrowBody
example : (typecheckAO argThrowSigs "FakeCall" ["x"] argThrowBody).isSome
  = Bool.true := by native_decide
example : (typecheckAO argThrowGoodSigs "FakeCall" ["x"] argThrowBody).isNone
  = Bool.true := by native_decide
#eval typecheckSeq closeSigs langCT [("r", langT), ("c", [.anyValue .desc])] goodArg
example : tcOk closeSigs langCT [("r", langT), ("c", [.anyValue .desc])] goodArg
    = Bool.true := by native_decide
/- Stricter typing: a number where kIte demands a boolean. This is the
   class of bug runtime smoke tests miss on dead paths. -/
def bug3 : List Instr :=
  [.kEval (.const (JSValue.number 5)), .kIte [] []]
#eval typecheckSeq corpusSigs (liftC langT) [] bug3
example : tcReject corpusSigs (liftC langT) [] bug3 = Bool.true := by native_decide

/- ## Reference machine equivalence (exit-checked).
    Reference.lean is re-exported by the root metalanguage module. -/

def theRefReg : RefReg := fun f =>
  match f with
  | .isCallable => some (["arg"], build isCallable7_2_3)
  | .isConstructor => some (["argument"], build isConstructor7_2_4)
  | .isDataDescriptor => some (["Desc"], build isDataDescriptor6_2_6_2)
  | .isAccessorDescriptor => some (["Desc"], build isAccessorDescriptor6_2_6_1)
  | .toPrimitive => some (["input", "preferredType"],
      build toPrimitive7_1_1)
  | .ordinaryToPrimitive => some (["obj", "hint"],
      build ordinaryToPrimitive7_1_1_1)
  | .toObject => some (["value"], build toObject7_1_20)
  | .getV => some (["V", "P"], build getV7_3_3)
  | .getMethod => some (["V", "P"], build getMethod7_3_10)
  | .ordinaryGet => some (["O", "P", "Receiver"],
      build ordinaryGet10_1_8_1)
  | .get | .call => none

/-- Reference vs machine: same terminal outcome on the same program.
    timeout counts as failure (the fuel budget is generous). -/
def refAgree (reg : RefReg) (n : Nat) (p : Prog)
    (m : FM) : Bool :=
  match refRun reg n p [] emptyHeap 0, m with
  | .done v _ _, .fdone (.compl Bool.false v') _ _ _ _ => v == v'
  | .threw v _ _, .fdone (.compl Bool.true v') _ _ _ _ => Bool.true
  | .fell _ _, .fell _ _ _ _ => Bool.true
  | _, _ => Bool.false

def refDemos : Bool :=
  refAgree theRefReg 600 (build exampleF)
    (fsteps theReg 300 (fmOf (build exampleF)))
  && refAgree theRefReg 600 (build callDemoF)
    (fsteps theReg 300 (fmOf (build callDemoF)))
  && refAgree theRefReg 600 (build retDemoF)
    (fsteps theReg 300 (fmOf (build retDemoF)))
  && refAgree theRefReg 600 (build primDemoF)
    (fsteps theReg 300 (fmOf (build primDemoF)))
  && refAgree theRefReg 600 (build forEachDemoF)
    (fsteps theReg 300 (fmOf (build forEachDemoF)))
  && refAgree theRefReg 900 (build otpDemoF)
    (fsteps theReg 300 (fmOf (build otpDemoF)))

#eval refDemos
example : refDemos = Bool.true := by native_decide

/- The complex completion corner: first-class completions certify
    assumption-free, and the machine agrees with the reference. -/
#eval assumesOf corpusSigs "IteratorNext" ["iteratorRecord", "value"]
    (compileSteps (build iteratorNext7_4_6))
#eval assumesOf corpusSigs "IteratorComplete" ["iteratorResult"]
    (compileSteps (build iteratorComplete7_4_7))
#eval assumesOf corpusSigs "IteratorStep" ["iteratorRecord"]
    (compileSteps (build iteratorStep7_4_9))
#eval assumesOf corpusSigs "IteratorClose" ["iteratorRecord", "completion"]
    (compileSteps (build iteratorClose7_4_11))
example : assumesOf corpusSigs "IteratorNext" ["iteratorRecord", "value"]
    (compileSteps (build iteratorNext7_4_6)) = 0 := by native_decide
example : assumesOf corpusSigs "IteratorComplete" ["iteratorResult"]
    (compileSteps (build iteratorComplete7_4_7)) = 0 := by native_decide
example : assumesOf corpusSigs "IteratorStep" ["iteratorRecord"]
    (compileSteps (build iteratorStep7_4_9)) = 0 := by native_decide
example : assumesOf corpusSigs "IteratorClose" ["iteratorRecord", "completion"]
    (compileSteps (build iteratorClose7_4_11)) = 0 := by native_decide
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
