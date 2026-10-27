/- # Grammar core: ASTs, label elaboration, numbering audit, and
   compilation to Instr instruction lists. No surface syntax (that is
   Syntax.lean), no evaluation. -/

/- # ovm-fv metalanguage

   The ECMA-262 emu-alg metalanguage: surface grammar (`┊` depth
   markers, spec numbering), label-carrying elaboration, audits
   (numbering consecutiveness), SOS and kEval small-step semantics
   (frames for control boundaries), and the operation-registry
   protocol. Spec transcriptions live under spec/<clause>/spec.lean
   and are assembled into a registry by tools/build_corpus.py. -/

/- Numbered-step grammar with exact ECMA-262 tokens AND explicit
depth markers ┊ (one per level below the top):

  1: …          depth 1 (no marker)
  ┊a: …        depth 2
  ┊┊i: …       depth 3
  ┊┊┊1: …      depth 4 (numbers restart — no collision)
  ┊┊┊┊a: …     depth 5

A block at depth n is a maximal run of steps carrying exactly n-1
markers; it ends when a step with fewer markers appears. Since the
restarted depth-4 numbers are `┊┊┊1:` vs top-level `1:` —
different tokens — the greedy swallow of the marker-free design is
structurally impossible. Numbering becomes decoration: identifiers
serve as roman labels (no keyword shadowing), and the consecutiveness
audit remains purely as a typo check. -/

/- ===== Objects ===== -/

/- Property Descriptor — verbatim six optional fields (ES 6.2.6.1). -/
mutual
inductive Descriptor where
  | mk (value : Option JSValue) (writable : Option Bool)
      (getter : Option Nat) (setter : Option Nat)
      (enumerable : Option Bool) (configurable : Option Bool)
  deriving Repr, BEq
inductive JSValue where
  | undefined | null | boolean (b : Bool) | number (n : Float)
  | str (s : «String»)
  | listV (l : List JSValue)     -- spec List, injected for the AO layer
  | compl (abrupt : Bool) (v : JSValue)  -- Completion Record, as a value
  | obj (loc : Nat)                     -- object reference
  | descV (d : Descriptor)              -- Property Descriptor, as a value
  deriving Repr, BEq
end

inductive Expr where
  | nv (name : «String»)
  | nat (n : Nat)
  | const (v : JSValue)
  | isObject (e : Expr)
  | isNotObject (e : Expr)
  | isNotUndefined (e : Expr)
  | hasCall (e : Expr)
  | hasCtor (e : Expr)
  | isU (e : Expr)
  | isBoolVal (b : Bool) (e : Expr)
  | isStrVal (s : «String») (e : Expr)
  | isNullOrUnd (e : Expr)
  | isNull (e : Expr)
  | isType (ty : «String») (e : Expr)
  | hasField (name : «String») (e : Expr)
  | imeth (name : «String») (recv : Expr) (args : List Expr)
  | ifield (name : «String») (e : Expr)
  | varNotPresent (name : «String»)
  | call (name : «String») (args : List Expr)
  | listE (es : List Expr)
  deriving Repr

/- Clean, label-free AST (what the interpreter consumes). -/
inductive Step where
  | ret (v : Expr)
  | retE (e : Expr)
  | retNewSlot (slotName : «String») (valVar : «String»)
  | assertE (e : Expr)
  | forEach (x : «String») (e : Expr) (body : List Step)
  | throw
  | setE (name : «String») (e : Expr)
  | letE (name : «String») (e : Expr)
  | ifS (c : Expr) (t : List Step) (e : List Step)
  | elseM (body : List Step)
  deriving Repr

abbrev Prog := List Step


/- Label-carrying parallel AST (what the audit consumes). -/
inductive LBody where
  | ret (v : Expr)
  | retE (e : Expr)
  | retNewSlot (slotName : «String») (valVar : «String»)
  | assertE (e : Expr)
  | forEach (x : «String») (e : Expr) (body : List («String» × LBody))
  | throw
  | setE (name : «String») (e : Expr)
  | letE (name : «String») (e : Expr)
  | ifS (c : Expr) (t : List («String» × LBody)) (e : List («String» × LBody))
  | elseM (body : List («String» × LBody))
  deriving Repr

abbrev LStep := String × LBody

/- Flat stream body: ifs and elses carry no branches here;
   `renest` fills them in from the depth markers. -/
inductive FBody where
  | ret (v : Expr)
  | retE (e : Expr)
  | throw
  | setE (name : «String») (e : Expr)
  | ifI (c : Expr) (s : FBody)
  | elseI (s : FBody)
  | elseG (c : Expr)
  | assertE (e : Expr)
  | forEach (x : «String») (e : Expr)
  | retNewSlot (slotName : «String») (valVar : «String»)
  | letE (name : «String») (e : Expr)
  | ifS (c : Expr)
  | elseM
  deriving Repr

abbrev FStep := Nat × String × FBody

/- Fuse an ECMA-262 `N. Else,` step into the immediately preceding if.
   A dangling marker is kept in the output — a stray "else" can never
   silently lose its branch; it stays visible for the audit. -/
/- else-if CHAINS nest: an else-step attaches to the end of the last
   if's else-branch, not by overwriting it. A dangling else (no
   preceding if) stays visible. -/
/- Attach a pending else-block at the INNERMOST if whose else is
   still open — else-if chains nest: `If c1 … / Else if c2 … / Else …`
   makes the second block the else of c2's if, not c1's. -/
def setDeepestElse (b : List LStep) : List LStep → List LStep
  | [] => b
  | (l, LBody.ifS c t []) :: rest => (l, LBody.ifS c t b) :: rest
  | (l, LBody.ifS c t e') :: rest => (l, LBody.ifS c t (setDeepestElse b e')) :: rest
  | p => p ++ b

/-- Attaching an elseM block removes exactly one elseM step; the
   lexicographic measure (elseM-count, total size) decreases. -/
def countElse : List LStep → Nat
  | [] => 0
  | (_, LBody.elseM _) :: r => 1 + countElse r
  | _ :: r => countElse r

theorem countElse_cons (n : «String») (b : LBody) (r : List LStep) :
    countElse r ≤ countElse ((n, b) :: r) := by
  cases b <;> simp [countElse]

def fuseL : List LStep → List LStep
  | [] => []
  | (l, LBody.ifS c t e') :: (_, LBody.elseM e) :: rest =>
      fuseL ((l, LBody.ifS c t (setDeepestElse e e')) :: rest)
  | p :: rest => p :: fuseL rest
termination_by l => countElse l + l.length
decreasing_by
  · simp [countElse] <;> omega
  · obtain ⟨n, b⟩ := p
    have hmono := countElse_cons n b rest
    simp only [List.length_cons]
    omega

mutual
def strip : List LStep → Prog
  | [] => []
  | (_l, b) :: rest => stripBody b :: strip rest
def stripBody : LBody → Step
  | .ret v => .ret v
  | .retNewSlot sn vv => .retNewSlot sn vv
  | .throw => .throw
  | .assertE e => .assertE e
  | .forEach x e b => .forEach x e (strip b)
  | .retE e => .retE e
  | .setE n e => .setE n e
  | .letE n e => .letE n e
  | .ifS c t e => .ifS c (strip t) (strip e)
  | .elseM b => .elseM (strip b)
end

/- Fuse else-steps, then strip labels. -/

/- Consecutiveness audit: label ordinals per scheme (1→1, a→1, i→1). -/
def romanOrd : «String» → Option Nat
  | "i" => some 1 | "ii" => some 2 | "iii" => some 3
  | "iv" => some 4 | "v" => some 5 | "vi" => some 6
  | _ => none

def labelOrd (s : «String») : Option Nat :=
  match s.toNat? with
  | some n => some n
  | none =>
    match romanOrd s with
    | some n => some n
    | none =>
      if s.length == 1
          && s.front.toNat ≥ 'a'.toNat && s.front.toNat ≤ 'z'.toNat then
        some (s.front.toNat - 'a'.toNat + 1)
      else none

mutual
/- check l i: the labels of l are i, i+1, i+2, … and every nested
   block (checked recursively) also starts at 1. -/
def check : List LStep → Nat → Bool
  | [], _ => true
  | p :: rest, i =>
      match labelOrd p.1 with
      | some n => n == i && checkBody p.2 && check rest (i + 1)
      | none => false
def checkBody : LBody → Bool
  | .ifS _ t e => check t 1 && check e 1
  | .forEach _ _ b => check b 1
  | .elseM b => check b 1
  | _ => true
end

def checkRun (l : List LStep) : Bool := check l 1


inductive Prim where              -- bedrock predicates (the axiom stratum)
  | pIsObj | pIsNotObj | pIsNotU | pHasCall
  | pHasCtor | pIsU | pIsTrue | pIsFalse
  | pNullOrUnd
  | pWrapC
  | pThrowC
  | pIsNull
  | pIsType (s : «String»)
  | pHasField (s : «String»)
  | pDescField (s : «String»)
  | pIsStr (s : «String»)
  deriving Repr





/- Control boundaries as frames: the callee REPLACES the current list
   (caller continuation saved in the frame — cannot be spliced wrong),
   and return POPS one frame (no scanning, cannot discard past a
   boundary). break/continue/try later = more Frame kinds. -/




/-- Calls the machine answers natively when the registry misses. -/
def nativeOps : List «String» :=
  ["GetV", "Get", "Call", "GetMethod", "OrdinaryToPrimitive"]

/- Internal-slot universe: closed by construction (ES declares the set). -/
inductive Slot where
  | call | construct | strData | dateValue
  | boolData | numData | symData | bigData
  deriving Repr, BEq

def slotOrd : Slot → Nat
  | .call => 0 | .construct => 1 | .strData => 2 | .dateValue => 3
  | .boolData => 4 | .numData => 5 | .symData => 6 | .bigData => 7

def slotOfName : «String» → Option Nat
  | "Call" => some (slotOrd .call)
  | "Construct" => some (slotOrd .construct)
  | "StringData" => some (slotOrd .strData)
  | "DateValue" => some (slotOrd .dateValue)
  | "BooleanData" => some (slotOrd .boolData)
  | "NumberData" => some (slotOrd .numData)
  | "SymbolData" => some (slotOrd .symData)
  | "BigIntData" => some (slotOrd .bigData)
  | _ => none

/- The transcribed-operation registry (the corpus). -/
abbrev AOReg := List («String» × (List «String» × Prog))


def findAO : AOReg → «String» → Option (List «String» × Prog)
  | [], _ => none
  | (n, e) :: r, n' => if n == n' then some e else findAO r n'




/- ===== SOS semantics: state = (remaining program, env).
   The if-rule splices the branch:  ifS c t e :: rest → (t ++ rest | e ++ rest).
   One SOS step = one whole statement (conditions/expressions evaluate atomically).
   Reference semantics closest to the spec prose; agreement with the machine
   above is the next theorem. ===== -/


/- ===== Frame machine: eval stack + frames + in-list loop markers.
   LoopFrame IS the statement list; the final marker is the redo
   instruction (user's design). Expressions decompose at runtime:

     kEval (call f [a1..an]) :: rt  =>  kEval a1 :: … :: kEval an :: kCall f n :: rt
     kEval (isObject e)      :: rt  =>  kEval e :: kPrim1 pIsObj :: rt

   Consumers pop the eval stack (top of stack = LAST pushed operand):
     kCall f n : pop n -> new frame (env = params.zip popped.reverse)
     kRet      : top of eval -> caller's eval, pop frame (stuck if empty)
     kThrow    : pop one frame per step, kThrow at the caller's head
     kSet/kDrop/kBranch/kAssert: pop 1
   Invariant (lemma, not type): eval stack empty at statement boundaries. -/

inductive Instr where
  | kEval (e : Expr)
  | kPrim1 (p : Prim)
  | kCall (f : «String») (n : Nat)
  | kSet (x : «String»)
  | kPop
  | kIte (t e : List Instr)
  | kAssert
  | kAssertObj (x : «String»)   -- Assert: x is an Object - refining
  | kNarrowNotNull (x : «String») -- else-path of If x is null, <exit>
  | kRet
  | kTest
  | kUnwrap
  | kIMeth (name : «String») (n : Nat)
  | kMkList (n : Nat)
  | kNewSlot (slotName : «String»)
  | kRepeatWhile (c : Expr) (body : List Instr)
  | kRepeatTest (c : Expr) (body : List Instr)
  | kForStart (x : «String») (body : List Instr)
  | kForBody (x : «String») (elems : List JSValue) (body : List Instr)
  deriving Repr


def compileSteps : List Step → List Instr
  | [] => []
  | .ret v :: rest => .kEval v :: .kPrim1 .pWrapC :: .kRet :: compileSteps rest
  | .retE e :: rest =>
      -- `Return ? e`: if e is a call/imeth its kEval decomposition already
      -- self-tests (propagating abrupt / unwrapping normal), so the value
      -- arrives raw and we just wrap it. Any other shape: test here.
      ((match e with
        | .call _ _ | .imeth _ _ _ =>
            [.kEval e, .kPrim1 .pWrapC, .kRet]
        | _ =>
            [.kEval e, .kTest, .kIte [.kRet] [.kUnwrap, .kPrim1 .pWrapC, .kRet]])
        : List Instr)
        ++ compileSteps rest
  | .retNewSlot sn vv :: rest =>
      .kEval (.nv vv) :: .kNewSlot sn :: .kPrim1 .pWrapC :: .kRet
        :: compileSteps rest
  | .throw :: rest =>
      .kEval (.const JSValue.undefined) :: .kPrim1 .pThrowC :: .kRet
        :: compileSteps rest
  | .setE n e :: rest => .kEval e :: .kSet n :: compileSteps rest
  | .letE n e :: rest => .kEval e :: .kSet n :: compileSteps rest
  | .assertE (.isObject (.nv x)) :: rest =>
      -- a refining assert: after it, x : obj (justifies e.g. ToObject's
      -- final `Return argument.` under a declared obj return)
      .kEval (.isObject (.nv x)) :: .kAssertObj x :: compileSteps rest
  | .assertE e :: rest => .kEval e :: .kAssert :: compileSteps rest
  | .forEach x e body :: rest =>
      .kEval e :: .kForStart x (compileSteps body) :: compileSteps rest
  | .ifS (.isNull (.nv x)) t [] :: rest =>
      -- `If x is null, <then>` with no else: the fall-through path
      -- knows x is not null — inject the narrowing
      .kEval (.isNull (.nv x))
        :: .kIte (compileSteps t) [.kNarrowNotNull x] :: compileSteps rest
  | .ifS c t e :: rest =>
      .kEval c :: .kIte (compileSteps t) (compileSteps e) :: compileSteps rest
  | .elseM _ :: rest => compileSteps rest   -- unreachable post-fuseL

