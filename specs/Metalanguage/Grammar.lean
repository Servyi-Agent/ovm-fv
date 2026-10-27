/- # Grammar core: ASTs, label elaboration, numbering audit, and
   compilation to Rt2 instruction lists. No surface syntax (that is
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

inductive E2 where
  | nv (name : «String»)
  | nat (n : Nat)
  | const (v : JSValue)
  | isObject (e : E2)
  | isNotObject (e : E2)
  | isNotUndefined (e : E2)
  | hasCall (e : E2)
  | hasCtor (e : E2)
  | isU (e : E2)
  | isBoolVal (b : Bool) (e : E2)
  | isStrVal (s : «String») (e : E2)
  | isNullOrUnd (e : E2)
  | isNull (e : E2)
  | isType (ty : «String») (e : E2)
  | hasField (name : «String») (e : E2)
  | imeth (name : «String») (recv : E2) (args : List E2)
  | ifield (name : «String») (e : E2)
  | varNotPresent (name : «String»)
  | call (name : «String») (args : List E2)
  | listE (es : List E2)
  deriving Repr

inductive P2 where
  | getMethod (o : E2) (sym : «String»)
  | getV (v : E2) (p : E2)
  | call (f : E2) (thisArg : E2) (arg : E2)
  | ordinaryToPrimitive (o : E2) (hint : E2)
  deriving Repr

/- Clean, label-free AST (what the interpreter consumes). -/
inductive Step where
  | ret (v : E2)
  | retQ (op : P2)
  | retE (e : E2)
  | retNewSlot (slotName : «String») (valVar : «String»)
  | assertE (e : E2)
  | forEach (x : «String») (e : E2) (body : List Step)
  | throw
  | setE (name : «String») (e : E2)
  | letQ (name : «String») (op : P2)
  | letE (name : «String») (e : E2)
  | ifS (c : E2) (t : List Step) (e : List Step)
  | elseM (body : List Step)
  deriving Repr

abbrev Prog := List Step


/- Label-carrying parallel AST (what the audit consumes). -/
inductive LBody where
  | ret (v : E2)
  | retQ (op : P2)
  | retE (e : E2)
  | retNewSlot (slotName : «String») (valVar : «String»)
  | assertE (e : E2)
  | forEach (x : «String») (e : E2) (body : List («String» × LBody))
  | throw
  | setE (name : «String») (e : E2)
  | letQ (name : «String») (op : P2)
  | letE (name : «String») (e : E2)
  | ifS (c : E2) (t : List («String» × LBody)) (e : List («String» × LBody))
  | elseM (body : List («String» × LBody))
  deriving Repr

abbrev LStep := String × LBody

/- Flat stream body: ifs and elses carry no branches here;
   `renest` fills them in from the depth markers. -/
inductive FBody where
  | ret (v : E2)
  | retQ (op : P2)
  | retE (e : E2)
  | throw
  | setE (name : «String») (e : E2)
  | ifI (c : E2) (s : FBody)
  | elseI (s : FBody)
  | elseG (c : E2)
  | assertE (e : E2)
  | forEach (x : «String») (e : E2)
  | retNewSlot (slotName : «String») (valVar : «String»)
  | letQ (name : «String») (op : P2)
  | letE (name : «String») (e : E2)
  | ifS (c : E2)
  | elseM
  deriving Repr

abbrev FStep := Nat × String × FBody

/- Fuse an ECMA-262 `N. Else,` step into the immediately preceding if.
   A dangling marker is kept in the output — a stray "else" can never
   silently lose its branch; it stays visible for the audit. -/
/- else-if CHAINS nest: an else-step attaches to the end of the last
   if's else-branch, not by overwriting it. A dangling else (no
   preceding if) stays visible. -/
def attach (e : List LStep) : List LStep → List LStep
  | [] => e                                          -- pending else becomes the branch
  | [(l2, LBody.ifS c2 t2 e2)] =>                    -- chain end: nest here
      [(l2, LBody.ifS c2 t2 (attach e e2))]
  | [p] => [p, ("", LBody.elseM e)]                  -- dangling: stays visible
  | s :: rest => s :: attach e rest

def fuseL : List LStep → List LStep
  | [] => []
  | (l, LBody.ifS c t e') :: (_, LBody.elseM e) :: rest =>
      (l, LBody.ifS c t (attach e e')) :: fuseL rest
  | p :: rest => p :: fuseL rest

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
  | .retQ op => .retQ op
  | .retE e => .retE e
  | .setE n e => .setE n e
  | .letQ n op => .letQ n op
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

inductive Rt2 where
  | kEval (e : E2)
  | kPrim1 (p : Prim)
  | kPrimQ (op : P2)
  | kCall (f : «String») (n : Nat)
  | kSet (x : «String»)
  | kPop
  | kIte (t e : List Rt2)
  | kAssert
  | kRet
  | kTest
  | kUnwrap
  | kIMeth (name : «String») (n : Nat)
  | kMkList (n : Nat)
  | kNewSlot (slotName : «String»)
  | kRepeatWhile (c : E2) (body : List Rt2)
  | kRepeatTest (c : E2) (body : List Rt2)
  | kForStart (x : «String») (body : List Rt2)
  | kForBody (x : «String») (elems : List JSValue) (body : List Rt2)
  deriving Repr


def compileSteps : List Step → List Rt2
  | [] => []
  | .ret v :: rest => .kEval v :: .kPrim1 .pWrapC :: .kRet :: compileSteps rest
  | .retQ op :: rest => .kPrimQ op :: .kRet :: compileSteps rest
  | .retE e :: rest =>
      -- `Return ? e`: if e is a call/imeth its kEval decomposition already
      -- self-tests (propagating abrupt / unwrapping normal), so the value
      -- arrives raw and we just wrap it. Any other shape: test here.
      ((match e with
        | .call _ _ | .imeth _ _ _ =>
            [.kEval e, .kPrim1 .pWrapC, .kRet]
        | _ =>
            [.kEval e, .kTest, .kIte [.kRet] [.kUnwrap, .kPrim1 .pWrapC, .kRet]])
        : List Rt2)
        ++ compileSteps rest
  | .retNewSlot sn vv :: rest =>
      .kEval (.nv vv) :: .kNewSlot sn :: .kPrim1 .pWrapC :: .kRet
        :: compileSteps rest
  | .throw :: rest =>
      .kEval (.const JSValue.undefined) :: .kPrim1 .pThrowC :: .kRet
        :: compileSteps rest
  | .setE n e :: rest => .kEval e :: .kSet n :: compileSteps rest
  | .letQ n op :: rest =>
      .kPrimQ op :: .kTest :: .kIte [.kRet] [.kUnwrap] :: .kSet n :: compileSteps rest
  | .letE n e :: rest => .kEval e :: .kSet n :: compileSteps rest
  | .assertE e :: rest => .kEval e :: .kAssert :: compileSteps rest
  | .forEach x e body :: rest =>
      .kEval e :: .kForStart x (compileSteps body) :: compileSteps rest
  | .ifS c t e :: rest =>
      .kEval c :: .kIte (compileSteps t) (compileSteps e) :: compileSteps rest
  | .elseM _ :: rest => compileSteps rest   -- unreachable post-fuseL

