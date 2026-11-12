import Metalanguage.Grammar

/-- Append only grows the structural size. -/
theorem sizeOf_append_le {α : Type} [SizeOf α] :
    ∀ (t rest : List α), sizeOf (t ++ rest) ≤ sizeOf t + sizeOf rest := by
  intro t rest
  induction t with
  | nil => simp [List.nil_append]
  | cons a t ih =>
      show 1 + sizeOf a + sizeOf (t ++ rest) ≤ 1 + sizeOf a + sizeOf t + sizeOf rest
      omega

/- # Static typechecking: the flat lattice + pending completions.

    Types are SETS over a closed constructor universe, always in FLAT
    form: Ty = List VTy, a disjunction of atoms with no nesting. A
    test `x is a T` SPLITS the world (then: x ∩ T, verdict singleton
    true; else: x − T, verdict singleton false). Completions are NOT
    types: a world parks at most one completion (pending), pushed by
    bare kCall/kIMeth and completion literals, peeked by kTest,
    extracted by kUnwrap, re-parked by pWrapC/pThrowC, exempt at
    kRet. Descriptor well-formedness is part of the tag's meaning:
    anyValue desc = any well-formed descriptor; desc fs = exactly
    these fields. -/

/- ## Constructor tags (the coarse universe) -/

inductive Ctor where
  | undef | null | bool | num | str | obj | list | desc
  deriving Repr, DecidableEq, BEq

def langTags : List Ctor := [.undef, .null, .bool, .num, .str, .obj]
def anyTags : List Ctor := langTags ++ [.list, .desc]

/- ## Descriptor fields -/

inductive Field where
  | value | writable | getter | setter | enumerable | configurable
  deriving Repr, DecidableEq, BEq

def fData : List Field := [.value, .writable]
def fAcc : List Field := [.getter, .setter]

/-- Well-formed field-set: never both a data field and an accessor
    field — the spec's descriptor-disjointness invariant. -/
def wfFields (fs : List Field) : Bool :=
  !(fs.any (fun fld => fData.contains fld) && fs.any (fun fld => fAcc.contains fld))

def fieldsOf : Descriptor → List Field
  | .mk value writ get set enum conf =>
      (if value.isSome then [Field.value] else [])
      ++ (if writ.isSome then [Field.writable] else [])
      ++ (if get.isSome then [Field.getter] else [])
      ++ (if set.isSome then [Field.setter] else [])
      ++ (if enum.isSome then [Field.enumerable] else [])
      ++ (if conf.isSome then [Field.configurable] else [])

/- ## Atoms: the flat value layer -/

/- THE FLAT UNIVERSE: ONE eval stack, ONE lattice. A completion is
    an ordinary value whose atom says so — no pending field, no
    splitStack: the slot's type gives its position and kind. The
    four constructors below are the BARE forms (plain values); the
    two above them are the COMPLETION forms. `isBareVTy` is the
    two-arm classification. -/
inductive VTy where
  | complN (p : VTy)             -- normal completion, payload of type p
  | complT                       -- throw completion
  | anyValue (c : Ctor)          -- any bare value of this class
  | isValue (v : JSValue)        -- exactly this bare value (singleton)
  | desc (fs : List Field)      -- bare descriptor with exactly this field-set
  | notPresent                   -- the bare binding is absent (optional arg)
  deriving Repr, BEq

/-- The classification: bare value vs completion. -/
def isBareVTy : VTy → Bool
  | .complN _ | .complT => Bool.false
  | _ => Bool.true

/-- A flat type: a finite disjunction of atoms. -/
abbrev Ty := List VTy

/-- A parked completion: normal payload (a flat type) or a throw. -/
inductive Pending where
  | normal (t : Ty)
  | throw
  deriving Repr

def tagOf : JSValue → Ctor
  | .undefined => .undef | .null => .null
  | .boolean _ => .bool | .number _ => .num | .str _ => .str
  | .obj _ => .obj | .listV _ => .list | .descV _ => .desc
  | .compl _ _ => .undef        -- completions are never stack atoms

/-- Canonical abstraction of a stack value — completions included:
    they are ordinary values, abstracted where they sit. -/
def typeOfV : JSValue → VTy
  | .descV d => .desc (fieldsOf d)
  | .compl Bool.false v => .complN (typeOfV v)
  | .compl Bool.true _ => .complT
  | v => .isValue v

def anyOf (cs : List Ctor) : Ty := cs.map VTy.anyValue
def langT : Ty := anyOf langTags
def anyT : Ty := anyOf anyTags

/- ## Subtyping: a finite grid on atoms; forall-exists on flat types -/

def tmovesV : VTy → VTy → Bool
  | .complN p, .complN q => tmovesV p q
  | .complT, .complT => Bool.true
  | .anyValue c, .anyValue c' => decide (c = c')
  | .isValue v, .isValue w => v == w
  | .isValue v, .anyValue c => decide (tagOf v = c)
  | .desc fs, .desc fs' => decide (fs = fs')
  | .desc _, .anyValue .desc => Bool.true
  | .notPresent, .notPresent => Bool.true
  | _, _ => Bool.false

def tmoves (t u : Ty) : Bool :=
  t.all (fun a => u.any (fun b => tmovesV a b))

def leTy : List Ty → List Ty → Bool
  | [], [] => Bool.true
  | t :: ts, t' :: ts' => tmoves t t' && leTy ts ts'
  | _, _ => Bool.false

/- ## Meets and differences on the flat lattice -/

/-- Atom meet; none = empty. -/
def meetAtom : VTy → VTy → Option VTy
  | .anyValue c, .anyValue c' => if c = c' then some (.anyValue c) else none
  | .isValue v, .isValue w => if v == w then some (.isValue v) else none
  | .desc fs, .desc fs' => if fs = fs' then some (.desc fs) else none
  | .desc fs, .anyValue .desc => some (.desc fs)
  | .anyValue .desc, .desc fs => some (.desc fs)
  | .isValue v, .anyValue c => if tagOf v = c then some (.isValue v) else none
  | .anyValue c, .isValue v => if tagOf v = c then some (.isValue v) else none
  | .notPresent, .notPresent => some .notPresent
  | _, _ => none

def meetTy (S T : Ty) : Ty :=
  S.flatMap (fun a => T.flatMap (fun b =>
    match meetAtom a b with
    | some m => [m]
    | none => []))

/-- Difference. On this lattice a − b is empty exactly when a ⊑ b
    (classes cannot be punctured by singletons), so removal is
    filtration by ¬(a ⊑ b). -/
def removeTy (S T : Ty) : Ty :=
  S.filter (fun a => !T.any (fun b => tmovesV a b))

/- ## Signature tables

    A signature's return is a COMPLETION JUDGEMENT: the list of
    deliveries the function may produce - e.g. [normal t1, throw] or
    just [normal t1] (total). Parking splits over exactly these
    alternatives (one world each); a throw world exists only if the
    judgement says so. Judgement soundness is enforced per body:
    a certified body whose judgement omits throw must never exit
    via a throw (Flows.throws). -/

abbrev SigTable := List («String» × (List Ty × List Pending))

def complCanThrow (cs : List Pending) : Bool :=
  cs.any (fun c => match c with | .throw => Bool.true | _ => Bool.false)

/-- The payload union of a completion judgement (bare). -/
def complPayload (cs : List Pending) : Ty :=
  (cs.filterMap (fun c => match c with
    | .normal t => some t | .throw => none)).flatten

/-- A completion judgement as ONE stack-slot type: the normal
    payload alternatives as complN atoms, plus complT iff declared.
    This is what a call pushes and what a frame returns. -/
def complTy (cs : List Pending) : Ty :=
  (cs.filterMap (fun c => match c with
    | .normal t => some (t.map VTy.complN) | .throw => none)).flatten
  ++ (if complCanThrow cs then [VTy.complT] else [])

def sigFind : SigTable → «String» → Option (List Ty × List Pending)
  | [], _ => none
  | (n, s) :: rest, f => if n == f then some s else sigFind rest f

def sigParams (sigs : SigTable) (name : «String») : List Ty :=
  match sigFind sigs name with
  | some (ps, _) => ps
  | none => []

/-- The callee's completion judgement (unknown callee: worst case). -/
def sigCompls (sigs : SigTable) (name : «String») : List Pending :=
  match sigFind sigs name with
  | some (_, cs) => cs
  | none => [.throw]

def sigRetTy (sigs : SigTable) (name : «String») : Ty :=
  complTy (sigCompls sigs name)

abbrev TyEnv := List («String» × Ty)

def zipTy : List «String» → List Ty → TyEnv
  | [], [] => []
  | x :: xs, t :: ts => (x, t) :: zipTy xs ts
  | _, _ => []

def tyLookup : TyEnv → «String» → Option Ty
  | [], _ => none
  | (n, t) :: r, x => if n == x then some t else tyLookup r x

def mopArity : «String» → Option Nat
  | "Get" => some 2
  | "GetOwnProperty" => some 1
  | "GetPrototypeOf" => some 0
  | _ => none

def mopResult : «String» → List Pending
  | "Get" => [.normal langT]
  -- Iterator Record fields: [[Iterator]] is an Object (spec 7.4.1);
  -- the others are dynamic guards.
  | "Iterator" => [.normal [.anyValue .obj]]
  | "NextMethod" | "Done" => [.normal langT]
  | "GetPrototypeOf" => [.normal [.anyValue .null, .anyValue .obj]]
  | "Value" | "Getter" | "Setter" => [.normal langT]
  | "Writable" | "Enumerable" | "Configurable" => [.normal [.anyValue .bool]]
  | "GetOwnProperty" =>
      -- stored descriptors are completed at write time: data-complete
      -- or accessor-complete (the spec's disjointness invariant)
      [.normal [.desc [.value, .writable, .enumerable, .configurable]],
       .normal [.desc [.getter, .setter, .enumerable, .configurable]],
       .normal [.anyValue .undef]]
  | _ => [.normal anyT, .throw]

def mopPayload («nm» : «String») : Ty := complPayload (mopResult nm)

/- ## Worlds -/

structure World where
  Γ : TyEnv
  σ : List Ty
  deriving Repr

abbrev Worlds := List World

/- ## Expression typing (no side conditions; the is-family refines
    only via the kEval split below) -/

mutual
def typesOf (sigs : SigTable) (Γ : TyEnv) : List Expr → Option (List Ty)
  | [] => some []
  | x :: xs =>
      match typeOfE sigs Γ x, typesOf sigs Γ xs with
      | some t, some ts => some (t :: ts)
      | _, _ => none
termination_by es => sizeOf es

/-- The payloads of the complN atoms, as one flat type. -/
def payloadsOf (t : Ty) : Ty :=
  t.flatMap (fun a => match a with | .complN p => [p] | _ => [])

/-- The completion-kind decider for the splitP1 stratum. -/
def primDecide : Prim → Option (VTy → Option Bool)
  | .pIsNormalC =>
      some (fun t => match t with
        | .complN _ => some Bool.true
        | .complT => some Bool.false
        | _ => none)
  | .pIsThrowC =>
      some (fun t => match t with
        | .complN _ => some Bool.false
        | .complT => some Bool.true
        | _ => none)
  | .pIsCompletion =>
      some (fun t => match t with
        | .complN _ | .complT => some Bool.true
        | _ => none)
  | _ => none

/-- complN-only slot -> payload atoms (none if mixed/bare). -/
def payloadOf : Ty → Option Ty
  | [] => none
  | [.complN p] => some [p]
  | .complN p :: rest =>
      match payloadOf rest with
      | some ps => some (p :: ps)
      | none => none
  | _ => none

/-- bare-only slot -> atoms (none if any completion atom). -/
def bareOf : Ty → Option Ty
  | [] => some []
  | a :: rest =>
      match isBareVTy a with
      | Bool.true => (bareOf rest).map (fun ps => a :: ps)
      | Bool.false => none

def typeOfE (sigs : SigTable) (Γ : TyEnv) : Expr → Option Ty
  | .nv x => tyLookup Γ x
  | .nat n => some [.isValue (.number ↑n)]
  | .const v => some [typeOfV v]
  | .varNotPresent _ => some [.anyValue .bool]
  | .isNormalC _ | .isThrowC _ | .isCompletion _ => some [.anyValue .bool]
  | .complValue e =>
      match typeOfE sigs Γ e with
      | some t => payloadOf t
      | none => none
  | .completionOf e =>
      match typeOfE sigs Γ e with
      | some t => bareOf t |>.map (fun bt => bt.map VTy.complN)
      | none => none
  | .call f as =>
      match sigFind sigs f with
      | some (ps, retj) =>
          match typesOf sigs Γ as with
          | some ts =>
              if leTy ts ps
                 || (as.length == ps.length - 1
                     && leTy ts (ps.dropLast))
              then some (complPayload retj) else none
          | none => none
      | none => none
  | .imeth nm recv args =>
      match mopArity nm with
      | some k =>
          if args.length == k
             && (match typeOfE sigs Γ recv with
                 | some t => tmoves t [.anyValue .obj]
                 | none => Bool.false)
             && (typesOf sigs Γ args).isSome
          then some (mopPayload nm) else none
      | none => none
  | .ifield nm x =>
      -- `.[[Value]]` is POLYMORPHIC by receiver: on a normal
      -- completion it is the payload read (IteratorClose's
      -- innerResult.[[Value]]); otherwise the zero-arg-MOP
      -- deviation / dynamic guard as before.
      if nm == "Value" then
        match typeOfE sigs Γ x with
        | some t =>
            match payloadOf t with
            | some ps => some ps
            -- a mixed slot: the read, when normal, is SOME declared
            -- payload (union of the complN atoms' payloads); the
            -- bare part reads as the field MOP. A refined
            -- pure-complN slot then refines this union.
            | none =>
                some (payloadsOf t ++ mopPayload nm)
        | none => none
      else
        if (typeOfE sigs Γ x).isSome then some (mopPayload nm) else none
  | .listE es =>
      if (typesOf sigs Γ es).isSome then some [.anyValue .list] else none
  | .isObject x =>
      -- refinement: an obj-only receiver makes the test decidable
      -- (IteratorClose's step-1 assert discharges)
      match typeOfE sigs Γ x with
      | some t =>
          if tmoves t [.anyValue .obj] then some [.isValue (.boolean Bool.true)]
          else if (removeTy t [.anyValue .obj]).isEmpty && !t.isEmpty then
            some [.isValue (.boolean Bool.false)]
          else some [.anyValue .bool]
      | none => none
  | .isNotObject x | .isNotUndefined x | .hasCall x
  | .hasCtor x | .isU x | .isBoolVal _ x | .isStrVal _ x
  | .isNullOrUnd x | .isNull x | .isType _ x | .hasField _ x =>
      if (typeOfE sigs Γ x).isSome then some [.anyValue .bool] else none
termination_by e => sizeOf e
end

/- ## Flows and results -/

structure Flows where
  exits : Bool
  /- Some world exited via kRet with a THROWN pending: the checked
     body can produce an abrupt answer. Judgement soundness: if the
     signature's completion judgement omits throw, this must be
     false (typecheckAO enforces it). -/
  throws : Bool
  falls : Worlds
  /- Assert obligations that could not be discharged by the splits:
     each recorded assumption is a proof debt (caller contracts, spec
     editor claims); the certificate is RELATIVE to them. Discharged
     asserts (impossible false-worlds) leave no trace. -/
  assumes : List «String»
  deriving Repr

/-- Frame-level demand: every world exits (returns), none falls. -/
def terminal (f : Flows) : Bool :=
  f.exits && f.falls.isEmpty

inductive TCResult where
  | flows (f : Flows)
  | reject (site : Instr) (why : «String»)
  deriving Repr

/- Can evaluating this expression exit the frame abruptly? True
    exactly when it contains a call/imeth whose completion judgement
    lists throw. -/
mutual
def exprCanThrow (sigs : SigTable) : Expr → Bool
  -- arguments are ?-wrapped: a throwing ARG aborts the caller
  -- before the callee is entered (ES never delivers throws as args)
  | .call f as => complCanThrow (sigCompls sigs f) || exprsCanThrow sigs as
  | .imeth nm recv args =>
      complCanThrow (mopResult nm) || exprCanThrow sigs recv
        || exprsCanThrow sigs args
  | .isObject e | .isNotObject e | .isNotUndefined e | .hasCall e
  | .hasCtor e | .isU e | .isBoolVal _ e | .isStrVal _ e
  | .isNullOrUnd e | .isNull e | .isType _ e | .hasField _ e
  | .isNormalC e | .isThrowC e | .isCompletion e | .complValue e
  | .completionOf e =>
      exprCanThrow sigs e
  | .listE es => exprsCanThrow sigs es
  | _ => Bool.false
termination_by e => sizeOf e

def exprsCanThrow (sigs : SigTable) : List Expr → Bool
  | [] => Bool.false
  | e :: es => exprCanThrow sigs e || exprsCanThrow sigs es
termination_by es => sizeOf es
end

/-- The kEval summary of a call skips the self-test dust; record the
    abrupt exit the dust would take (for judgement consistency). -/
def markThrow (sigs : SigTable) (ex : Expr) : TCResult → TCResult :=
  fun res => match res with
  | .flows fr =>
      .flows { fr with throws := fr.throws || exprCanThrow sigs ex }
  | r => r

/- ## Stack operations -/

/-- Pop one slot, demanding every atom below the upper bound T. -/
def popTy (T : Ty) (σ : List Ty) : Option (List Ty) :=
  match σ with
  | ts :: σ' => if tmoves ts T then some σ' else none
  | [] => none

def popA (t : VTy) (σ : List Ty) : Option (List Ty) := popTy [t] σ

def popTyN : Nat → Ty → List Ty → Option (List Ty)
  | 0, _, σ => some σ
  | k + 1, t, σ =>
      match popTy t σ with
      | some σ' => popTyN k t σ'
      | none => none

/- Argument check: the top n stack types REVERSED (the machine pushes
    args in order, so the top is the LAST argument) are pointwise
    below the callee's parameters. -/
def popArgs (ps σ : List Ty) : Bool :=
  σ.length ≥ ps.length && leTy (σ.take ps.length).reverse ps

def primTys (p : Prim) : Option (Ty × Ty) :=
  match p with
  | .pThrowC => none                     -- t ↦ throw completion, inline
  | .pWrapC => none                      -- t ↦ complN t, inline
  | .pUnwrapC => none                    -- complN t ↦ t, inline (typeOfE .complValue)
  | .pIsNormalC | .pIsThrowC | .pIsCompletion => none  -- correlated split, inline
  | .pIsObj | .pIsNotObj | .pIsNotU | .pHasCall | .pHasCtor | .pIsU
  | .pIsTrue | .pIsFalse | .pNullOrUnd | .pIsNull
  | .pIsType _ | .pHasField _ | .pIsStr _ => some (anyT, [.anyValue .bool])
  | .pDescField _ =>
      -- uniform: the receiver-side descent (GetOwnProperty's union)
      -- carries the precision; the field read is loose here. (The
      -- per-name refinement was unprovable for abstract names: the
      -- string-match in primTys cannot reduce.)
      some (anyT, anyT)
  | .pPred _ _ => none                      -- fused in kTestVar

/- ## Shape tests: the flat type a test's THEN side asserts -/

def typeMask : «String» → Ty
  | "Boolean" => [.anyValue .bool]
  | "Number" => [.anyValue .num]
  | "String" => [.anyValue .str]
  | _ => []        -- no such constructor in our universe

def testType : Expr → Option Ty
  | .isObject _ => some [.anyValue .obj]
  | .isNotObject _ => some (anyOf (anyTags.filter (fun c => c != .obj)))
  | .isU _ => some [.anyValue .undef]
  | .isNotUndefined _ => some (anyOf (anyTags.filter (fun c => c != .undef)))
  | .isNull _ => some [.anyValue .null]
  | .isNullOrUnd _ => some [.anyValue .undef, .anyValue .null]
  | .isBoolVal b _ => some [.isValue (.boolean b)]
  | .isStrVal s _ => some [.isValue (.str s)]
  | .isType ty _ => some (typeMask ty)
  | .varNotPresent _ => some [.notPresent]
  | _ => none

/-- The correlated-predicate stratum: these AO names fuse into
    kTestVar (machine + checker agree on exactly this test). -/
def fusedPred (f : «String») : Bool :=
  f == "IsDataDescriptor" || f == "IsAccessorDescriptor"

/-- The THEN-type of a fused variable test (per Prim). none = no
    refinement (undecided predicate: plain boolean push). -/
def testTypeP : Prim → Option Ty
  | .pIsObj => some [.anyValue .obj]
  | .pIsNotObj => some (anyOf (anyTags.filter (fun c => c != .obj)))
  | .pIsU => some [.anyValue .undef]
  | .pIsNotU => some (anyOf (anyTags.filter (fun c => c != .undef)))
  | .pIsNull => some [.anyValue .null]
  | .pNullOrUnd => some [.anyValue .undef, .anyValue .null]
  | .pIsTrue => some [.isValue (.boolean Bool.true)]
  | .pIsFalse => some [.isValue (.boolean Bool.false)]
  | .pIsStr s => some [.isValue (.str s)]
  | .pIsType s => some (typeMask s)
  | _ => none

/-- The variable a shape test inspects, if any. -/
def testedVar : Expr → Option «String»
  | .isObject (.nv x) | .isNotObject (.nv x) | .isU (.nv x)
  | .isNotUndefined (.nv x) | .isNull (.nv x) | .isNullOrUnd (.nv x)
  | .isBoolVal _ (.nv x) | .isStrVal _ (.nv x) | .isType _ (.nv x)
  | .varNotPresent x => some x
  | _ => none

/- Hand-rolled sequence fuel: the kIte arms recurse on (branch ++ rest),
    which the auto-generated sizeOf cannot compare across the append. -/

/- ## Sequence fuel (termination measure for checkSeq) -/

mutual
def efuel : Expr → Nat
  | .nv _ | .const _ | .nat _ | .varNotPresent _ => 1
  | .isObject e | .isNotObject e | .isNotUndefined e | .hasCall e
  | .hasCtor e | .isU e | .isBoolVal _ e | .isStrVal _ e
  | .isNullOrUnd e | .isNull e | .isType _ e | .hasField _ e
  | .isNormalC e | .isThrowC e | .isCompletion e | .complValue e
  | .completionOf e | .ifield _ e => efuel e + 1
  | .call _ as => (as.map efuel).sum + 2
  | .imeth _ r as => efuel r + (as.map efuel).sum + 2
  | .listE es => (es.map efuel).sum + 2

def ifuel : Instr → Nat
  | .kEval e => efuel e + 1
  | .kIte t e => sfuel t + sfuel e + 2
  | .kRepeatWhile _ b | .kRepeatTest _ b => sfuel b + 2
  | .kForStart _ b | .kForBody _ _ b => sfuel b + 2
  | _ => 1

def sfuel : List Instr → Nat
  | [] => 0
  | i :: rest => ifuel i + sfuel rest
end

theorem sfuel_cons (i : Instr) (rest : List Instr) :
    sfuel (i :: rest) = ifuel i + sfuel rest := rfl

theorem sfuel_append (t rest : List Instr) :
    sfuel (t ++ rest) ≤ sfuel t + sfuel rest := by
  induction t with
  | nil => simp [sfuel]
  | cons a t ih => simp only [List.cons_append, sfuel] at *; omega

theorem efuel_pos (e : Expr) : 1 ≤ efuel e := by
  cases e <;> simp only [efuel, List.map_cons, List.sum_cons, List.sum_nil] at * <;> omega

theorem ifuel_pos (i : Instr) : 1 ≤ ifuel i := by
  cases i with
  | kEval e => simp only [ifuel]; have := efuel_pos e; omega
  | kIte t e => simp only [ifuel]; omega
  | kRepeatWhile c b | kRepeatTest c b => simp only [ifuel]; omega
  | kForStart x b | kForBody x vs b => simp only [ifuel]; omega
  | kPrim1 p => cases p <;> simp only [ifuel] <;> omega
  | kCall f n => simp only [ifuel]; omega
  | kSet x => simp only [ifuel]; omega
  | kPop => simp only [ifuel]; omega
  | kAssert => simp only [ifuel]; omega
  | kRet => simp only [ifuel]; omega
  | kTest => simp only [ifuel]; omega
  | kUnwrap => simp only [ifuel]; omega
  | kIMeth nm n => simp only [ifuel]; omega
  | kMkList n => simp only [ifuel]; omega
  | kNewSlot sn => simp only [ifuel]; omega
  | kTestVar x p => cases p <;> simp only [ifuel] <;> omega

theorem sfuel_cons_gt (i : Instr) (rest : List Instr) :
    sfuel rest < sfuel (i :: rest) := by
  rw [sfuel_cons]
  have := ifuel_pos i
  omega

/-- The kIte arms recurse on (branch ++ rest). -/
theorem sfuel_ite_append_true (t e rest : List Instr) :
    sfuel (t ++ rest) < sfuel (.kIte t e :: rest) := by
  have h1 := sfuel_append t rest
  have h2 : sfuel t < sfuel t + sfuel e + 2 := by omega
  show sfuel (t ++ rest) < sfuel t + sfuel e + 2 + sfuel rest
  omega

theorem sfuel_ite_append_false (t e rest : List Instr) :
    sfuel (e ++ rest) < sfuel (.kIte t e :: rest) := by
  have h1 := sfuel_append e rest
  show sfuel (e ++ rest) < sfuel t + sfuel e + 2 + sfuel rest
  omega

/-- The 1-for-1 binder-test rewrites: kEval (isX (nv x)) > kTestVar x p. -/
theorem sfuel_testvar_lt (e : Expr) (x : «String») (p : Prim)
    (h : efuel e = 2) (rest : List Instr) :
    sfuel (.kTestVar x p :: rest) < sfuel (.kEval e :: rest) := by
  simp only [sfuel, ifuel, h]
  omega

/-- A completion-only slot (no bare atoms). kTest accepts only
    these, mirroring the machine's loud fall on bare values. -/
def complOnly : Ty → Bool
  | [] => Bool.true
  | a :: rest =>
      (match a with
       | .complN _ | .complT => Bool.true
       | _ => Bool.false) && complOnly rest

/-- Split a slot type by completion kind: the normal side (complN
    atoms, payloads kept) and the throw side. -/
def complNormals (t : Ty) : Ty :=
  t.filterMap (fun a => match a with | .complN p => some (.complN p) | _ => none)

def complHasThrow (t : Ty) : Bool :=
  t.any (fun a => match a with | .complT => Bool.true | _ => Bool.false)

/-- The payloads of a complN-ONLY slot (none if any atom is not a
    normal completion). -/
def unwrapSlot : Ty → Option Ty
  | [] => some []
  | .complN p :: rest => (unwrapSlot rest).map (fun ps => p :: ps)
  | _ :: _ => none

/-- The complN-wrapping of a BARE-only slot (none if any atom is a
    completion). -/
def bareSlot : Ty → Option Ty
  | [] => some []
  | a :: rest =>
      match isBareVTy a with
      | Bool.true => (bareSlot rest).map (fun ps => a :: ps)
      | Bool.false => none

/-- Step ONE world through one stack instruction (no control flow).
    Fails (none) on shape mismatch; the completion test (kTest)
    splits by completion kind — the same fork machinery as the Γ
    splits, applied to the slot. -/
def step1 (sigs : SigTable) (i : Instr) (w : World) : Option Worlds :=
  match i with
  | .kPrim1 .pWrapC =>
      -- wrap-IF-BARE (machine-aligned: a completion flows through
      -- unchanged; a bare value gets a fresh normal completion).
      -- compl-pure slots: identity; bare-only slots: complN-wrap;
      -- mixed: reject (machine-visible ambiguity, never pushed).
      match w.σ with
      | t :: σ' =>
          if complOnly t then some [{ w with σ := t :: σ' }]
          else (bareSlot t).map (fun wt =>
            [{ w with σ := wt.map VTy.complN :: σ' }])
      | [] => none
  | .kPrim1 .pThrowC =>
      match w.σ with
      | _ :: σ' => some [{ w with σ := [VTy.complT] :: σ' }]
      | [] => none
  | .kPrim1 p =>
      match primTys p with
      | some (tin, tout) =>
          match popTy tin w.σ with
          | some σ' => some [{ w with σ := tout :: σ' }]
          | none => none
      | none => some [w]
  | .kCall f n =>
      match sigFind sigs f with
      | none => none
      | some (ps, retj) =>
          match (ps.length == n) || (ps.length == n + 1) with
          | false => none
          | true =>
              match popArgs (if ps.length == n then ps else ps.take n) w.σ with
              | false => none
              | true => some [{ w with σ := complTy retj :: w.σ.drop n }]
  | .kSet x =>
      match w.σ with
      | t :: σ' => some [{ w with Γ := (x, t) :: w.Γ, σ := σ' }]
      | [] => none
  | .kPop =>
      match w.σ with
      | _ :: σ' => some [{ w with σ := σ' }]
      | [] => none
  | .kTest =>
      -- peek the top slot: split by completion kind, push the
      -- verdict. The machine is LOUD unless the top is a
      -- completion, so acceptance requires a completion-only slot -
      -- a possibly-bare slot is a loud run and rejects here.
      match w.σ with
      | t :: σ' =>
          if complOnly t then
            match (match complNormals t with
                   | [] => []
                   | _ => [{ w with σ := [.isValue (.boolean Bool.false)] :: complNormals t :: σ' }])
                ++ (match complHasThrow t with
                    | Bool.true => [{ w with σ := [.isValue (.boolean Bool.true)] :: [VTy.complT] :: σ' }]
                    | Bool.false => []) with
            | [] => none
            | ws => some ws
          else none
      | [] => none
  | .kUnwrap =>
      match w.σ with
      | t :: σ' => (unwrapSlot t).map (fun ps => [{ w with σ := ps :: σ' }])
      | [] => none
  | .kIMeth nm n =>
      match mopArity nm == some n with
      | false => none
      | true =>
          match popTyN n anyT w.σ with
          | none => none
          | some σ' =>
              match popA (.anyValue .obj) σ' with
              | none => none
              | some σ'' =>
                  some [{ w with σ := complTy (mopResult nm) :: σ'' }]
  | .kMkList n =>
      match popTyN n anyT w.σ with
      | some σ' => some [{ w with σ := [.anyValue .list] :: σ' }]
      | none => none
  | .kNewSlot sn =>
      match slotOfName sn with
      | none => none
      | some _ =>
          match popTy anyT w.σ with
          | some σ' => some [{ w with σ := [.anyValue .obj] :: σ' }]
          | none => none
  | _ => some [w]

/-- Correlated predicate tests: IsDataDescriptor(x) /
    IsAccessorDescriptor(x) are decidable per EXACT desc atom. -/
def predDecide (f : «String») : Option (VTy → Option Bool) :=
  match f with
  | "IsDataDescriptor" =>
      some (fun t => match t with
        | .desc fs => some (fs.any (fun fld => fData.contains fld))
        | _ => none)
  | "IsAccessorDescriptor" =>
      some (fun t => match t with
        | .desc fs => some (fs.any (fun fld => fAcc.contains fld))
        | _ => none)
  | _ => none

/-- Split ONE world at a shape test of x with then-type T. -/
def split1 (x : «String») (T : Ty) (w : World) : Worlds :=
  match tyLookup w.Γ x with
  | none => []
  | some S =>
      (match meetTy S T with
       | [] => []
       | _ => [{ Γ := (x, meetTy S T) :: w.Γ,
                 σ := [.isValue (.boolean Bool.true)] :: w.σ }])
      ++ (match removeTy S T with
       | [] => []
       | _ => [{ Γ := (x, removeTy S T) :: w.Γ,
                 σ := [.isValue (.boolean Bool.false)] :: w.σ }])

/-- Split ONE world by a per-atom predicate decider. -/
def splitP1 (x : «String») (dec : VTy → Option Bool) (w : World) : Worlds :=
  match tyLookup w.Γ x with
  | none => []
  | some S =>
      let go (acc : Worlds) (a : VTy) : Worlds :=
        match dec a with
        | some Bool.true =>
            acc ++ [{ Γ := (x, [a]) :: w.Γ,
                      σ := [.isValue (.boolean Bool.true)] :: w.σ }]
        | some Bool.false =>
            acc ++ [{ Γ := (x, [a]) :: w.Γ,
                      σ := [.isValue (.boolean Bool.false)] :: w.σ }]
        | none =>
            acc ++ [{ Γ := (x, [a]) :: w.Γ,
                      σ := [.isValue (.boolean Bool.true)] :: w.σ },
                    { Γ := (x, [a]) :: w.Γ,
                      σ := [.isValue (.boolean Bool.false)] :: w.σ }]
      S.foldl go []

/- Loop join: every falls-world must come back to a REFINEMENT of
    the loop-entry stack with no parked completion (neutrality). -/
def checkLoopBody (rbody : TCResult) (site : Instr)
    (σ₀ : List Ty) (k : Worlds → TCResult) : TCResult :=
  match rbody with
  | .reject site' why => .reject site' why
  | .flows fb =>
      let neutral := fb.falls.all (fun w =>
        w.σ.length == σ₀.length
          && (List.zip w.σ σ₀).all (fun (t, u) => tmoves t u))
      if neutral then
        match k fb.falls with
        | .flows fr => .flows { exits := fb.exits || fr.exits,
                                throws := fb.throws || fr.throws,
                                falls := fr.falls,
                                assumes := fb.assumes ++ fr.assumes }
        | res => res
      else .reject site "loop body is not stack-neutral"

/-- Result merge for forks: rejection dominates, otherwise the
    summaries combine (exits/throws disjoin, falls/assumes append). -/
def mergeTC : TCResult → TCResult → TCResult
  | .reject s w, _ => .reject s w
  | _, .reject s w => .reject s w
  | .flows f₁, .flows f₂ =>
      .flows { exits := f₁.exits || f₂.exits
             , throws := f₁.throws || f₂.throws
             , falls := f₁.falls ++ f₂.falls
             , assumes := f₁.assumes ++ f₂.assumes }

/-- The empty summary (fork-fold identity). -/
def noFlows : TCResult :=
  .flows { exits := Bool.false, throws := Bool.false, falls := [], assumes := [] }

/-- The vacuous OK (conjunction seed): the empty index set accepts.
    A bottom (unreachable) slot folds to this. -/
def vacOk : TCResult :=
  .flows { exits := Bool.true, throws := Bool.false, falls := [], assumes := [] }

/-- Fork fold over CONCRETE successor worlds: an empty successor set
    is a stuck (or unreachable) world and rejects — it is the dual
    of the vacuous-OK seed: an empty SUCCESSOR SET is stuck, an
    empty VERDICT SLOT is unreachable. -/
def forkTC (site : Instr) (ws : Worlds) (k : World → TCResult) : TCResult :=
  match ws with
  | [] => .reject site "empty fork (stuck or unreachable world)"
  | _ => ws.foldl (fun acc u => mergeTC acc (k u)) noFlows

/-- Record an undischarged assert as proof debt on the result. -/
def markDebt (why : «String») : TCResult → TCResult :=
  fun res => match res with
  | .flows f => .flows { f with assumes := why :: f.assumes }
  | r => r

def checkSeq : SigTable → Ty → World → List Instr → TCResult
  | _, _, w, [] => .flows { exits := Bool.false, throws := Bool.false, falls := [w], assumes := [] }
  | _, r, w, .kRet :: _ =>
      -- the frame returns its top: a completion (complN payload ⊑
      -- r's payloads, or complT when r declares throw)
      match w.σ with
      | t :: σ' =>
          if tmoves t r then
            .flows { exits := Bool.true,
                     throws := complHasThrow t,
                     falls := [], assumes := [] }
          else
            .reject .kRet ("kRet: payload does not match the frame's destiny r: "
              ++ toString (toString (repr t) ++ toString (repr w.σ)))
      | [] =>
          .reject .kRet ("kRet: payload does not match the frame's destiny r: "
            ++ toString (toString (repr w.σ)))
  | sigs, r, w, .kIte t e :: rest =>
      -- dispatch per VERDICT ATOM of the top slot: true checks a
      -- then-world, false an else-world, a bool-union spawns both
      -- (fork), any other atom rejects. The atom judgements combine
      -- with a mergeTC fold — reject-dominating, so the fold IS the
      -- conjunction — seeded with the vacuous OK: the empty slot is
      -- the bottom type (unreachable) and accepts vacuously, exactly
      -- as a conjunction over an empty index set does.
      match w.σ with
      | [] => .reject (.kIte t e) "kIte: verdict is not boolean"
      | ts :: σ' =>
          ts.foldl (fun acc a =>
            mergeTC acc
              (match a with
               | .isValue (.boolean Bool.true) =>
                   checkSeq sigs r { w with σ := σ' } (t ++ rest)
               | .isValue (.boolean Bool.false) =>
                   checkSeq sigs r { w with σ := σ' } (e ++ rest)
               | .anyValue .bool =>
                   mergeTC (checkSeq sigs r { w with σ := σ' } (t ++ rest))
                     (checkSeq sigs r { w with σ := σ' } (e ++ rest))
               | _ => .reject (.kIte t e) "kIte: verdict is not boolean"))
            vacOk
  | sigs, r, w, .kEval (.varNotPresent x) :: rest =>
      -- presence test: unbound means NOT present (verdict true);
      -- a binding splits (then: notPresent, else: the alternatives)
      match tyLookup w.Γ x with
      | none => checkSeq sigs r { w with σ := [.isValue (.boolean Bool.true)] :: w.σ } rest
      | some _ =>
          forkTC (.kEval (.varNotPresent x)) (split1 x [.notPresent] w)
            (fun u => checkSeq sigs r u rest)
  | sigs, r, w, .kEval (.isObject (.nv x)) :: rest =>
      checkSeq sigs r w (.kTestVar x .pIsObj :: rest)
  | sigs, r, w, .kEval (.isNotObject (.nv x)) :: rest =>
      checkSeq sigs r w (.kTestVar x .pIsNotObj :: rest)
  | sigs, r, w, .kEval (.isNotUndefined (.nv x)) :: rest =>
      checkSeq sigs r w (.kTestVar x .pIsNotU :: rest)
  | sigs, r, w, .kEval (.isU (.nv x)) :: rest =>
      checkSeq sigs r w (.kTestVar x .pIsU :: rest)
  | sigs, r, w, .kEval (.hasCall (.nv x)) :: rest =>
      checkSeq sigs r w (.kTestVar x .pHasCall :: rest)
  | sigs, r, w, .kEval (.hasCtor (.nv x)) :: rest =>
      checkSeq sigs r w (.kTestVar x .pHasCtor :: rest)
  | sigs, r, w, .kEval (.isNull (.nv x)) :: rest =>
      checkSeq sigs r w (.kTestVar x .pIsNull :: rest)
  | sigs, r, w, .kEval (.isNullOrUnd (.nv x)) :: rest =>
      checkSeq sigs r w (.kTestVar x .pNullOrUnd :: rest)
  | sigs, r, w, .kEval (.isBoolVal Bool.true (.nv x)) :: rest =>
      checkSeq sigs r w (.kTestVar x .pIsTrue :: rest)
  | sigs, r, w, .kEval (.isBoolVal Bool.false (.nv x)) :: rest =>
      checkSeq sigs r w (.kTestVar x .pIsFalse :: rest)
  | sigs, r, w, .kEval (.isStrVal s (.nv x)) :: rest =>
      checkSeq sigs r w (.kTestVar x (.pIsStr s) :: rest)
  | sigs, r, w, .kEval (.isNormalC (.nv x)) :: rest =>
      checkSeq sigs r w (.kTestVar x .pIsNormalC :: rest)
  | sigs, r, w, .kEval (.isThrowC (.nv x)) :: rest =>
      checkSeq sigs r w (.kTestVar x .pIsThrowC :: rest)
  | sigs, r, w, .kEval (.isCompletion (.nv x)) :: rest =>
      checkSeq sigs r w (.kTestVar x .pIsCompletion :: rest)
  | sigs, r, w, .kEval (.isType ty (.nv x)) :: rest =>
      checkSeq sigs r w (.kTestVar x (.pIsType ty) :: rest)
  | sigs, r, w, .kEval (.hasField nm (.nv x)) :: rest =>
      checkSeq sigs r w (.kTestVar x (.pHasField nm) :: rest)
  | sigs, r, w, .kEval (.isBoolVal b (.call f [.nv x])) :: rest =>
      -- the machine fuses exactly the descriptor predicates natively
      if fusedPred f
      then checkSeq sigs r w (.kTestVar x (.pPred f b) :: rest)
      else
        match typeOfE sigs w.Γ (.isBoolVal b (.call f [.nv x])) with
        | none => .reject (.kEval (.isBoolVal b (.call f [.nv x])))
            "ill-typed expression (unbound or bad args)"
        | some t =>
            markThrow sigs (.isBoolVal b (.call f [.nv x]))
              (checkSeq sigs r { w with σ := t :: w.σ } rest)
  | sigs, r, w, .kRepeatWhile c body :: rest =>
      -- LOOPS RUN ON THE EMPTY STACK: loop-local state lives in Γ
      -- (kSet/kEval pairs are net-zero on σ). The neutrality
      -- demand is then the constant "falls are empty" — no
      -- entry-derived invariant, so refinement cannot flip it.
      match w.σ with
      | [] =>
          match typeOfE sigs w.Γ c with
          | some t =>
              if tmoves t [.anyValue .bool] then
                  checkLoopBody (checkSeq sigs r w body) (.kRepeatWhile c body)
                    [] (fun wsf => wsf.foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows)
              else .reject (.kRepeatWhile c body) "loop condition is not boolean"
          | none => .reject (.kRepeatWhile c body) "loop condition is not boolean"
      | _ => .reject (.kRepeatWhile c body) "loop entry stack is not empty"
  | sigs, r, w, .kEval ex :: rest =>
      -- summary arm: the call/imeth/list/ifield dust's NET world effect
      -- (args pushed then popped, payload parked then unwrapped) equals
      -- this push; the expansion-step preservation is a net-effect lemma
      match typeOfE sigs w.Γ ex with
      | none => .reject (.kEval ex) "ill-typed expression (unbound or bad args)"
      | some t =>
          markThrow sigs ex (checkSeq sigs r { w with σ := t :: w.σ } rest)
  | sigs, r, w, .kTestVar x p :: rest =>
      -- FUSED variable test: the Γ-correlated split site
      match p with
      | .pPred f _ =>
          match predDecide f with
          | some dec =>
              forkTC (.kTestVar x p) (splitP1 x dec w)
                (fun u => checkSeq sigs r u rest)
          | none =>
              match tyLookup w.Γ x with
              | none => .reject (.kTestVar x p) "unbound variable"
              | some _ =>
                  checkSeq sigs r { w with σ := [.anyValue .bool] :: w.σ } rest
      | .pIsNormalC | .pIsThrowC =>
          match primDecide p with
          | some dec =>
              forkTC (.kTestVar x p) (splitP1 x dec w)
                (fun u => checkSeq sigs r u rest)
          | none =>
              match tyLookup w.Γ x with
              | none => .reject (.kTestVar x p) "unbound variable"
              | some _ =>
                  checkSeq sigs r { w with σ := [.anyValue .bool] :: w.σ } rest
      | _ =>
          match testTypeP p with
          | some T =>
              forkTC (.kTestVar x p) (split1 x T w)
                (fun u => checkSeq sigs r u rest)
          | none =>
              match tyLookup w.Γ x with
              | none => .reject (.kTestVar x p) "unbound variable"
              | some _ =>
                  checkSeq sigs r { w with σ := [.anyValue .bool] :: w.σ } rest
  | sigs, r, w, .kRepeatTest c body :: rest =>
      match popTy [.anyValue .bool] w.σ with
      | none => .reject (.kRepeatTest c body) "loop verdict is not boolean"
      | some [] =>
          checkLoopBody (checkSeq sigs r { w with σ := [] } body) (.kRepeatTest c body)
            [] (fun wsf => wsf.foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows)
      | some (_ :: _) => .reject (.kRepeatTest c body) "loop entry stack is not empty"
  | sigs, r, w, .kForStart x body :: rest =>
      match popA (.anyValue .list) w.σ with
      | none => .reject (.kForStart x body) "for-each over a non-list"
      | some [] =>
          checkLoopBody (checkSeq sigs r
            { w with Γ := (x, langT) :: w.Γ, σ := [] } body) (.kForStart x body)
            [] (fun wsf => wsf.foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows)
      | some (_ :: _) => .reject (.kForStart x body) "loop entry stack is not empty"
  | sigs, r, w, .kForBody x _ body :: rest =>
      match w.σ with
      | [] =>
          checkLoopBody (checkSeq sigs r { w with Γ := (x, langT) :: w.Γ } body)
            (.kForBody x [] body)
            [] (fun wsf => wsf.foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows)
      | _ => .reject (.kForBody x [] body) "loop entry stack is not empty"
  | sigs, r, w, .kAssert :: rest =>
      -- assert, per VERDICT ATOM, machine-aligned (the machine
      -- continues ONLY on .boolean true; false, non-boolean and
      -- empty are LOUD): true discharges (pop, clean); a genuinely
      -- undecided bool pops with the debt recorded; everything
      -- else — statically false, or not boolean at all — is a path
      -- the machine is loud on and rejects. The fold is the
      -- conjunction; the bottom slot is the vacuous fold
      -- (discharged), exactly as in kIte.
      match w.σ with
      | [] => .reject .kAssert "assert: verdict is not boolean"
      | ts :: σ' =>
          ts.foldl (fun acc a =>
            mergeTC acc
              (match a with
               | .isValue (.boolean Bool.true) =>
                   checkSeq sigs r { w with σ := σ' } rest
               | .anyValue .bool =>
                   markDebt "assert obligation not discharged"
                     (checkSeq sigs r { w with σ := σ' } rest)
               | _ => .reject .kAssert "assert: verdict is not boolean"))
            vacOk
  | sigs, r, w, i :: rest =>
      match step1 sigs i w with
      | none =>
          .reject i ("world stack mismatch: " ++ toString (repr w))
      | some ws' =>
          forkTC i ws' (fun u => checkSeq sigs r u rest)
termination_by _ _ _ is => sfuel is
decreasing_by
  all_goals
    first
      | exact sfuel_ite_append_true t e rest
      | exact sfuel_ite_append_false t e rest
      | exact sfuel_cons_gt _ _
      | (simp only [sfuel_cons, ifuel, efuel]; omega)
      | (simp only [sfuel_cons, ifuel]; omega)
      | (exfalso; simp_all)
      | omega
      | (rename_i l; exact absurd rfl (by intro _; exact l.elim))

def typecheckSeq (sigs : SigTable) (r : Ty) (Γ : TyEnv) (seq : List Instr) : TCResult :=
  checkSeq sigs r { Γ := Γ, σ := [] } seq

def typecheckAO (sigs : SigTable)
    (name : «String») (params : List «String») (body : List Instr) : Option TCResult :=
  match sigFind sigs name with
  | none =>
      some (.reject (body.head?.getD .kRet)
        (name ++ " has no entry in the signature table"))
  | some (paramTys, retj) =>
      if params.length != paramTys.length then
        some (.reject (body.head?.getD .kRet)
          (name ++ ": registry arity/signature arity mismatch"))
      else match typecheckSeq sigs (complTy retj) (zipTy params paramTys) body with
        | .flows f =>
            -- JUDGEMENT CONSISTENCY: a body that can exit via a throw
            -- must carry throw in its declared completion judgement
            if terminal f && (!f.throws || complCanThrow retj) then none
            else some (.flows f)
        | res => some res

def typecheckReg (sigs : SigTable) (reg : AOReg) : Option («String» × TCResult) :=
  match reg with
  | [] => none
  | (name, (params, prog)) :: rest =>
      match typecheckAO sigs name params (compileSteps prog) with
      | some r => some (name, r)
      | none => typecheckReg sigs rest

def typecheckRegOk (sigs : SigTable) (reg : AOReg) : Bool :=
  (typecheckReg sigs reg).isNone
