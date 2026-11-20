import Metalanguage.Grammar
import Metalanguage.Semantics
import Metalanguage.Typecheck

/- # Subject reduction: fstep preserves typing.

    A frame TYPES AS P: `checkSeq` of its remaining instructions,
    started from the canonically-abstracted runtime stack (values →
    singleton slots; at most one parked completion → the pending
    field, or an anticipated one when a callee sits directly above),
    falls through to an eval stack of shape P — or exits via kRet.
    Each machine step preserves the judgment.

    FLAT LATTICE REWORK: completions are no longer stack atoms. The
    runtime eval stack is split into (σ, pending) by splitStack; the
    parked completion is the machine's self-test idiom territory.
    The proof layer is being re-proven on the simpler lattice — the
    arms are the same, the normalization lemmas are gone. -/

/- Runtime-value <-> static-type agreement is definitional: -/

/- ## The frame <-> world bridge (direct: one eval stack)

    Completions are ordinary values; the abstraction of eval is the
    pointwise singleton map (typeOfV is completion-aware), and Γ
    maps likewise. No splitStack, no pending field: the slot's type
    gives its position and kind. -/

def isCompl : JSValue → Bool
  | .compl _ _ => Bool.true
  | _ => Bool.false

def envTyOf (η : HeapCallableTy) : Env → TyEnv := fun env =>
  env.map (fun (n, v) => (n, [normalizeAtom η (typeOfV v)]))

theorem envTyOf_lookup (η : HeapCallableTy) (env : Env) (x : «String») :
    (lookup env x).map
        (fun v => [normalizeAtom η (typeOfV v)])
      = tyLookup (envTyOf η env) x := by
  induction env with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨n, v⟩ := hd
      by_cases h : n == x
      · simp [lookup, tyLookup, envTyOf, h]
      · simp [lookup, tyLookup, envTyOf, h, ih]

theorem envTyOf_cons (η : HeapCallableTy) (n : «String») (v : JSValue)
    (env : Env) :
    envTyOf η ((n, v) :: env)
      = (n, [normalizeAtom η (typeOfV v)]) :: envTyOf η env := rfl

/-- Normalization kills exactly the exact-object singletons; it is
    idempotent and never re-introduces one. -/
theorem normalizeAtom_idem (η : HeapCallableTy) :
    ∀ (a : VTy), normalizeAtom η (normalizeAtom η a) = normalizeAtom η a
  | .isValue (.obj l) => rfl
  | .isValue .undefined => rfl
  | .isValue .null => rfl
  | .isValue (.boolean _) => rfl
  | .isValue (.number _) => rfl
  | .isValue (.str _) => rfl
  | .isValue (.listV _) => rfl
  | .isValue (.descV _) => rfl
  | .isValue (.compl _ _) => rfl
  | .complN p => by
      have ih := normalizeAtom_idem η p
      simp only [normalizeAtom, ih]
  | .complT => rfl
  | .anyValue _ => rfl
  | .desc _ => rfl
  | .notPresent => rfl

theorem normalizeAtom_notObj (η : HeapCallableTy) :
    ∀ (a : VTy) (l : Nat), normalizeAtom η a ≠ .isValue (.obj l)
  | .isValue (.obj l') => by intro l h; simp [normalizeAtom] at h
  | .isValue .undefined => by intro l h; simp [normalizeAtom] at h
  | .isValue .null => by intro l h; simp [normalizeAtom] at h
  | .isValue (.boolean _) => by intro l h; simp [normalizeAtom] at h
  | .isValue (.number _) => by intro l h; simp [normalizeAtom] at h
  | .isValue (.str _) => by intro l h; simp [normalizeAtom] at h
  | .isValue (.listV _) => by intro l h; simp [normalizeAtom] at h
  | .isValue (.descV _) => by intro l h; simp [normalizeAtom] at h
  | .isValue (.compl _ _) => by intro l h; simp [normalizeAtom] at h
  | .complN p => by
      intro l h
      simp only [normalizeAtom] at h
      cases hp : normalizeAtom η p with
      | isValue v =>
          rw [hp] at h
          cases v with
          | obj l' => simp at h
          | undefined | null | boolean _ | number _ | str _ | listV _
            | descV _ | compl _ _ => simp at h
      | complN q | complT | anyValue _ | desc _ | notPresent =>
          rw [hp] at h
          simp at h
  | .complT => by intro l h; simp [normalizeAtom] at h
  | .anyValue _ => by intro l h; simp [normalizeAtom] at h
  | .desc _ => by intro l h; simp [normalizeAtom] at h
  | .notPresent => by intro l h; simp [normalizeAtom] at h

/-- THE ABSTRACTION FUNCTION: value frame → type-machine state
    (the canonical singleton map — the bridge, named; implicit in
    frameTyped). -/
def frameWorld (η : HeapCallableTy) (f : Fr) : World :=
  { η := η, Γ := envTyOf η f.env,
    σ := f.eval.map (fun v => [normalizeAtom η (typeOfV v)]) }

/- ## The anticipated completion.

    After kCall / kIMeth fire, the caller's instructions are
    `kTest :: kIte [kRet] [kUnwrap] :: rest` and the completion it
    will test does not exist yet: it is INSIDE the callee frame
    above, and will be delivered INTO the caller's pending. The
    judgment anticipates BOTH deliveries — a normal payload TYPED
    by the callee's destiny, and a throw. Each delivery must check;
    the throw side exits at the self-test's kRet (exempt), the
    normal side continues through kUnwrap. -/

def selfTestHead : List Instr → Bool
  | .kTest :: .kIte [.kRet] [.kUnwrap] :: _ => Bool.true
  | _ => Bool.false

/- ## Frame and state typing -/

/-- The frame's check at a GIVEN top-slot type (the anticipation:
    the completion a callee above will deliver onto this stack). -/
def frameChecksAt (sigs : SigTable) (η : HeapCallableTy) (f : Fr)
    (top : Ty) : Prop :=
  match checkSeq sigs (sigRetTy sigs f.ret)
    { η := η, Γ := envTyOf η f.env,
      σ := top :: f.eval.map (fun v => [normalizeAtom η (typeOfV v)]) }
      f.stmts with
  | .flows fb => terminal fb = Bool.true  -- every world returns
  | _ => False

/-- The frame's check as it stands. -/
def frameChecks (sigs : SigTable) (η : HeapCallableTy) (f : Fr) : Prop :=
  match checkSeq sigs (sigRetTy sigs f.ret) (frameWorld η f) f.stmts with
  | .flows fb => terminal fb = Bool.true  -- every world returns
  | _ => False

def frameOk (sigs : SigTable) (η : HeapCallableTy)
    (above : Option «String») (f : Fr) : Prop :=
  -- a frame under a callee MUST be waiting at the self-test idiom:
  -- the delivery assumption of kRet
  (above.isNone ∨ selfTestHead f.stmts = Bool.true)
    ∧ (match above with
       | some n => ∀ c ∈ sigCompls sigs n,
           frameChecksAt sigs η f (complTy [c])
       | none => frameChecks sigs η f)

/-- Each frame is checked at its own destiny (its AO's declared
    return type), anticipating a delivery TYPED by the frame directly
    above. -/
def framesOkFrom (η : HeapCallableTy) :
    SigTable → Option «String» → List Fr → Prop
  | _, _, [] => True
  | sigs, above, f :: fs =>
      frameOk sigs η above f
        ∧ framesOkFrom η sigs f.ret fs

def framesOk (sigs : SigTable) (η : HeapCallableTy)
    (fs : List Fr) : Prop :=
  framesOkFrom η sigs none fs


-- Object references reachable from a value (completions carry
-- payloads; descriptors and lists carry values).
mutual
def locsList : List JSValue → List Nat
  | [] => []
  | v :: vs => locsOf v ++ locsList vs
termination_by vs => sizeOf vs
decreasing_by all_goals simp_wf <;> omega

def locsOf : JSValue → List Nat
  | .obj l => [l]
  | .compl _ v => locsOf v
  | .descV (.mk (some v) _ (some g) (some s) _ _) =>
      locsOf v ++ [g, s]
  | .descV (.mk (some v) _ _ (some s) _ _) => locsOf v ++ [s]
  | .descV (.mk (some v) _ (some g) _ _ _) => locsOf v ++ [g]
  | .descV (.mk (some v) _ _ _ _ _) => locsOf v
  | .descV (.mk none _ (some g) (some s) _ _) => [g, s]
  | .descV (.mk none _ _ (some s) _ _) => [s]
  | .descV (.mk none _ (some g) _ _ _) => [g]
  | .descV _ => []
  | .listV vs => locsList vs
  | _ => []
termination_by v => sizeOf v
decreasing_by all_goals simp_wf <;> omega
end

theorem locsOf_compl (b : Bool) (v : JSValue) :
    locsOf (.compl b v) = locsOf v := by rw [locsOf]

/- References out of an allocated object: property descriptor
    payloads. -/
def objRefs (o : JsObj) : List Nat :=
  (o.props.flatMap (fun (_, d) =>
     match d with
     | .mk (some v) _ _ _ _ _ => locsOf v
     | _ => []))

/-- Heap agreement over a BOUNDED region [0, n) — the region grows
    with allocation, so no separate nextLoc conjunct is needed. -/
def heapOk (heap : Heap) (n : Nat) : List Fr → Prop
  | [] =>
      (∀ l < n, ∀ o, heap l = some o →
          (objRefs o).all (fun r => r < n ∧ (heap r).isSome))
      ∧ ∀ l, n ≤ l → heap l = none
  | f :: fs =>
      (∀ l ∈ (f.eval.flatMap locsOf ++ (f.env.map Prod.snd).flatMap locsOf),
        l < n ∧ (heap l).isSome)
      ∧ heapOk heap n fs

/- ## Heap typing (store typing) -/

structure HeapObjTy where
  kind : Kind
  callable : Bool

abbrev HeapTy := Nat → HeapObjTy

def kindCallable : Kind → Bool
  | .builtin _ _ => Bool.true
  | _ => Bool.false

def heapCallableTy (ht : HeapTy) : HeapCallableTy :=
  fun loc => (ht loc).callable

def runtimeCallable (heap : Heap) : HeapCallableTy :=
  fun loc =>
    match heap loc with
    | some o => kindCallable o.kind
    | none => Bool.false

def objConsistent (k : Kind) (o : JsObj) : Bool :=
  match k, o.kind with
  | .ordinary, .ordinary => Bool.true
  | .string _, .string _ => Bool.true
  | .builtin _ _, .builtin _ _ => Bool.true
  | _, _ => Bool.false

def heapTyOk (heap : Heap) (ht : HeapTy) (n : Nat) : Prop :=
  ∀ l < n, ∀ o, heap l = some o →
    objConsistent (ht l).kind o = Bool.true
      ∧ (ht l).callable = kindCallable o.kind
      ∧ ∀ p, o.proto = some p →
          p < n ∧ (heap p).isSome = Bool.true
            ∧ (ht p).kind = .ordinary

def heapCallabilityOk (heap : Heap) (η : HeapCallableTy) : Prop :=
  ∀ l, η l = runtimeCallable heap l

/- The machine's return type is the BOTTOM frame's destiny (stable:
    only that frame popping turns the state into fdone). -/
def machineRet (sigs : SigTable) (fs : List Fr) : Ty :=
  match fs.getLast? with
  | some f => sigRetTy sigs f.ret
  | none => [.anyValue .undef]

/- ## State typing, indexed by the machine's answer type r.

    fell is ILL-TYPED: with this definition, preservation alone
    already implies progress. -/

mutual
def exprLocs : Expr → List Nat
  | .const v => locsOf v
  | .isObject e | .isNotObject e | .isNotUndefined e | .hasCall e
  | .hasCtor e | .isU e | .isBoolVal _ e | .isStrVal _ e
  | .isNullOrUnd e | .isNull e | .isType _ e | .hasField _ e
  | .ifield _ e | .isNormalC e | .isThrowC e | .isCompletion e
  | .complValue e | .completionOf e => exprLocs e
  | .imeth _ recv args => exprLocs recv ++ exprLocsList args
  | .call _ args => exprLocsList args
  | .listE es => exprLocsList es
  | .nv _ | .nat _ | .varNotPresent _ => []
  termination_by e => sizeOf e
  decreasing_by all_goals simp_wf <;> omega

def exprLocsList : List Expr → List Nat
  | [] => []
  | e :: es => exprLocs e ++ exprLocsList es
  termination_by es => sizeOf es
  decreasing_by all_goals simp_wf <;> omega
end

mutual
def instrLocs : Instr → List Nat
  | .kEval e => exprLocs e
  | .kForBody _ vs body => vs.flatMap locsOf ++ instrsLocs body
  | .kForStart _ body => instrsLocs body
  | .kIte t e => instrsLocs t ++ instrsLocs e
  | .kRepeatWhile c body | .kRepeatTest c body => exprLocs c ++ instrsLocs body
  | _ => []
  termination_by i => sizeOf i
  decreasing_by all_goals simp_wf <;> omega

def instrsLocs : List Instr → List Nat
  | [] => []
  | i :: rest => instrLocs i ++ instrsLocs rest
  termination_by is => sizeOf is
  decreasing_by all_goals simp_wf <;> omega
end

def exprWf (heap : Heap) (nl : Nat) (e : Expr) : Prop :=
  ∀ l ∈ exprLocs e, l < nl ∧ (heap l).isSome = Bool.true

def instrWf (heap : Heap) (nl : Nat) (i : Instr) : Prop :=
  ∀ l ∈ instrLocs i, l < nl ∧ (heap l).isSome = Bool.true

def instrsWf (heap : Heap) (nl : Nat) : List Instr → Prop
  | [] => True
  | i :: rest => instrWf heap nl i ∧ instrsWf heap nl rest

theorem instrsLocs_append (l₁ l₂ : List Instr) :
    instrsLocs (l₁ ++ l₂) = instrsLocs l₁ ++ instrsLocs l₂ := by
  induction l₁ with
  | nil => simp [instrsLocs]
  | cons i tl ih =>
      simp only [List.cons_append, instrsLocs, ih, List.append_assoc]

theorem instrWf_mem {heap : Heap} {nl : Nat} {i : Instr}
    (h : instrWf heap nl i) (l : Nat) (hl : l ∈ instrLocs i) :
    l < nl ∧ (heap l).isSome = Bool.true := h l hl

theorem instrsWf_iff_locs {heap : Heap} {nl : Nat} :
    ∀ (ls : List Instr),
      instrsWf heap nl ls ↔ ∀ l ∈ instrsLocs ls, l < nl ∧ (heap l).isSome = Bool.true := by
  intro ls
  induction ls with
  | nil => simp [instrsWf, instrsLocs]
  | cons i tl ih =>
      constructor
      · intro h l hl
        simp only [instrsLocs, List.mem_append] at hl
        rcases hl with hl' | hl'
        · exact h.1 l hl'
        · exact ih.mp h.2 l hl'
      · intro h
        constructor
        · intro l hl; exact h l (by
            simp only [instrsLocs, List.mem_append]; exact Or.inl hl)
        · exact ih.mpr (fun l hl => h l (by
            simp only [instrsLocs, List.mem_append]; exact Or.inr hl))

theorem instrsWf_append_intro {heap : Heap} {nl : Nat} : ∀ (l₁ l₂ : List Instr),
    instrsWf heap nl l₁ → instrsWf heap nl l₂ → instrsWf heap nl (l₁ ++ l₂) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ _ h₂; exact h₂
  | cons i tl ih => intro l₂ h₁ h₂; exact ⟨h₁.1, ih l₂ h₁.2 h₂⟩

theorem instrWf_kIte_elim {heap : Heap} {nl : Nat} {t e : List Instr}
    (h : instrWf heap nl (.kIte t e)) :
    instrsWf heap nl t ∧ instrsWf heap nl e := by
  constructor
  · rw [instrsWf_iff_locs]
    intro l hl
    exact h l (by
      simp only [instrLocs, instrsLocs_append, List.mem_append]
      exact Or.inl hl)
  · rw [instrsWf_iff_locs]
    intro l hl
    exact h l (by
      simp only [instrLocs, instrsLocs_append, List.mem_append]
      exact Or.inr hl)

theorem instrWf_kEval_elim {heap : Heap} {nl : Nat} {e : Expr}
    (h : instrWf heap nl (.kEval e)) : exprWf heap nl e := by
  intro l hl
  exact h l (by simp [instrLocs, hl])

theorem instrWf_kRepeatWhile_elim {heap : Heap} {nl : Nat}
    {c : Expr} {body : List Instr}
    (h : instrWf heap nl (.kRepeatWhile c body)) :
    exprWf heap nl c ∧ instrsWf heap nl body := by
  constructor
  · intro l hl; exact h l (by
      simp only [instrLocs, List.mem_append]; exact Or.inl hl)
  · rw [instrsWf_iff_locs]
    intro l hl; exact h l (by
      simp only [instrLocs, List.mem_append]; exact Or.inr hl)

theorem instrWf_kRepeatTest_elim {heap : Heap} {nl : Nat}
    {c : Expr} {body : List Instr}
    (h : instrWf heap nl (.kRepeatTest c body)) :
    exprWf heap nl c ∧ instrsWf heap nl body := by
  constructor
  · intro l hl; exact h l (by
      simp only [instrLocs, List.mem_append]; exact Or.inl hl)
  · rw [instrsWf_iff_locs]
    intro l hl; exact h l (by
      simp only [instrLocs, List.mem_append]; exact Or.inr hl)

theorem instrWf_kForStart_elim {heap : Heap} {nl : Nat}
    {x : «String»} {body : List Instr}
    (h : instrWf heap nl (.kForStart x body)) :
    instrsWf heap nl body := by
  rw [instrsWf_iff_locs]
  intro l hl; exact h l (by simp [instrLocs, hl])

theorem instrWf_kForBody_elim {heap : Heap} {nl : Nat}
    {x : «String»} {vs : List JSValue} {body : List Instr}
    (h : instrWf heap nl (.kForBody x vs body)) :
    (∀ l ∈ vs.flatMap locsOf, l < nl ∧ (heap l).isSome = Bool.true)
      ∧ instrsWf heap nl body := by
  constructor
  · intro l hl; exact h l (by
      simp only [instrLocs, List.mem_append]; exact Or.inl hl)
  · rw [instrsWf_iff_locs]
    intro l hl; exact h l (by
      simp only [instrLocs, List.mem_append]; exact Or.inr hl)

theorem instrWf_kRepeatWhile_intro {heap : Heap} {nl : Nat}
    {c : Expr} {body : List Instr}
    (hc : exprWf heap nl c) (hb : instrsWf heap nl body) :
    instrWf heap nl (.kRepeatWhile c body) := by
  intro l hl
  simp only [instrLocs, List.mem_append] at hl
  rcases hl with hl | hl
  · exact hc l hl
  · exact (instrsWf_iff_locs body).mp hb l hl

theorem instrWf_kRepeatTest_intro {heap : Heap} {nl : Nat}
    {c : Expr} {body : List Instr}
    (hc : exprWf heap nl c) (hb : instrsWf heap nl body) :
    instrWf heap nl (.kRepeatTest c body) := by
  intro l hl
  simp only [instrLocs, List.mem_append] at hl
  rcases hl with hl | hl
  · exact hc l hl
  · exact (instrsWf_iff_locs body).mp hb l hl

theorem instrWf_kForStart_intro {heap : Heap} {nl : Nat}
    {x : «String»} {body : List Instr}
    (hb : instrsWf heap nl body) :
    instrWf heap nl (.kForStart x body) := by
  intro l hl
  simp only [instrLocs] at hl
  exact (instrsWf_iff_locs body).mp hb l hl

theorem instrWf_kForBody_intro {heap : Heap} {nl : Nat}
    {x : «String»} {vs : List JSValue} {body : List Instr}
    (hvs : ∀ l ∈ vs.flatMap locsOf,
      l < nl ∧ (heap l).isSome = Bool.true)
    (hb : instrsWf heap nl body) :
    instrWf heap nl (.kForBody x vs body) := by
  intro l hl
  simp only [instrLocs, List.mem_append] at hl
  rcases hl with hl | hl
  · exact hvs l hl
  · exact (instrsWf_iff_locs body).mp hb l hl

theorem instrsWf_tail {heap : Heap} {nl : Nat} {i : Instr} {rest : List Instr}
    (h : instrsWf heap nl (i :: rest)) : instrsWf heap nl rest := h.2

def framesWf (heap : Heap) (nl : Nat) : List Fr → Prop
  | [] => True
  | f :: fs => instrsWf heap nl f.stmts ∧ framesWf heap nl fs

def stateOk (sigs : SigTable) (r : Ty) (m : FM) : Prop :=
  match m with
  | .frames fs heap nl =>
      fs.isEmpty = Bool.false
      ∧ heapOk heap nl fs
      ∧ (∃ ht, heapTyOk heap ht nl
          ∧ framesOk sigs (runtimeCallable heap) fs)
      ∧ machineRet sigs fs = r
      ∧ framesWf heap nl fs
  | .fdone v _ _ _ _ =>
      -- the final completion: complN payload ⊑ r, or complT
      match v with
      | .compl Bool.false pv => tmoves [typeOfV pv] r = Bool.true
      | .compl Bool.true _ => Bool.true
      | _ => False
  | .fell _ _ _ _ => False

/- Registry coverage (existence): every name the checker may call is
    answered by the registry (Get and Call are registry-backed -
    7.3.2 / 7.3.13 - and the nativeOps stub is gone); the MOP-Get
    dispatch target exists. -/
def closedRegistry (sigs : SigTable) (reg : AOReg) : Prop :=
  (∀ n _ps _ret, sigFind sigs n = some (_ps, _ret) →
      (findAO reg n).isSome = Bool.true)
  ∧ (findAO reg "OrdinaryGet").isSome = Bool.true

/- ## Registry certification

    kCall pushes the callee's compiled body with a fresh env made from
    the ACTUAL argument values. Nothing about the caller can make that
    frame well-typed, so subject reduction is relative to a registry
    certified at every argument typing that satisfies the signature. -/

/-- The certificate a registry entry carries at a given argument
    typing. -/
def certifies (sigs : SigTable) (η : HeapCallableTy) (name : «String»)
    (ps : List «String»)
    (ts : List Ty) (prog : Prog) : Prop :=
  match checkSeq sigs (sigRetTy sigs name)
      { η := η, Γ := zipTy ps ts, σ := []} (compileSteps prog) with
  | .flows fb =>
      terminal fb = Bool.true
        ∧ (fb.throws = Bool.true → complCanThrow (sigCompls sigs name) = Bool.true)
  | _ => False

theorem certifies_flows_elim {sigs : SigTable} {η : HeapCallableTy}
    {name : «String»}
    {ps : List «String»} {ts : List Ty} {prog : Prog}
    (h : certifies sigs η name ps ts prog) :
    ∃ fb, checkSeq sigs (sigRetTy sigs name)
        { η := η, Γ := zipTy ps ts, σ := []} (compileSteps prog)
        = TCResult.flows fb ∧ terminal fb = Bool.true
        ∧ (fb.throws = Bool.true
            → complCanThrow (sigCompls sigs name) = Bool.true) := by
  cases hb : checkSeq sigs (sigRetTy sigs name)
      { η := η, Γ := zipTy ps ts, σ := []} (compileSteps prog) with
  | flows fb =>
      simp only [certifies] at h
      rw [hb] at h
      exact ⟨fb, rfl, h.1, h.2⟩
  | reject s w =>
      simp only [certifies] at h
      rw [hb] at h
      exact False.elim h

def registryCertified (sigs : SigTable) (reg : AOReg) : Prop :=
  ∀ name ps prog, (name, (ps, prog)) ∈ reg →
    (∀ (heap : Heap) (nl : Nat), instrsWf heap nl (compileSteps prog)) ∧
    -- the certificate is at every PREFIX typing that the checker may
    -- pass: kCall accepts an n+1-parameter callee called with n
    -- arguments (the optional trailing parameter stays unbound), so
    -- the argument typing covers a prefix of the declared parameters.
    -- It holds at EVERY heap-callability η: the callee frame's own
    -- check runs at the caller's runtime η.
    ∀ η ts, ts.length ≤ (sigParams sigs name).length →
      leTy ts ((sigParams sigs name).take ts.length) →
      certifies sigs η name ps ts prog

/- ## The target statement (proof in progress, bottom-up):

    theorem type_safety (sigs : SigTable) (reg : AOReg)
        (hreg : registryCertified sigs reg)
        (hcover : closedRegistry sigs reg)
        (r : Ty) (m : FM) (h : stateOk sigs r m) :
        stateOk sigs r (fstep reg m)

    Preservation alone suffices: fell is ill-typed in stateOk.
    Per-arm plan (re-proofs on the flat lattice, in git history on
    the old STy at c269325): kEval_const/nat/nv, kPop, kSet,
    kPrim1_pWrapC/pThrowC, kUnwrap, kCall, kRet_bottom, kTest,
    kTestT, then the refinement family (kEval of tests — meetTy
    consumers — kIte, kMkList, kNewSlot, loops). -/

/- ## Proof layer (flat lattice): in progress. -/

/- ## Proof layer I: the flat refinement order -/

/-- Pointwise refinement of flat types: every atom below some atom. -/
def tyLe (t u : Ty) : Prop := tmoves t u = Bool.true

/- ## Proof layer I': the refinement relations, strengthened.

    Plain ∃-atom covariance admits refined EMPTY slots/bindings
    ([] ⊑ anything vacuously) - and an empty binding makes the
    refined split reject (meetTy [] T = []) while the coarse is
    terminal. Three components close exactly those holes:
      - atom covariance (∀-∃),
      - lookup EXISTENCE preservation (no refined-only unbounds),
      - coarse-nonempty → refined-nonempty (no refined bottoms). -/

/-- Slot refinement: atom covariance + no refined bottom slot
    (a nonempty coarse slot keeps a nonempty refined slot). -/
def slotLe (t' t : Ty) : Prop :=
  tyLe t' t ∧ (t ≠ [] → t' ≠ [])

/-- Pointwise refinement of type environments. -/
def envLe (Γ' Γ : TyEnv) : Prop :=
  (∀ (x : «String»), (tyLookup Γ' x).isSome = (tyLookup Γ x).isSome)
  ∧ (∀ (x : «String»), ∀ t' ∈ tyLookup Γ' x, ∃ t ∈ tyLookup Γ x, tyLe t' t)
  ∧ (∀ (x : «String»), ∀ t ∈ tyLookup Γ x, t ≠ [] →
       ∃ t' ∈ tyLookup Γ' x, t' ≠ [] ∧ tyLe t' t)

def stackLe : List Ty → List Ty → Prop
  | [], [] => True
  | t' :: σ', t :: σ => slotLe t' t ∧ stackLe σ' σ
  | _, _ => False

/- ## Decider agreement (the specialization subspace).

    The fused-predicate deciders (predDecide, total) are verdict
    functions on atoms; a REFINED atom may decide differently than
    its coarse cover (a data descriptor singleton under the any-desc
    class; a heap-callable exact object under the non-callable
    object class). The specialization induction therefore lives in
    the subspace where refined atoms have covers with the SAME
    verdicts — carried pointwise through Γ and σ, and recursively
    through completion payloads (a delivered complN singleton must
    stay coverable after kUnwrap extracts its payload). -/
def decAgree (η : HeapCallableTy) (a' a : VTy) : Prop :=
  ∀ (f : «String») (dec : VTy → Bool),
    predDecide η f = some dec → dec a' = dec a

/-- Atom coverage: refinement + verdict agreement + (for normal
    completions) payload coverage. -/
def atomCov (η : HeapCallableTy) (a' a : VTy) : Prop :=
  tmovesV a' a = Bool.true
    ∧ decAgree η a' a
    ∧ match a', a with
      | .complN p', .complN p => atomCov η p' p
      | _, _ => True

/-- Slot coverage: every refined atom covered. -/
def tyCov (η : HeapCallableTy) (t' t : Ty) : Prop :=
  ∀ a' ∈ t', ∃ a ∈ t, atomCov η a' a

/-- Pointwise stack coverage. -/
def stackCov : HeapCallableTy → List Ty → List Ty → Prop
  | _, [], [] => True
  | η, t' :: σ', t :: σ => tyCov η t' t ∧ stackCov η σ' σ
  | _, _, _ => False

/-- Environment coverage (per binding, through lookups). -/
def envCov (η : HeapCallableTy) (Γ' Γ : TyEnv) : Prop :=
  ∀ (x : «String») (t' : Ty), tyLookup Γ' x = some t' →
    ∃ t, tyLookup Γ x = some t ∧ tyCov η t' t

def worldLe (w' w : World) : Prop :=
  w'.η = w.η ∧ envLe w'.Γ w.Γ ∧ stackLe w'.σ w.σ
    ∧ envCov w'.η w'.Γ w.Γ ∧ stackCov w'.η w'.σ w.σ

/-- Subtyping is a preorder on the flat lattice (the atom grid is
    essentially discrete: identity, singleton-into-class, and
    desc-into-anyValue-desc). -/
theorem tmovesV_refl : ∀ (a : VTy), tmovesV a a = Bool.true
  | .complN p => tmovesV_refl p
  | .complT => rfl
  | .anyValue c => by simp [tmovesV]
  | .isValue v => by simp [tmovesV]
  | .desc fs => decide_eq_true (rfl : fs = fs)
  | .notPresent => rfl
termination_by a => sizeOf a
decreasing_by all_goals simp_wf <;> omega

theorem tmoves_refl (t : Ty) : tyLe t t := by
  unfold tyLe tmoves
  simp only [List.all_eq_true]
  intro a ha
  exact List.any_eq_true.mpr ⟨a, ha, tmovesV_refl a⟩

theorem tmovesV_trans {a b c : VTy}
    (h₁ : tmovesV a b = Bool.true) (h₂ : tmovesV b c = Bool.true) :
    tmovesV a c = Bool.true := by
  induction a generalizing b c with
  | complN p ih =>
      cases b with
      | complN q =>
          cases c with
          | complN s => simp only [tmovesV]; exact ih h₁ h₂
          | complT | anyValue _ | isValue _ | desc _ | notPresent => simp [tmovesV] at h₂
      | complT | anyValue _ | isValue _ | desc _ | notPresent => simp [tmovesV] at h₁
  | complT =>
      cases b with
      | complT =>
          cases c with
          | complT => rfl
          | complN _ | anyValue _ | isValue _ | desc _ | notPresent => simp [tmovesV] at h₂
      | complN _ | anyValue _ | isValue _ | desc _ | notPresent => simp [tmovesV] at h₁
  | anyValue ca =>
      cases b with
      | anyValue cb =>
          cases c with
          | anyValue cc =>
              simp only [tmovesV] at h₁ h₂ ⊢
              exact decide_eq_true ((of_decide_eq_true h₁).trans (of_decide_eq_true h₂))
          | complN _ | complT | isValue _ | desc _ | notPresent => simp [tmovesV] at h₂
      | complN _ | complT | isValue _ | desc _ | notPresent => simp [tmovesV] at h₁
  | isValue va =>
      cases b with
      | isValue vb =>
          cases c with
          | isValue vc =>
              simp only [tmovesV, beq_iff_eq] at h₁ h₂ ⊢
              exact h₁.trans h₂
          | anyValue cc =>
              simp only [tmovesV, tagOf, decide_eq_true, beq_iff_eq] at h₁ h₂ ⊢
              rw [h₁, h₂]
          | complN _ | complT | desc _ | notPresent => simp [tmovesV] at h₂
      | anyValue cb =>
          cases c with
          | anyValue cc =>
              cases va <;> cases cb <;> cases cc <;>
                simp_all [tmovesV, tagOf, decide_eq_true]
          | complN _ | complT | isValue _ | desc _ | notPresent =>
              simp [tmovesV] at h₂
      | complN _ | complT | desc _ | notPresent => simp [tmovesV] at h₁
  | desc fa =>
      cases b with
      | desc fb =>
          cases c with
          | desc fc =>
              simp only [tmovesV] at h₁ h₂ ⊢
              exact decide_eq_true ((of_decide_eq_true h₁).trans (of_decide_eq_true h₂))
          | anyValue cc =>
              cases cc with
              | desc => simpa only [tmovesV] using h₁
              | undef | null | bool | num | str | obj | list =>
                  exact absurd h₂ (by simp [tmovesV])
          | complN _ | complT | isValue _ | notPresent =>
              simp only [tmovesV] at h₂
              exact Bool.noConfusion h₂
      | anyValue cb =>
          cases cb with
          | desc =>
              cases c with
              | anyValue cc =>
                  cases cc with
                  | desc => simpa only [tmovesV] using h₂
                  | undef | null | bool | num | str | obj | list =>
                      exact absurd h₂ (by simp [tmovesV])
              | complN _ | complT | isValue _ | desc _ | notPresent =>
                  simp only [tmovesV] at h₂
                  exact Bool.noConfusion h₂
          | undef | null | bool | num | str | obj | list =>
              exact absurd h₁ (by simp [tmovesV])
      | complN _ | complT | isValue _ | notPresent =>
          simp only [tmovesV] at h₁
          exact Bool.noConfusion h₁
  | notPresent =>
      cases b with
      | notPresent =>
          cases c with
          | notPresent => rfl
          | complN _ | complT | anyValue _ | isValue _ | desc _ => simp [tmovesV] at h₂
      | complN _ | complT | anyValue _ | isValue _ | desc _ => simp [tmovesV] at h₁

theorem tmoves_trans {t u v : Ty}
    (h₁ : tyLe t u) (h₂ : tyLe u v) : tyLe t v := by
  unfold tyLe tmoves at h₁ h₂ ⊢
  simp only [List.all_eq_true, List.any_eq_true] at *
  intro a ha
  obtain ⟨b, hb, hab⟩ := h₁ a ha
  obtain ⟨c, hc, hbc⟩ := h₂ b hb
  exact ⟨c, hc, tmovesV_trans hab hbc⟩

theorem tyLe_of_eq {t u : Ty} (h : t = u) : tyLe t u := by
  rw [h]; exact tmoves_refl u

/- ## Proof layer I'': plumbing for the strengthened relations -/

theorem envLe_refl (Γ : TyEnv) : envLe Γ Γ := by
  refine ⟨fun _ => rfl, fun _ t' ht' => ⟨t', ht', tyLe_of_eq rfl⟩, ?_⟩
  intro x t ht hne
  exact ⟨t, ht, hne, tyLe_of_eq rfl⟩

theorem stackLe_refl : ∀ (σ : List Ty), stackLe σ σ
  | [] => trivial
  | t :: σ => ⟨⟨tmoves_refl _, fun h => h⟩, stackLe_refl σ⟩

/-- Agreement and coverage are reflexive. -/
theorem decAgree_refl (η : HeapCallableTy) (a : VTy) : decAgree η a a := by
  intro f dec hd; rfl

theorem atomCov_refl : ∀ (η : HeapCallableTy) (a : VTy), atomCov η a a
  | η, .complN p => by
      simp only [atomCov]
      exact ⟨tmovesV_refl _, decAgree_refl _ _, atomCov_refl η p⟩
  | η, .complT => by
      simp only [atomCov]
      exact ⟨tmovesV_refl _, decAgree_refl _ _, True.intro⟩
  | η, .anyValue _ => by
      simp only [atomCov]
      exact ⟨tmovesV_refl _, decAgree_refl _ _, True.intro⟩
  | η, .isValue _ => by
      simp only [atomCov]
      exact ⟨tmovesV_refl _, decAgree_refl _ _, True.intro⟩
  | η, .desc _ => by
      simp only [atomCov]
      exact ⟨tmovesV_refl _, decAgree_refl _ _, True.intro⟩
  | η, .notPresent => by
      simp only [atomCov]
      exact ⟨tmovesV_refl _, decAgree_refl _ _, True.intro⟩

theorem tyCov_refl (η : HeapCallableTy) (t : Ty) : tyCov η t t := by
  intro a ha
  exact ⟨a, ha, atomCov_refl η a⟩

theorem stackCov_refl : ∀ (η : HeapCallableTy) (σ : List Ty), stackCov η σ σ
  | _, [] => True.intro
  | η, t :: σ => ⟨tyCov_refl η t, stackCov_refl η σ⟩

theorem envCov_refl (η : HeapCallableTy) (Γ : TyEnv) : envCov η Γ Γ := by
  intro x t ht
  exact ⟨t, ht, tyCov_refl η t⟩

theorem worldLe_refl (w : World) : worldLe w w :=
  ⟨rfl, envLe_refl w.Γ, stackLe_refl w.σ,
    envCov_refl w.η w.Γ, stackCov_refl w.η w.σ⟩

/-- Coverage through extended environments. -/
theorem envCov_cons {η : HeapCallableTy} {Γ' Γ : TyEnv} {x : «String»}
    {t' t : Ty} (hΓ : envCov η Γ' Γ) (h : tyCov η t' t) :
    envCov η ((x, t') :: Γ') ((x, t) :: Γ) := by
  intro y s' hs'
  by_cases hxy : x = y
  · subst hxy
    simp only [tyLookup, beq_self_eq_true, if_true, Option.some.injEq] at hs'
    subst hs'
    exact ⟨t, by simp [tyLookup], h⟩
  · simp only [tyLookup, if_neg (fun he => hxy (beq_iff_eq.mp he))] at hs'
    obtain ⟨s, hs, hcs⟩ := hΓ y s' hs'
    exact ⟨s, by
      simp only [tyLookup, if_neg (fun he => hxy (beq_iff_eq.mp he))]
      exact hs, hcs⟩

theorem tyCov_cons {η : HeapCallableTy} {a' a : Ty} {σ' σ : List Ty}
    (h : stackCov η (a' :: σ') (a :: σ)) :
    tyCov η a' a ∧ stackCov η σ' σ := h

theorem stackCov_cons_intro {η : HeapCallableTy} {a' a : Ty} {σ' σ : List Ty}
    (h : tyCov η a' a) (hrest : stackCov η σ' σ) :
    stackCov η (a' :: σ') (a :: σ) := ⟨h, hrest⟩

theorem stackCov_drop : ∀ {σ' σ : List Ty} (n : Nat) {η : HeapCallableTy},
    stackCov η σ' σ → stackCov η (σ'.drop n) (σ.drop n)
  | _, _, 0, _, h => h
  | [], [], _ + 1, _, _ => True.intro
  | a' :: σ', a :: σ, n + 1, η, h => by
      show stackCov η (List.drop n σ') (List.drop n σ)
      exact stackCov_drop n h.2
termination_by σ' => sizeOf σ'
decreasing_by all_goals simp_wf <;> omega

/-- Coverage of a singleton below a covered atom. -/
theorem atomCov_single {η : HeapCallableTy} {a' a : VTy}
    (h : atomCov η a' a) :
    tyCov η [a'] [a] := by
  intro b hb
  simp only [List.mem_singleton] at hb
  subst hb
  exact ⟨a, by simp, h⟩

/-- The pure atoms (no descriptor class, no non-callable object
    class): anything below a pure atom agrees with it on every
    decider the fused-test stratum consults. -/
def pureAtom (a : VTy) : Prop :=
  match a with
  | .anyValue .desc => False
  | .anyValue (.obj Bool.false) => False
  | _ => True

def pureAtomDeep : VTy → Prop
  | .anyValue .desc | .anyValue (.obj Bool.false) => False
  | .complN p => pureAtomDeep p
  | _ => True

theorem pureAtomDeep_shallow {a : VTy} (h : pureAtomDeep a) : pureAtom a := by
  cases a with
  | complN p => trivial
  | anyValue c =>
      cases c with
      | desc => exact h
      | obj b => cases b <;> exact h
      | undef | null | bool | num | str | list => trivial
  | complT | isValue _ | desc _ | notPresent => trivial

theorem decAgree_complN {η : HeapCallableTy} {q p : VTy} :
    decAgree η (.complN q) (.complN p) := by
  intro f dec hd
  unfold predDecide at hd
  split at hd
  all_goals first
    | (injection hd with h; subst h; rfl)
    | cases hd

theorem decAgree_of_pure_cover {η : HeapCallableTy} {a' a : VTy}
    (h : tmovesV a' a = Bool.true) (hp : pureAtom a) : decAgree η a' a := by
  intro f dec hd
  unfold predDecide at hd
  split at hd
  · injection hd with hdec
    subst hdec
    cases a' with
    | desc fs' =>
        cases a with
        | desc fs => simp_all [tmovesV]
        | anyValue c =>
            cases c <;> simp_all [tmovesV, pureAtom, decide_eq_true_eq]
        | complN q | complT | isValue _ | notPresent => simp_all [tmovesV]
    | anyValue c' =>
        cases a with
        | anyValue c =>
            cases c' <;> cases c <;>
              simp_all [tmovesV, pureAtom, decide_eq_true_eq]
        | complN q | complT | isValue _ | desc _ | notPresent =>
            simp_all [tmovesV]
    | complN q =>
        cases a with
        | complN p => simp_all [tmovesV]
        | complT | anyValue _ | isValue _ | desc _ | notPresent =>
            simp_all [tmovesV]
    | complT =>
        cases a with
        | complT => simp_all [tmovesV]
        | complN _ | anyValue _ | isValue _ | desc _ | notPresent =>
            simp_all [tmovesV]
    | isValue v =>
        cases a with
        | isValue w => simp_all [tmovesV]
        | anyValue c =>
            cases v <;> cases c <;>
              simp_all [tmovesV, tagOf, pureAtom, decide_eq_true_eq,
                beq_iff_eq]
        | complN _ | complT | desc _ | notPresent => simp_all [tmovesV]
    | notPresent =>
        cases a with
        | notPresent => simp_all [tmovesV]
        | complN _ | complT | anyValue _ | isValue _ | desc _ =>
            simp_all [tmovesV]
  · injection hd with hdec
    subst hdec
    cases a' with
    | desc fs' =>
        cases a with
        | desc fs => simp_all [tmovesV]
        | anyValue c =>
            cases c <;> simp_all [tmovesV, pureAtom, decide_eq_true_eq]
        | complN q | complT | isValue _ | notPresent => simp_all [tmovesV]
    | anyValue c' =>
        cases a with
        | anyValue c =>
            cases c' <;> cases c <;>
              simp_all [tmovesV, pureAtom, decide_eq_true_eq]
        | complN q | complT | isValue _ | desc _ | notPresent =>
            simp_all [tmovesV]
    | complN q =>
        cases a with
        | complN p => simp_all [tmovesV]
        | complT | anyValue _ | isValue _ | desc _ | notPresent =>
            simp_all [tmovesV]
    | complT =>
        cases a with
        | complT => simp_all [tmovesV]
        | complN _ | anyValue _ | isValue _ | desc _ | notPresent =>
            simp_all [tmovesV]
    | isValue v =>
        cases a with
        | isValue w => simp_all [tmovesV]
        | anyValue c =>
            cases v <;> cases c <;>
              simp_all [tmovesV, tagOf, pureAtom, decide_eq_true_eq,
                beq_iff_eq]
        | complN _ | complT | desc _ | notPresent => simp_all [tmovesV]
    | notPresent =>
        cases a with
        | notPresent => simp_all [tmovesV]
        | complN _ | complT | anyValue _ | isValue _ | desc _ =>
            simp_all [tmovesV]
  · injection hd with hdec
    subst hdec
    cases a' with
    | desc fs' =>
        cases a with
        | desc fs => simp_all [tmovesV, isCallableAtom]
        | anyValue c =>
            cases c <;> simp_all [tmovesV, pureAtom, decide_eq_true_eq,
              isCallableAtom]
        | complN q | complT | isValue _ | notPresent =>
            simp_all [tmovesV, isCallableAtom]
    | anyValue c' =>
        cases a with
        | anyValue c =>
            cases c' <;> cases c <;>
              simp_all [tmovesV, pureAtom, decide_eq_true_eq,
                isCallableAtom]
        | complN q | complT | isValue _ | desc _ | notPresent =>
            simp_all [tmovesV, isCallableAtom]
    | complN q =>
        cases a with
        | complN p => simp_all [tmovesV, isCallableAtom]
        | complT | anyValue _ | isValue _ | desc _ | notPresent =>
            simp_all [tmovesV, isCallableAtom]
    | complT =>
        cases a with
        | complT => simp_all [tmovesV, isCallableAtom]
        | complN _ | anyValue _ | isValue _ | desc _ | notPresent =>
            simp_all [tmovesV, isCallableAtom]
    | isValue v =>
        cases a with
        | isValue w => simp_all [tmovesV, isCallableAtom, beq_iff_eq]
        | anyValue c =>
            cases v <;> cases c <;>
              simp_all [tmovesV, tagOf, pureAtom, isCallableAtom,
                decide_eq_true_eq, beq_iff_eq]
        | complN _ | complT | desc _ | notPresent =>
            simp_all [tmovesV, isCallableAtom]
    | notPresent =>
        cases a with
        | notPresent => simp_all [tmovesV, isCallableAtom]
        | complN _ | complT | anyValue _ | isValue _ | desc _ =>
            simp_all [tmovesV, isCallableAtom]
  · cases hd

theorem atomCov_of_pure_cover (η : HeapCallableTy) :
    ∀ {a' a : VTy},
    tmovesV a' a = Bool.true → pureAtomDeep a → atomCov η a' a := by
  intro a' a h hp
  cases a' with
  | complN q =>
      cases a with
      | complN p =>
          simp only [atomCov]
          exact ⟨h, decAgree_complN, atomCov_of_pure_cover η h hp⟩
      | complT | anyValue _ | isValue _ | desc _ | notPresent =>
          simp only [atomCov]
          exact ⟨h, decAgree_of_pure_cover h (pureAtomDeep_shallow hp),
            True.intro⟩
  | complT | anyValue _ | isValue _ | desc _ | notPresent =>
      simp only [atomCov]
      exact ⟨h, decAgree_of_pure_cover h (pureAtomDeep_shallow hp),
        True.intro⟩

/-- Projections and the complN intro for atomCov (the definition is a
    recursive match, so access goes through these). -/
theorem atomCov_tmoves {η : HeapCallableTy} {a' a : VTy}
    (h : atomCov η a' a) : tmovesV a' a = Bool.true := by
  cases a' with
  | complN q =>
      cases a with
      | complN r => simp only [atomCov] at h; exact h.1
      | complT | anyValue _ | isValue _ | desc _ | notPresent =>
          simp only [atomCov] at h; exact h.1
  | complT | anyValue _ | isValue _ | desc _ | notPresent =>
      simp only [atomCov] at h; exact h.1

theorem atomCov_dec {η : HeapCallableTy} {a' a : VTy}
    (h : atomCov η a' a) : decAgree η a' a := by
  cases a' with
  | complN q =>
      cases a with
      | complN r => simp only [atomCov] at h; exact h.2.1
      | complT | anyValue _ | isValue _ | desc _ | notPresent =>
          simp only [atomCov] at h; exact h.2.1
  | complT | anyValue _ | isValue _ | desc _ | notPresent =>
      simp only [atomCov] at h; exact h.2.1

theorem atomCov_pay {η : HeapCallableTy} {q r : VTy}
    (h : atomCov η (.complN q) (.complN r)) : atomCov η q r := by
  simp only [atomCov] at h
  exact h.2.2

/-- complN-wrapping preserves coverage. -/
theorem atomCov_complN_of {η : HeapCallableTy} {p' p : VTy}
    (h : atomCov η p' p) : atomCov η (.complN p') (.complN p) := by
  have h1 : tmovesV p' p = Bool.true := atomCov_tmoves h
  show tmovesV (.complN p') (.complN p) = Bool.true
    ∧ decAgree η (.complN p') (.complN p) ∧ _
  exact ⟨by simpa only [tmovesV] using h1, decAgree_complN, h⟩

/-- complNormals preserves coverage (through the complN payloads). -/
theorem tyCov_complNormals {η : HeapCallableTy} {t' t : Ty}
    (h : tyCov η t' t) : tyCov η (complNormals t') (complNormals t) := by
  intro m' hm'
  simp only [complNormals, List.mem_filterMap] at hm'
  obtain ⟨a', ha', hma'⟩ := hm'
  obtain ⟨a, ha, hac⟩ := h a' ha'
  have h1 := atomCov_tmoves hac
  cases a' with
  | complN p' =>
      have hm2 : some (VTy.complN p') = some m' := hma'
      injection hm2 with hma'
      subst hma'
      cases a with
      | complN p =>
          refine ⟨.complN p, by
            simp only [complNormals, List.mem_filterMap]
            exact ⟨.complN p, ha, rfl⟩,
            atomCov_complN_of (atomCov_pay hac)⟩
      | complT | anyValue _ | isValue _ | desc _ | notPresent =>
          exact absurd h1 (by simp [tmovesV])
  | complT | anyValue _ | isValue _ | desc _ | notPresent =>
      have hm2 : (none : Option VTy) = some m' := hma'
      contradiction

theorem envLe_cons {Γ' Γ : TyEnv} {x : «String»} {t' t : Ty}
    (hΓ : envLe Γ' Γ) (hslot : slotLe t' t) :
    envLe ((x, t') :: Γ') ((x, t) :: Γ) := by
  obtain ⟨hex, hcov, hne⟩ := hΓ
  refine ⟨?_, ?_, ?_⟩
  · intro y
    by_cases h : x = y
    · subst h
      simp [tyLookup]
    · simp only [tyLookup, if_neg (fun he => h (beq_iff_eq.mp he))]
      exact hex y
  · intro y s' hs'
    by_cases h : x = y
    · subst h
      simp only [tyLookup, beq_self_eq_true, if_true, Option.mem_some,
        List.mem_singleton] at hs'
      subst hs'
      simp only [tyLookup, beq_self_eq_true, if_true, Option.mem_some,
        List.mem_singleton]
      exact ⟨t, rfl, hslot.1⟩
    · simp only [tyLookup, if_neg (fun he => h (beq_iff_eq.mp he))] at hs'
      obtain ⟨s, hs, hle⟩ := hcov y s' hs'
      refine ⟨s, ?_, hle⟩
      simp only [tyLookup, if_neg (fun he => h (beq_iff_eq.mp he))]
      exact hs
  · intro y s hs hne2
    by_cases h : x = y
    · subst h
      simp only [tyLookup, beq_self_eq_true, if_true, Option.mem_some,
        List.mem_singleton] at hs
      refine ⟨t', by simp [tyLookup], hslot.2 (by rw [hs]; exact hne2),
        by rw [← hs]; exact hslot.1⟩
    · simp only [tyLookup, if_neg (fun he => h (beq_iff_eq.mp he))] at hs
      obtain ⟨w, hw, hne_w, hle_w⟩ := hne y s hs hne2
      refine ⟨w, ?_, hne_w, hle_w⟩
      simp only [tyLookup, if_neg (fun he => h (beq_iff_eq.mp he))]
      exact hw

theorem stackLe_cons {a' a : Ty} {σ' σ : List Ty}
    (h : stackLe (a' :: σ') (a :: σ)) : slotLe a' a ∧ stackLe σ' σ := h

theorem stackLe_cons_intro {a' a : Ty} {σ' σ : List Ty}
    (hslot : slotLe a' a) (h : stackLe σ' σ) : stackLe (a' :: σ') (a :: σ) :=
  ⟨hslot, h⟩

theorem envLe_lookup_cov {Γ' Γ : TyEnv} (h : envLe Γ' Γ) {x : «String»}
    {t : Ty} (ht : tyLookup Γ x = some t) (hne : t ≠ []) :
    ∃ t', tyLookup Γ' x = some t' ∧ tyLe t' t := by
  obtain ⟨-, -, hne3⟩ := h
  obtain ⟨t', ht', -, hle⟩ := hne3 x t ht hne
  exact ⟨t', ht', hle⟩


/- ## Proof layer IX: covariance of the expression summary -/

def slotsLe : List Ty → List Ty → Prop
  | [], [] => True
  | t :: ts, u :: us => slotLe t u ∧ slotsLe ts us
  | _, _ => False

theorem slotLe_refl (t : Ty) : slotLe t t :=
  ⟨tmoves_refl t, fun h => h⟩

theorem slotLe_tyLe {t' t : Ty} (h : slotLe t' t) : tyLe t' t := h.1

/-- The atom-cover form of tyLe. -/
theorem tyLe_cov_atoms {t' t : Ty} (h : tyLe t' t) :
    ∀ a' ∈ t', ∃ a ∈ t, tmovesV a' a = Bool.true := by
  unfold tyLe tmoves at h
  simp only [List.all_eq_true, List.any_eq_true] at h
  exact h

/-- A complN atom only covers complN atoms. -/
theorem tmovesV_complN_inv {p : VTy} {b : VTy}
    (h : tmovesV (.complN p) b = Bool.true) : ∃ q, b = .complN q := by
  cases b with
  | complN q => exact ⟨q, rfl⟩
  | complT | anyValue _ | isValue _ | desc _ | notPresent =>
      simp [tmovesV] at h

/-- Under complN, coverage is payload coverage. -/
theorem tmovesV_complN {p q : VTy} :
    tmovesV (.complN p) (.complN q) = tmovesV p q := rfl

/-- A bare atom never covers a completion atom. -/
theorem isBareVTy_of_cover {a' a : VTy}
    (hb : isBareVTy a = Bool.true) (h : tmovesV a' a = Bool.true) :
    isBareVTy a' = Bool.true := by
  cases a with
  | complN p => simp [isBareVTy] at hb
  | complT => simp [isBareVTy] at hb
  | anyValue c =>
      cases a' with
      | complN p => simp [tmovesV] at h
      | complT => simp [tmovesV] at h
      | anyValue c' | isValue _ | desc _ | notPresent => rfl
  | isValue v =>
      cases a' with
      | complN p => simp [tmovesV] at h
      | complT => simp [tmovesV] at h
      | anyValue c' | isValue _ | desc _ | notPresent => rfl
  | desc fs =>
      cases a' with
      | complN p => simp [tmovesV] at h
      | complT => simp [tmovesV] at h
      | anyValue c' =>
          cases c' with
          | desc => rfl
          | undef | null | bool | num | str | obj | list => simp [tmovesV] at h
      | isValue _ | desc _ | notPresent => rfl
  | notPresent =>
      cases a' with
      | complN p | complT => simp [tmovesV] at h
      | anyValue c' | isValue _ | desc _ | notPresent => rfl

theorem payloadOf_pure : ∀ (t : Ty) (ps : Ty), payloadOf t = some ps →
    ∀ a ∈ t, ∃ p, a = .complN p := by
  intro t
  induction t with
  | nil => intro ps hp a ha; cases ha
  | cons b rest ih =>
      intro ps hp a ha
      cases b with
      | complN p =>
          cases rest with
          | nil =>
              simp only [payloadOf] at hp
              match List.mem_cons.mp ha with
              | Or.inl he => exact ⟨p, he⟩
              | Or.inr hr => cases hr
          | cons c rest' =>
              simp only [payloadOf] at hp
              cases hrest : payloadOf (c :: rest') with
              | none => rw [hrest] at hp; simp at hp
              | some rs =>
                  rw [hrest] at hp
                  simp only [Option.some.injEq] at hp
                  match List.mem_cons.mp ha with
                  | Or.inl he => exact ⟨p, he⟩
                  | Or.inr hr => exact ih rs hrest a hr
      | complT | anyValue _ | isValue _ | desc _ | notPresent =>
          simp only [payloadOf] at hp; simp at hp

theorem payloadsOf_ne {t : Ty} (hne : t ≠ [])
    (hpure : ∀ a ∈ t, ∃ p, a = .complN p) : payloadsOf t ≠ [] := by
  match t, hne, hpure with
  | a :: rest, _, hpure =>
      obtain ⟨p, hp⟩ := hpure a (List.mem_cons_self ..)
      subst hp
      simp [payloadsOf]

theorem payloadOf_eq : ∀ (t : Ty), (∀ a ∈ t, ∃ p, a = .complN p) →
    t ≠ [] → payloadOf t = some (payloadsOf t) := by
  intro t
  induction t with
  | nil => intro _ hne; exact absurd rfl hne
  | cons a rest ih =>
      intro hpure hne
      obtain ⟨p, hp⟩ := hpure a (List.mem_cons_self ..)
      subst hp
      cases rest with
      | nil => simp [payloadOf, payloadsOf]
      | cons b rest' =>
          have hrestne : b :: rest' ≠ [] := fun hc => by cases hc
          have hpurerest : ∀ x ∈ b :: rest', ∃ p, x = .complN p :=
            fun x hx => hpure x (List.mem_cons_of_mem _ hx)
          simp only [payloadOf]
          rw [ih hpurerest hrestne]
          simp [payloadsOf]

theorem payloadsOf_cov {t' t : Ty} (hcov : ∀ a' ∈ t', ∃ a ∈ t,
    tmovesV a' a = Bool.true) : ∀ p' ∈ payloadsOf t', ∃ p ∈ payloadsOf t,
    tmovesV p' p = Bool.true := by
  intro p' hp'
  simp only [payloadsOf, List.mem_flatMap] at hp'
  obtain ⟨a', ha', hmem'⟩ := hp'
  obtain ⟨a, ha, haa⟩ := hcov a' ha'
  cases a with
  | complN q =>
      refine ⟨q, ?_, ?_⟩
      · simp only [payloadsOf, List.mem_flatMap]
        exact ⟨.complN q, ha, by simp⟩
      · cases a' with
        | complN r =>
            have heq : p' = r := by simpa using hmem'
            rw [← tmovesV_complN, heq]
            exact haa
        | complT | anyValue _ | isValue _ | desc _ | notPresent =>
            simp [tmovesV] at haa
  | complT | anyValue _ | isValue _ | desc _ | notPresent =>
      cases a' with
      | complN r => simp [tmovesV] at haa
      | complT | anyValue _ | isValue _ | desc _ | notPresent =>
          have hnil : p' ∈ ([] : Ty) := hmem'
          exact absurd hnil (by simp)

/-- payloadOf is covariant on pure slots. -/
theorem payloadOf_cov {t' t : Ty} (h : slotLe t' t) {ps : Ty}
    (hp : payloadOf t = some ps) : ∃ ps', payloadOf t' = some ps'
      ∧ slotLe ps' ps := by
  have hpure : ∀ a ∈ t, ∃ p, a = .complN p :=
    payloadOf_pure t ps hp
  have hne : t ≠ [] := by
    intro hc
    subst hc
    simp [payloadOf] at hp
  rw [payloadOf_eq t hpure hne] at hp
  simp only [Option.some.injEq] at hp
  subst hp
  have hne' : t' ≠ [] := fun hc => h.2 hne hc
  have hpure' : ∀ a' ∈ t', ∃ p, a' = .complN p := by
    intro a' ha'
    obtain ⟨a, ha, haa⟩ := tyLe_cov_atoms h.1 a' ha'
    obtain ⟨q, hq⟩ := hpure a ha
    rw [hq] at haa
    cases a' with
    | complN p' => exact ⟨p', rfl⟩
    | complT | anyValue _ | isValue _ | desc _ | notPresent =>
        simp [tmovesV] at haa
  refine ⟨payloadsOf t', payloadOf_eq t' hpure' hne', ?_, ?_⟩
  · unfold tyLe tmoves
    simp only [List.all_eq_true, List.any_eq_true]
    exact payloadsOf_cov (fun a' ha' => tyLe_cov_atoms h.1 a' ha')
  · intro _
    exact payloadsOf_ne hne' hpure'


/-- Whole-slot lookup covariance: existence + cover + no refined bottom. -/
theorem envLe_lookup_cov_full {Γ' Γ : TyEnv} (h : envLe Γ' Γ) {x : «String»}
    {t : Ty} (ht : tyLookup Γ x = some t) :
    ∃ t', tyLookup Γ' x = some t' ∧ slotLe t' t := by
  obtain ⟨hex, hcov, hne⟩ := h
  have h1 : (tyLookup Γ' x).isSome = Bool.true := by
    rw [hex, ht]; rfl
  cases hl' : tyLookup Γ' x with
  | none => rw [hl'] at h1; simp at h1
  | some t' =>
      refine ⟨t', rfl, ?_, ?_⟩
      · obtain ⟨t0, ht0, hle0⟩ := hcov x t' (by rw [hl']; exact Option.mem_some_self t')
        rw [ht] at ht0
        have heq0 : t = t0 := by simpa using ht0
        rw [heq0]
        exact hle0
      · intro hne0
        obtain ⟨t1, ht1, hne1, _⟩ := hne x t (by rw [ht]; exact Option.mem_some_self t) hne0
        rw [hl'] at ht1
        have heq1 : t' = t1 := by simpa using ht1
        rw [heq1]
        exact hne1

theorem bareOf_pure : ∀ (t bs : Ty), bareOf t = some bs →
    ∀ a ∈ t, isBareVTy a = Bool.true := by
  intro t
  induction t with
  | nil => intro bs hb a ha; cases ha
  | cons b rest ih =>
      intro bs hb a ha
      simp only [bareOf] at hb
      cases hib : isBareVTy b with
      | false => rw [hib] at hb; simp at hb
      | true =>
          rw [hib] at hb
          simp only [Option.map_eq_some_iff] at hb
          obtain ⟨bs', hbs', heq⟩ := hb
          match List.mem_cons.mp ha with
          | Or.inl he => rw [he]; exact hib
          | Or.inr hr => exact ih bs' hbs' a hr

theorem bareOf_eq_self {t : Ty} (hpure : ∀ a ∈ t, isBareVTy a = Bool.true) :
    bareOf t = some t := by
  induction t with
  | nil => rfl
  | cons a rest ih =>
      have hrest : ∀ x ∈ rest, isBareVTy x = Bool.true :=
        fun x hx => hpure x (List.mem_cons_of_mem _ hx)
      simp only [bareOf, hpure a (List.mem_cons_self ..), ih hrest]
      rfl

theorem bareOf_cov {t' t : Ty} (h : slotLe t' t) {bs : Ty}
    (hb : bareOf t = some bs) : bareOf t' = some t' ∧ slotLe t' bs := by
  have hpure := bareOf_pure t bs hb
  have hbs : t = bs := by
    have := bareOf_eq_self (t := t) hpure
    rw [this, Option.some.injEq] at hb
    exact hb
  subst hbs
  have hpure' : ∀ a' ∈ t', isBareVTy a' = Bool.true := by
    intro a' ha'
    obtain ⟨a, ha, haa⟩ := tyLe_cov_atoms h.1 a' ha'
    exact isBareVTy_of_cover (hpure a ha) haa
  refine ⟨bareOf_eq_self hpure', h⟩

theorem complN_map_cov {t' t : Ty} (h : slotLe t' t) :
    slotLe (t'.map VTy.complN) (t.map VTy.complN) := by
  refine ⟨?_, ?_⟩
  · unfold tyLe tmoves
    simp only [List.all_eq_true, List.any_eq_true, List.mem_map]
    intro a ha
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b, hb, hbb⟩ := tyLe_cov_atoms h.1 a' ha'
    exact ⟨.complN b, by simp [hb], by
      rw [tmovesV_complN]; exact hbb⟩
  · intro hne hnil
    exact absurd (List.map_eq_nil_iff.mp hnil) (h.2 (fun hc => hne (by rw [hc]; rfl)))

/-- The three possible isObject verdicts are all below [.anyValue .bool]. -/
theorem isObject_result_le (r : Ty)
    (h : r = [.isValue (.boolean Bool.true)]
      ∨ r = [.isValue (.boolean Bool.false)] ∨ r = [.anyValue .bool]) :
    tyLe r [.anyValue .bool] := by
  cases h with
  | inl h => subst h; unfold tyLe tmoves; simp [tmovesV, tagOf]
  | inr h =>
      cases h with
      | inl h => subst h; unfold tyLe tmoves; simp [tmovesV, tagOf]
      | inr h => subst h; exact tmoves_refl _

/- removeTy lemmas for the punctured difference (removeAtom).

    The boolean puncture only fires when T carries a boolean
    SINGLETON; when it does not (every corpus split site tests
    object/string/undefined/... types), removeTy is the plain filter
    and the old reasoning applies via removeTy_noBool. -/

theorem isBoolSing_inv {c : VTy} {b : Bool}
    (h : isBoolSing b c = Bool.true) : c = .isValue (.boolean b) := by
  cases c with
  | isValue v =>
      cases v with
      | boolean b2 => cases b2 <;> simp only [isBoolSing] at h <;> simp_all
      | undefined | null | number _ | str _ | obj _
      | listV _ | descV _ | compl _ _ => simp [isBoolSing] at h
  | complN p | complT | anyValue _ | desc _ | notPresent =>
      simp [isBoolSing] at h
theorem isBoolClass_inv {c : VTy}
    (h : isBoolClass c = Bool.true) : c = .anyValue .bool := by
  cases c with
  | anyValue c2 =>
      cases c2 with
      | bool => rfl
      | undef | null | num | str | obj | list | desc => simp [isBoolClass] at h
  | complN p | complT | isValue _ | desc _ | notPresent =>
      simp [isBoolClass] at h
theorem isBoolClass_reduce :
    isBoolClass (.anyValue .bool) = Bool.true := rfl

theorem T_has_sing (T : Ty) (b : Bool)
    (h : T.any (isBoolSing b) = Bool.true) :
    (.isValue (.boolean b)) ∈ T := by
  obtain ⟨c, hc, hcc⟩ := List.any_eq_true.mp h
  exact (isBoolSing_inv hcc) ▸ hc

theorem removeAtom_noBool {a : VTy} {T : Ty}
    (hnb : ∀ b ∈ T, (match b with
      | .isValue (.boolean _) => False | _ => True)) :
    removeAtom a T
      = (if T.any (fun b => tmovesV a b) then ([] : Ty) else [a]) := by
  unfold removeAtom
  cases hf : T.any (fun b => tmovesV a b) with
  | true => rfl
  | false =>
      cases hbl : isBoolClass a with
      | true =>
          have h1 : T.any (isBoolSing Bool.true) = Bool.false := by
            cases h : T.any (isBoolSing Bool.true) with
            | true =>
                exfalso
                obtain ⟨c, hc, hcc⟩ := List.any_eq_true.mp h
                have hmem : (.isValue (.boolean Bool.true)) ∈ T :=
                  (isBoolSing_inv hcc) ▸ hc
                exact hnb _ hmem
            | false => rfl
          have h2 : T.any (isBoolSing Bool.false) = Bool.false := by
            cases h : T.any (isBoolSing Bool.false) with
            | true =>
                exfalso
                obtain ⟨c, hc, hcc⟩ := List.any_eq_true.mp h
                have hmem : (.isValue (.boolean Bool.false)) ∈ T :=
                  (isBoolSing_inv hcc) ▸ hc
                exact hnb _ hmem
            | false => rfl
          rw [h1, h2, isBoolClass_inv hbl]
          rfl
      | false => rfl
theorem removeTy_noBool {S T : Ty}
    (hnb : ∀ b ∈ T, (match b with
      | .isValue (.boolean _) => False | _ => True)) :
    removeTy S T
      = S.filter (fun a => !T.any (fun b => tmovesV a b)) := by
  induction S with
  | nil => rfl
  | cons a rest ih =>
      simp only [removeTy, List.flatMap_cons]
      rw [removeAtom_noBool hnb]
      cases h : T.any (fun b => tmovesV a b) with
  | true =>
      show ([] : Ty) ++ List.flatMap (fun a => removeAtom a T) rest = _
      rw [show List.flatMap (fun a => removeAtom a T) rest = removeTy rest T from rfl, ih]
      simp only [List.nil_append, List.filter, h, Bool.not_true, reduceIte]
  | false =>
      show [a] ++ List.flatMap (fun a => removeAtom a T) rest = _
      rw [show List.flatMap (fun a => removeAtom a T) rest = removeTy rest T from rfl, ih]
      rw [List.filter_cons_of_pos (by simp [h])]
      rfl


theorem removeTy_nil_imp {t T : Ty}
    (hnb : ∀ b ∈ T, (match b with
      | .isValue (.boolean _) => False | _ => True))
    (hr : removeTy t T = []) :
    tmoves t T = Bool.true := by
  rw [removeTy_noBool hnb] at hr
  unfold tmoves
  simp only [List.all_eq_true]
  intro a ha
  have hni : a ∉ List.filter (fun a => !T.any (fun b => tmovesV a b)) t := by
    rw [hr]
    intro hc
    cases hc
  cases hp : T.any (fun b => tmovesV a b) with
  | false =>
      exact absurd (by
        simp only [List.mem_filter]
        exact ⟨ha, by simp [hp]⟩) hni
  | true => rfl

theorem removeTy_nil_flat {t T : Ty} (hr : removeTy t T = []) :
    ∀ a ∈ t, removeAtom a T = [] := by
  intro a ha
  cases h : removeAtom a T with
  | nil => rfl
  | cons x xs =>
      exact absurd (show x ∈ removeTy t T from List.mem_flatMap.mpr
        ⟨a, ha, h ▸ (List.mem_cons.mpr (Or.inl rfl))⟩)
        (by rw [hr]; intro hc; cases hc)

/-- What can sit under the boolean class atom. -/
theorem covers_boolClass {a : VTy}
    (h : tmovesV a (.anyValue .bool) = Bool.true) :
    a = .anyValue .bool ∨ a = .isValue (.boolean Bool.true)
      ∨ a = .isValue (.boolean Bool.false) := by
  cases a with
  | anyValue c =>
      cases c with
      | bool => exact Or.inl rfl
      | undef | null | num | str | obj | list | desc => simp [tmovesV] at h
  | complN p | complT => simp [tmovesV] at h
  | isValue v =>
      cases v with
      | boolean b =>
          cases b with
          | true => exact Or.inr (Or.inl rfl)
          | false => exact Or.inr (Or.inr rfl)
      | undefined | null | number _ | str _ | obj _
      | listV _ | descV _ | compl _ _ => simp [tmovesV, tagOf] at h
  | desc _ | notPresent => simp [tmovesV] at h

/-- Only the boolean class covers the boolean class. -/
theorem boolClass_cover {b : VTy}
    (h : tmovesV (.anyValue .bool) b = Bool.true) :
    b = .anyValue .bool := by
  cases b with
  | anyValue c =>
      cases c with
      | bool => rfl
      | undef | null | num | str | obj | list | desc => simp [tmovesV] at h
  | complN _ | complT | isValue _ | desc _ | notPresent => simp [tmovesV] at h

/-- The bool class, filter-kept, removes to [] only via both
    singleton verdicts present in T. -/
theorem boolClass_removed_sings {T : Ty}
    (hkept : T.any (fun c => tmovesV (.anyValue .bool) c) = Bool.false)
    (hr : removeAtom (.anyValue .bool) T = []) :
    T.any (isBoolSing Bool.true) = Bool.true
      ∧ T.any (isBoolSing Bool.false) = Bool.true := by
  cases hc1 : T.any (isBoolSing Bool.true) with
  | true =>
      refine ⟨rfl, ?_⟩
      cases hc2 : T.any (isBoolSing Bool.false) with
      | true => rfl
      | false =>
          exfalso
          simp only [removeAtom, hkept, hc2, Bool.true_and] at hr
          rw [hc1] at hr
          simp only [reduceIte] at hr
          exact List.cons_ne_nil _ _ hr
  | false =>
      exfalso
      cases hc2 : T.any (isBoolSing Bool.false) with
      | true =>
          simp only [removeAtom, hkept, hc1, Bool.false_and] at hr
          rw [hc2] at hr
          simp only [reduceIte] at hr
          exact List.cons_ne_nil _ _ hr
      | false =>
          rw [removeAtom, hkept, hc1, hc2] at hr
          simp only [Bool.false_and, reduceIte] at hr
          exact List.cons_ne_nil _ _ hr

theorem removeTy_nil_cov {t' t T : Ty} (h : slotLe t' t)
    (hr : removeTy t T = []) : removeTy t' T = [] := by
  cases hr' : removeTy t' T with
  | nil => rfl
  | cons x' rest' =>
      exfalso
      have hx' : x' ∈ removeTy t' T := by
        rw [hr']
        exact List.mem_cons_self ..
      simp only [removeTy, List.mem_flatMap] at hx'
      obtain ⟨b', hb', hxm⟩ := hx'
      obtain ⟨b, hb, hbb⟩ := tyLe_cov_atoms h.1 b' hb'
      have hbn : removeAtom b T = [] := removeTy_nil_flat hr b hb
      cases hf' : T.any (fun c => tmovesV b' c) with
      | true =>
          simp only [removeAtom, hf', reduceIte] at hxm
          cases hxm
      | false =>
          have hbf : T.any (fun c => tmovesV b c) = Bool.false := by
            cases hbf : T.any (fun c => tmovesV b c) with
            | true =>
                exfalso
                obtain ⟨c, hc1, hc2⟩ := List.any_eq_true.mp hbf
                rw [List.any_eq_true.mpr ⟨c, hc1, tmovesV_trans hbb hc2⟩]
                  at hf'
                exact Bool.noConfusion hf'
            | false => rfl
          cases hb'eq : isBoolClass b' with
          | true =>
              have hbl' : b' = .anyValue .bool := isBoolClass_inv hb'eq
              subst hbl'
              have hbl : b = .anyValue .bool := boolClass_cover hbb
              rw [hbl] at hbn
              rw [hbn] at hxm
              cases hxm
          | false =>
              simp only [removeAtom, hf', hb'eq, reduceIte,
                List.mem_singleton] at hxm
              cases hbeq : isBoolClass b with
              | true =>
                  have hbl : b = .anyValue .bool := isBoolClass_inv hbeq
                  rw [hbl] at hbb
                  obtain ⟨hs1, hs2⟩ := boolClass_removed_sings
                    (show T.any (fun c => tmovesV (.anyValue .bool) c)
                        = Bool.false from by rw [← hbl]; exact hbf)
                    (show removeAtom (.anyValue .bool) T = [] from by
                      rw [← hbl]; exact hbn)
                  have h1 : (.isValue (.boolean Bool.true)) ∈ T :=
                    T_has_sing T Bool.true hs1
                  have h2 : (.isValue (.boolean Bool.false)) ∈ T :=
                    T_has_sing T Bool.false hs2
                  rcases covers_boolClass hbb with rfl | rfl | rfl
                  · rw [isBoolClass_reduce] at hb'eq
                    exact Bool.noConfusion hb'eq
                  · rw [List.any_eq_true.mpr ⟨_, h1, tmovesV_refl _⟩] at hf'
                    exact Bool.noConfusion hf'
                  · rw [List.any_eq_true.mpr ⟨_, h2, tmovesV_refl _⟩] at hf'
                    exact Bool.noConfusion hf'
              | false =>
                  simp only [removeAtom, hbf, hbeq, reduceIte] at hbn
                  cases hbn

/-- Coverage of the empty refined slot. -/
theorem tyCov_nil {η : HeapCallableTy} {t : Ty} : tyCov η [] t := by
  intro a ha
  cases ha

/-- Coverage distributes over append. -/
theorem tyCov_append {η : HeapCallableTy} {a1 b1 a2 b2 : Ty}
    (h1 : tyCov η a1 b1) (h2 : tyCov η a2 b2) :
    tyCov η (a1 ++ a2) (b1 ++ b2) := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨b, hb, hac⟩ := h1 a ha
    exact ⟨b, List.mem_append.mpr (Or.inl hb), hac⟩
  · obtain ⟨b, hb, hac⟩ := h2 a ha
    exact ⟨b, List.mem_append.mpr (Or.inr hb), hac⟩

theorem stackCov_take : ∀ {σ' σ : List Ty} (n : Nat) {η : HeapCallableTy},
    stackCov η σ' σ → stackCov η (σ'.take n) (σ.take n)
  | _, _, 0, _, _ => True.intro
  | [], [], _ + 1, _, _ => True.intro
  | a' :: σ', a :: σ, n + 1, η, h => by
      exact ⟨h.1, stackCov_take n h.2⟩
termination_by σ' => sizeOf σ'
decreasing_by all_goals simp_wf <;> omega

/-- The bool class atom is deeply pure. -/
theorem pureAtomDeep_bool : pureAtomDeep (.anyValue .bool) := trivial

/-- meetAtom preserves full atom coverage. -/
theorem atomCov_meet {η : HeapCallableTy} {a' a b : VTy}
    (hac : atomCov η a' a) {m' : VTy} (hm' : meetAtom a' b = some m') :
    ∃ m, meetAtom a b = some m ∧ atomCov η m' m := by
  have hle := atomCov_tmoves hac
  cases a' with
  | complN p | complT =>
      simp only [meetAtom] at hm'
      exact absurd hm' (by simp)
  | notPresent =>
      cases a with
      | notPresent =>
          cases b with
          | notPresent =>
              simp only [meetAtom, Option.some.injEq] at hm'
              subst hm'
              exact ⟨.notPresent, rfl, atomCov_refl η _⟩
          | complN q | complT | anyValue _ | isValue _ | desc _ =>
              simp only [meetAtom] at hm'
              exact absurd hm' (by simp)
      | complN q | complT | anyValue _ | isValue _ | desc _ =>
          simp [tmovesV] at hle
  | anyValue c' =>
      cases a with
      | anyValue c =>
          have hc : c' = c := by
            simp only [tmovesV, decide_eq_true_eq] at hle
            exact hle
          subst hc
          cases b with
          | anyValue c2 =>
              simp only [meetAtom] at hm' ⊢
              split at hm'
              · next hcc =>
                  rw [if_pos hcc]
                  simp only [Option.some.injEq] at hm'
                  subst hm'
                  exact ⟨.anyValue c', rfl, atomCov_refl η _⟩
              · exact absurd hm' (by simp)
          | isValue v =>
              simp only [meetAtom] at hm' ⊢
              split at hm'
              · next hcc =>
                  rw [if_pos hcc]
                  simp only [Option.some.injEq] at hm'
                  subst hm'
                  exact ⟨.isValue v, rfl, atomCov_refl η _⟩
              · exact absurd hm' (by simp)
          | desc fs =>
              cases c' with
              | desc =>
                  simp only [meetAtom, Option.some.injEq] at hm' ⊢
                  subst hm'
                  exact ⟨.desc fs, rfl, atomCov_refl η _⟩
              | undef | null | bool | num | str | obj _ | list =>
                  simp only [meetAtom] at hm'
                  exact absurd hm' (by simp)
          | complN q | complT | notPresent =>
              simp only [meetAtom] at hm'
              exact absurd hm' (by simp)
      | complN q | complT | isValue _ | desc _ | notPresent =>
          simp [tmovesV] at hle
  | isValue v =>
      cases a with
      | isValue w =>
          have hvw : v = w := by
            simp only [tmovesV] at hle
            exact beq_iff_eq.mp hle
          subst hvw
          cases b with
          | isValue u =>
              simp only [meetAtom] at hm' ⊢
              split at hm'
              · next hcc =>
                  rw [if_pos hcc]
                  simp only [Option.some.injEq] at hm'
                  subst hm'
                  exact ⟨.isValue v, rfl, atomCov_refl η _⟩
              · exact absurd hm' (by simp)
          | anyValue c =>
              simp only [meetAtom] at hm' ⊢
              split at hm'
              · next hcc =>
                  rw [if_pos hcc]
                  simp only [Option.some.injEq] at hm'
                  subst hm'
                  exact ⟨.isValue v, rfl, atomCov_refl η _⟩
              · exact absurd hm' (by simp)
          | complN q | complT | desc _ | notPresent =>
              simp only [meetAtom] at hm'
              exact absurd hm' (by simp)
      | anyValue c =>
          have hc : tagOf v = c := by
            simp only [tmovesV, decide_eq_true_eq] at hle
            exact hle
          cases b with
          | isValue u =>
              simp only [meetAtom] at hm' ⊢
              split at hm'
              · next hvu =>
                  have hvu' : v = u := beq_iff_eq.mp hvu
                  subst hvu'
                  rw [if_pos hc]
                  simp only [Option.some.injEq] at hm'
                  subst hm'
                  exact ⟨.isValue v, rfl, atomCov_refl η _⟩
              · exact absurd hm' (by simp)
          | anyValue c2 =>
              simp only [meetAtom] at hm' ⊢
              split at hm'
              · next hc2 =>
                  have hcc : c = c2 := hc.symm.trans hc2
                  rw [if_pos hcc]
                  simp only [Option.some.injEq] at hm'
                  subst hm'
                  exact ⟨.anyValue c, rfl, hac⟩
              · exact absurd hm' (by simp)
          | complN q | complT | desc _ | notPresent =>
              simp only [meetAtom] at hm'
              exact absurd hm' (by simp)
      | complN q | complT | desc _ | notPresent =>
          simp [tmovesV] at hle
  | desc fs =>
      cases a with
      | desc fs2 =>
          have hfs : fs = fs2 := by
            simp only [tmovesV, decide_eq_true_eq] at hle
            exact hle
          subst hfs
          cases b with
          | desc fs3 =>
              simp only [meetAtom] at hm' ⊢
              split at hm'
              · next hcc =>
                  rw [if_pos hcc]
                  simp only [Option.some.injEq] at hm'
                  subst hm'
                  exact ⟨.desc fs, rfl, atomCov_refl η _⟩
              · exact absurd hm' (by simp)
          | anyValue c2 =>
              cases c2 with
              | desc =>
                  simp only [meetAtom, Option.some.injEq] at hm' ⊢
                  subst hm'
                  exact ⟨.desc fs, rfl, atomCov_refl η _⟩
              | undef | null | bool | num | str | obj _ | list =>
                  simp only [meetAtom] at hm'
                  exact absurd hm' (by simp)
          | complN q | complT | isValue _ | notPresent =>
              simp only [meetAtom] at hm'
              exact absurd hm' (by simp)
      | anyValue c =>
          cases c with
          | desc =>
              cases b with
              | desc fs2 =>
                  simp only [meetAtom] at hm' ⊢
                  split at hm'
                  · next hff =>
                      subst hff
                      simp only [Option.some.injEq] at hm'
                      subst hm'
                      exact ⟨.desc fs, rfl, atomCov_refl η _⟩
                  · exact absurd hm' (by simp)
              | anyValue c2 =>
                  cases c2 with
                  | desc =>
                      simp only [meetAtom, Option.some.injEq] at hm' ⊢
                      subst hm'
                      exact ⟨.anyValue .desc, rfl, hac⟩
                  | undef | null | bool | num | str | obj _ | list =>
                      simp only [meetAtom] at hm'
                      exact absurd hm' (by simp)
              | complN q | complT | isValue _ | notPresent =>
                  simp only [meetAtom] at hm'
                  exact absurd hm' (by simp)
          | undef | null | bool | num | str | obj _ | list =>
              simp [tmovesV] at hle
      | complN q | complT | isValue _ | notPresent =>
          simp [tmovesV] at hle

theorem meetTy_tyCov {η : HeapCallableTy} {S' S T : Ty}
    (hcov : ∀ a' ∈ S', ∃ a ∈ S, atomCov η a' a) :
    tyCov η (meetTy S' T) (meetTy S T) := by
  intro m' hm'
  simp only [meetTy, List.mem_flatMap] at hm' ⊢
  obtain ⟨a', ha', b, hb, hmem⟩ := hm'
  cases hmeet : meetAtom a' b with
  | none =>
      exfalso
      rw [hmeet] at hmem
      cases hmem
  | some w =>
      rw [hmeet] at hmem
      have hwm : m' = w := by simpa using hmem
      subst hwm
      obtain ⟨a, ha, hac⟩ := hcov a' ha'
      obtain ⟨m, hm, hmac⟩ := atomCov_meet hac hmeet
      exact ⟨m, ⟨a, ha, ⟨b, hb, by
        rw [hm]; exact List.mem_singleton.mpr rfl⟩⟩, hmac⟩

/-- removeAtom is coverage-covariant. -/
theorem removeAtom_tyCov {η : HeapCallableTy} {a' a : VTy}
    (hac : atomCov η a' a) (T : Ty) : ∀ x' ∈ removeAtom a' T,
    ∃ x ∈ removeAtom a T, atomCov η x' x := by
  have haa := atomCov_tmoves hac
  intro x' hx'
  cases hf' : T.any (fun c => tmovesV a' c) with
  | true =>
      simp only [removeAtom, hf', reduceIte] at hx'
      cases hx'
  | false =>
      have hbf : T.any (fun c => tmovesV a c) = Bool.false := by
        cases hbf : T.any (fun c => tmovesV a c) with
        | true =>
            exfalso
            obtain ⟨c, hc1, hc2⟩ := List.any_eq_true.mp hbf
            rw [List.any_eq_true.mpr ⟨c, hc1, tmovesV_trans haa hc2⟩]
              at hf'
            exact Bool.noConfusion hf'
        | false => rfl
      cases hb'eq : isBoolClass a' with
      | true =>
          have ha'cl : a' = .anyValue .bool := isBoolClass_inv hb'eq
          rw [ha'cl] at haa hx'
          have hbl : a = .anyValue .bool := boolClass_cover haa
          rw [hbl]
          exact ⟨x', hx', atomCov_refl η _⟩
      | false =>
          simp only [removeAtom, hf', hb'eq] at hx'
          simp at hx'
          obtain rfl : x' = a' := hx'
          cases hbeq : isBoolClass a with
          | false =>
              refine ⟨a, ?_, hac⟩
              simp only [removeAtom, hbf, hbeq] at ⊢
              simp
          | true =>
              have hbl : a = .anyValue .bool := isBoolClass_inv hbeq
              rw [hbl] at haa hbf ⊢
              rcases covers_boolClass haa with rfl | rfl | rfl
              · exact absurd hb'eq (by simp [isBoolClass])
              · by_cases hc : T.any (isBoolSing Bool.true) = Bool.true
                · exfalso
                  rw [List.any_eq_true.mpr ⟨_, T_has_sing T Bool.true hc,
                    tmovesV_refl _⟩] at hf'
                  exact Bool.noConfusion hf'
                · by_cases h2 : T.any (isBoolSing Bool.false) = Bool.true
                  · refine ⟨VTy.isValue (.boolean Bool.true), ?_,
                      atomCov_refl η _⟩
                    have hc2 : ¬((T.any (isBoolSing Bool.true)
                        && T.any (isBoolSing Bool.false))
                        = Bool.true) := by
                      intro hcc
                      rw [Bool.and_eq_true] at hcc
                      exact hc hcc.1
                    simp only [removeAtom]
                    rw [if_neg (by rw [hbf]; exact fun h => Bool.noConfusion h),
                      if_pos isBoolClass_reduce, if_neg hc2, if_neg hc,
                      if_pos h2]
                    exact List.mem_singleton.mpr rfl
                  · refine ⟨.anyValue .bool, ?_,
                      atomCov_of_pure_cover η haa pureAtomDeep_bool⟩
                    have hc2 : ¬((T.any (isBoolSing Bool.true)
                        && T.any (isBoolSing Bool.false))
                        = Bool.true) := by
                      intro hcc
                      rw [Bool.and_eq_true] at hcc
                      exact hc hcc.1
                    simp only [removeAtom]
                    rw [if_neg (by rw [hbf]; exact fun h => Bool.noConfusion h),
                      if_pos isBoolClass_reduce, if_neg hc2, if_neg hc,
                      if_neg h2]
                    exact List.mem_singleton.mpr rfl
              · by_cases hc : T.any (isBoolSing Bool.false) = Bool.true
                · exfalso
                  rw [List.any_eq_true.mpr ⟨_, T_has_sing T Bool.false hc,
                    tmovesV_refl _⟩] at hf'
                  exact Bool.noConfusion hf'
                · by_cases h1 : T.any (isBoolSing Bool.true) = Bool.true
                  · refine ⟨VTy.isValue (.boolean Bool.false), ?_,
                      atomCov_refl η _⟩
                    have hc2 : ¬((T.any (isBoolSing Bool.true)
                        && T.any (isBoolSing Bool.false))
                        = Bool.true) := by
                      intro hcc
                      rw [Bool.and_eq_true] at hcc
                      exact hc hcc.2
                    simp only [removeAtom]
                    rw [if_neg (by rw [hbf]; exact fun h => Bool.noConfusion h),
                      if_pos isBoolClass_reduce, if_neg hc2, if_pos h1]
                    exact List.mem_singleton.mpr rfl
                  · refine ⟨.anyValue .bool, ?_,
                      atomCov_of_pure_cover η haa pureAtomDeep_bool⟩
                    have hc2 : ¬((T.any (isBoolSing Bool.true)
                        && T.any (isBoolSing Bool.false))
                        = Bool.true) := by
                      intro hcc
                      rw [Bool.and_eq_true] at hcc
                      exact hc hcc.2
                    simp only [removeAtom]
                    rw [if_neg (by rw [hbf]; exact fun h => Bool.noConfusion h),
                      if_pos isBoolClass_reduce, if_neg hc2, if_neg h1,
                      if_neg hc]
                    exact List.mem_singleton.mpr rfl

theorem removeTy_tyCov {η : HeapCallableTy} {t' t T : Ty}
    (hcov : ∀ a' ∈ t', ∃ a ∈ t, atomCov η a' a) :
    tyCov η (removeTy t' T) (removeTy t T) := by
  intro x' hx'
  simp only [removeTy, List.mem_flatMap] at hx' ⊢
  obtain ⟨a', ha', hxm⟩ := hx'
  obtain ⟨a, ha, haa⟩ := hcov a' ha'
  obtain ⟨x, hx, hxx⟩ := removeAtom_tyCov haa T x' hxm
  exact ⟨x, ⟨a, ha, hx⟩, hxx⟩

/-- payloadsOf preserves atom coverage (through complN payloads). -/
theorem payloadsOf_tyCov {η : HeapCallableTy} {t' t : Ty}
    (hcov : tyCov η t' t) :
    tyCov η (payloadsOf t') (payloadsOf t) := by
  intro p' hp'
  simp only [payloadsOf, List.mem_flatMap] at hp' ⊢
  obtain ⟨a', ha', hmem'⟩ := hp'
  obtain ⟨a, ha, hac⟩ := hcov a' ha'
  cases a with
  | complN q =>
      refine ⟨q, ⟨.complN q, ha, by simp⟩, ?_⟩
      cases a' with
      | complN r =>
          have heq : p' = r := by simpa using hmem'
          subst heq
          exact atomCov_pay hac
      | complT | anyValue _ | isValue _ | desc _ | notPresent =>
          have hn : p' ∈ ([] : Ty) := hmem'
          exact absurd hn (by simp)
  | complT | anyValue _ | isValue _ | desc _ | notPresent =>
      cases a' with
      | complN r => exact absurd (atomCov_tmoves hac) (by simp [tmovesV])
      | complT | anyValue _ | isValue _ | desc _ | notPresent =>
          have hn : p' ∈ ([] : Ty) := hmem'
          exact absurd hn (by simp)

/-- payloadOf is coverage-covariant on covered slots. -/
theorem payloadOf_tyCov {η : HeapCallableTy} {t' t : Ty}
    (hcov : tyCov η t' t) (hle : slotLe t' t) {ps : Ty}
    (hp : payloadOf t = some ps) : ∃ ps', payloadOf t' = some ps'
      ∧ tyCov η ps' ps := by
  have hpure : ∀ a ∈ t, ∃ p, a = .complN p :=
    payloadOf_pure t ps hp
  have hne : t ≠ [] := by
    intro hc
    subst hc
    simp [payloadOf] at hp
  rw [payloadOf_eq t hpure hne] at hp
  simp only [Option.some.injEq] at hp
  subst hp
  have hne' : t' ≠ [] := fun hc => hle.2 hne hc
  have hpure' : ∀ a' ∈ t', ∃ p, a' = .complN p := by
    intro a' ha'
    obtain ⟨a, ha, hac⟩ := hcov a' ha'
    obtain ⟨q, hq⟩ := hpure a ha
    rw [hq] at hac
    have h1 := atomCov_tmoves hac
    cases a' with
    | complN p' => exact ⟨p', rfl⟩
    | complT | anyValue _ | isValue _ | desc _ | notPresent =>
        simp [tmovesV] at h1
  refine ⟨payloadsOf t', payloadOf_eq t' hpure' hne', ?_⟩
  exact payloadsOf_tyCov hcov

/-- bareOf preserves coverage (through the complN wrap). -/
theorem bareOf_tyCov {η : HeapCallableTy} {t' t : Ty}
    (hcov : tyCov η t' t) {bs : Ty} (hb : bareOf t = some bs) :
    bareOf t' = some t' ∧ tyCov η (t'.map VTy.complN) (bs.map VTy.complN) := by
  have hpure := bareOf_pure t bs hb
  have hbs : bs = t := by
    have hs := bareOf_eq_self (t := t) hpure
    rw [hs] at hb
    simp only [Option.some.injEq] at hb
    exact hb.symm
  subst hbs
  have hpure' : ∀ a' ∈ t', isBareVTy a' = Bool.true := by
    intro a' ha'
    obtain ⟨a, ha, hac⟩ := hcov a' ha'
    exact isBareVTy_of_cover (hpure a ha) (atomCov_tmoves hac)
  refine ⟨bareOf_eq_self hpure', ?_⟩
  intro b hbm
  simp only [List.mem_map] at hbm
  obtain ⟨a', ha', rfl⟩ := hbm
  obtain ⟨a, ha, hac⟩ := hcov a' ha'
  exact ⟨.complN a, by simp [ha], atomCov_complN_of hac⟩


theorem payloadOf_eq' {t ps : Ty} (hp : payloadOf t = some ps) :
    ps = payloadsOf t ∧ t ≠ [] := by
  have hpure := payloadOf_pure t ps hp
  have hne : t ≠ [] := by
    intro hc
    subst hc
    simp [payloadOf] at hp
  rw [payloadOf_eq t hpure hne] at hp
  simp only [Option.some.injEq] at hp
  exact ⟨hp.symm, hne⟩

theorem leTy_cov : ∀ {ts' ts ps : List Ty}, slotsLe ts' ts →
    leTy ts ps = Bool.true → leTy ts' ps = Bool.true := by
  intro ts' ts ps
  induction ts' generalizing ts ps with
  | nil =>
      intro hs hle
      cases ts with
      | nil => cases ps <;> simp [leTy] at hle ⊢ <;> exact hle
      | cons t ts1 => exact absurd hs (by simp [slotsLe])
  | cons t' ts1' ih =>
      intro hs hle
      cases ts with
      | nil => exact absurd hs (by simp [slotsLe])
      | cons t ts1 =>
          obtain ⟨hslot, hs1⟩ := hs
          cases ps with
          | nil => simp [leTy] at hle
          | cons p ps1 =>
              simp only [leTy] at hle ⊢
              obtain ⟨hp1, hp2⟩ := (Bool.and_eq_true _ _) |>.mp hle
              exact (Bool.and_eq_true _ _) |>.mpr ⟨tmoves_trans hslot.1 hp1, ih hs1 hp2⟩


/-- A boolean singleton is covered by the bool class. -/
theorem atomCov_boolSing_class {η : HeapCallableTy} {b : Bool} :
    atomCov η (.isValue (.boolean b)) (.anyValue .bool) :=
  atomCov_of_pure_cover η (by simp [tmovesV, tagOf]) pureAtomDeep_bool

/-- Normalization (exact object locations through η) preserves
    coverage. -/
theorem normalizeAtom_cov {η : HeapCallableTy} : ∀ {a' a : VTy},
    atomCov η a' a → atomCov η (normalizeAtom η a') (normalizeAtom η a)
  | .complN p, a, hac => by
      have hle := atomCov_tmoves hac
      cases a with
      | complN q =>
          simp only [normalizeAtom]
          exact atomCov_complN_of (normalizeAtom_cov (atomCov_pay hac))
      | complT | anyValue _ | isValue _ | desc _ | notPresent =>
          simp [tmovesV] at hle
  | .complT, a, hac => by
      have hle := atomCov_tmoves hac
      cases a with
      | complT =>
          simp only [normalizeAtom]
          exact ⟨hle, atomCov_dec hac, True.intro⟩
      | complN q | anyValue _ | isValue _ | desc _ | notPresent =>
          simp [tmovesV] at hle
  | .anyValue _, a, hac => by
      have hle := atomCov_tmoves hac
      cases a with
      | anyValue _ =>
          simp only [normalizeAtom]
          exact ⟨hle, atomCov_dec hac, True.intro⟩
      | complN q | complT | isValue _ | desc _ | notPresent =>
          simp [tmovesV] at hle
  | .desc _, a, hac => by
      have hle := atomCov_tmoves hac
      cases a with
      | desc _ =>
          simp only [normalizeAtom]
          exact ⟨hle, atomCov_dec hac, True.intro⟩
      | anyValue c =>
          cases c with
          | desc =>
              simp only [normalizeAtom]
              exact ⟨hle, atomCov_dec hac, True.intro⟩
          | undef | null | bool | num | str | obj _ | list =>
              simp [tmovesV] at hle
      | complN q | complT | isValue _ | notPresent =>
          simp [tmovesV] at hle
  | .notPresent, a, hac => by
      have hle := atomCov_tmoves hac
      cases a with
      | notPresent =>
          simp only [normalizeAtom]
          exact ⟨hle, atomCov_dec hac, True.intro⟩
      | complN q | complT | anyValue _ | isValue _ | desc _ =>
          simp [tmovesV] at hle
  | .isValue v, a, hac => by
      have hle := atomCov_tmoves hac
      cases v with
      | obj loc =>
          cases a with
          | complN q | complT | desc _ | notPresent => simp [tmovesV] at hle
          | anyValue c =>
              cases c with
              | obj b =>
                  cases b with
                  | false =>
                      have hdec := atomCov_dec hac "IsCallable" (isCallableAtom η)
                        (by simp [predDecide])
                      simp only [isCallableAtom] at hdec
                      simp only [normalizeAtom]
                      rw [hdec]
                      exact atomCov_refl η _
                  | true => simp [tmovesV, tagOf] at hle
              | undef | null | bool | num | str | list | desc =>
                  simp [tmovesV, tagOf] at hle
          | isValue w =>
              cases w with
              | obj loc2 =>
                  simp only [tmovesV] at hle
                  have h12 : loc = loc2 :=
                    beq_iff_eq.mp (beq_iff_eq.mp hle)
                  subst h12
                  simp only [normalizeAtom]
                  exact atomCov_refl η _
              | undefined | null | boolean _ | number _ | str _ | listV _
                | descV _ | compl _ _ => simp [tmovesV] at hle
      | undefined | null | boolean _ | number _ | str _ | listV _
        | descV _ | compl _ _ =>
          cases a with
          | isValue w =>
              cases w with
              | obj loc2 => simp [tmovesV] at hle
              | undefined | null | boolean _ | number _ | str _ | listV _
                | descV _ | compl _ _ =>
                  simp only [normalizeAtom]
                  exact hac
          | anyValue _ =>
              simp only [normalizeAtom]
              exact hac
          | complN q | complT | desc _ | notPresent =>
              simp [tmovesV] at hle
termination_by a' => sizeOf a'
decreasing_by all_goals simp_wf <;> omega

theorem normalizeTy_cov {η : HeapCallableTy} {t' t : Ty}
    (hcov : tyCov η t' t) :
    tyCov η (normalizeTy η t') (normalizeTy η t) := by
  intro b hb
  obtain ⟨a', ha', rfl⟩ := List.mem_map.mp hb
  obtain ⟨a, ha, hac⟩ := hcov a' ha'
  exact ⟨normalizeAtom η a,
    List.mem_map.mpr ⟨a, ha, rfl⟩, normalizeAtom_cov hac⟩

theorem terminal_markThrow (sigs : SigTable) (ex : Expr) (res : TCResult) :
    (match markThrow sigs ex res with
      | .flows fb => terminal fb = Bool.true
      | _ => False) ↔
      (match res with
        | .flows fb => terminal fb = Bool.true
        | _ => False) := by
  cases res with
  | flows fb => simp [markThrow, terminal]
  | reject s why => exact Iff.rfl

theorem typeOfE_cov (sigs : SigTable) (Γ' Γ : TyEnv) {η : HeapCallableTy} :
    ∀ (e : Expr), envLe Γ' Γ → envCov η Γ' Γ →
      ∀ t, typeOfE sigs Γ e = some t →
        ∃ t', typeOfE sigs Γ' e = some t' ∧ slotLe t' t
          ∧ tyCov η t' t := by
  intro e
  induction e using typeOfE.induct (sigs := sigs) (Γ := Γ)
    (motive1 := fun es => envLe Γ' Γ → envCov η Γ' Γ →
      ∀ ts, typesOf sigs Γ es = some ts →
        ∃ ts', typesOf sigs Γ' es = some ts' ∧ slotsLe ts' ts
          ∧ stackCov η ts' ts) with
  | case1 =>
      rename_i _ ts ht
      simp only [typesOf] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      exact ⟨[], by simp [typesOf], True.intro, True.intro⟩

  | case2 =>
      rename_i x xs t0 ts0 hxs hx ih2 ih1 hle hcov ts ht
      simp only [typesOf, hx, hxs, Option.some.injEq] at ht
      subst ht
      obtain ⟨tx', htx', hslotx, htxc⟩ := ih2 hle hcov t0 hx
      obtain ⟨txs', htxs', hslotxs, htxsc⟩ := ih1 hle hcov ts0 hxs
      exact ⟨tx' :: txs', by
        simp only [typesOf, htx', htxs'], ⟨hslotx, hslotxs⟩, ⟨htxc, htxsc⟩⟩

  | case3 =>
      rename_i x xs hcontra ih2 ih1 hle hcov ts ht
      exfalso
      cases hx : typeOfE sigs Γ x with
      | none =>
          rw [show typesOf sigs Γ (x :: xs) = none from by
            simp only [typesOf, hx]] at ht
          simp at ht
      | some tx =>
          cases hxs : typesOf sigs Γ xs with
          | none =>
              rw [show typesOf sigs Γ (x :: xs) = none from by
                simp only [typesOf, hx, hxs]] at ht
              simp at ht
          | some txs =>
              rw [show typesOf sigs Γ (x :: xs) = some (tx :: txs) from by
                simp only [typesOf, hx, hxs]] at ht
              simp only [Option.some.injEq] at ht
              subst ht
              exact hcontra tx txs hx hxs

  | case4 =>
      rename_i x
      intro hle hcov t ht
      simp only [typeOfE] at ht
      obtain ⟨t', ht', hle', hne'⟩ := envLe_lookup_cov_full hle ht
      obtain ⟨t2, ht2, htcov⟩ := hcov x t' ht'
      rw [ht] at ht2
      have h2e : t2 = t := by simpa using ht2.symm
      subst h2e
      exact ⟨t', by simp only [typeOfE]; exact ht', ⟨hle', hne'⟩, htcov⟩

  | case5 =>
      intro _ _ t ht
      refine ⟨t, ?_, slotLe_refl t, tyCov_refl _ t⟩
      simp only [typeOfE] at ht ⊢
      exact ht

  | case6 =>
      intro _ _ t ht
      refine ⟨t, ?_, slotLe_refl t, tyCov_refl _ t⟩
      simp only [typeOfE] at ht ⊢
      exact ht

  | case7 =>
      intro _ _ t ht
      refine ⟨t, ?_, slotLe_refl t, tyCov_refl _ t⟩
      simp only [typeOfE] at ht ⊢
      exact ht

  | case8 =>
      intro _ _ t ht
      refine ⟨t, ?_, slotLe_refl t, tyCov_refl _ t⟩
      simp only [typeOfE] at ht ⊢
      exact ht

  | case9 =>
      intro _ _ t ht
      refine ⟨t, ?_, slotLe_refl t, tyCov_refl _ t⟩
      simp only [typeOfE] at ht ⊢
      exact ht

  | case10 =>
      intro _ _ t ht
      refine ⟨t, ?_, slotLe_refl t, tyCov_refl _ t⟩
      simp only [typeOfE] at ht ⊢
      exact ht

  | case11 =>
      rename_i e ps hps ih
      intro hle hcov t ht
      simp only [typeOfE, hps] at ht
      cases hpay : payloadOf ps with
      | none => rw [hpay] at ht; simp at ht
      | some psv =>
          rw [hpay] at ht
          simp only [Option.some.injEq] at ht
          subst ht
          obtain ⟨ps', hps', hslot, hpscov⟩ := ih hle hcov ps hps
          obtain ⟨t', ht', hslot'⟩ := payloadOf_cov hslot hpay
          obtain ⟨t2, ht2, htcov'⟩ := payloadOf_tyCov hpscov hslot hpay
          have htcov'' : tyCov η t' psv :=
            (Option.some.inj (ht2.symm.trans ht')) ▸ htcov'
          exact ⟨t', by simp only [typeOfE, hps', ht'], hslot', htcov''⟩

  | case12 =>
      rename_i e hnone ih
      intro _ _ t ht
      simp only [typeOfE, hnone] at ht
      exact absurd ht (by simp)

  | case13 =>
      rename_i e ps hps ih
      intro hle hcov t ht
      simp only [typeOfE, hps] at ht
      cases hb : bareOf ps with
      | none => rw [hb] at ht; simp at ht
      | some bs =>
          rw [hb] at ht
          simp only [Option.map_some, Option.some.injEq] at ht
          subst ht
          obtain ⟨ps', hps', hslot, hpscov⟩ := ih hle hcov ps hps
          obtain ⟨hb', hbs'⟩ := bareOf_cov hslot hb
          obtain ⟨-, hbcov⟩ := bareOf_tyCov hpscov hb
          exact ⟨ps'.map VTy.complN, by
            simp only [typeOfE, hps', hb', Option.map_some],
            complN_map_cov hbs', hbcov⟩

  | case14 =>
      rename_i e hnone ih
      intro _ _ t ht
      simp only [typeOfE, hnone] at ht
      exact absurd ht (by simp)

  | case15 =>
      rename_i f as ps snd hsig ts hts hguard ih1
      intro hle hcov t ht
      simp only [typeOfE, hsig, hts] at ht
      rw [if_pos hguard] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      obtain ⟨ts', hts', hslots, -⟩ := ih1 hle hcov ts hts
      have hguard' : (leTy ts' ps || as.length == ps.length - 1
          && leTy ts' ps.dropLast) = Bool.true := by
        rw [Bool.or_eq_true] at hguard
        cases hguard with
        | inl hA =>
            have h1 : leTy ts' ps = Bool.true := leTy_cov hslots hA
            simp only [h1, Bool.true_or]
        | inr hB =>
            rw [Bool.and_eq_true] at hB
            obtain ⟨hlen, hdl⟩ := hB
            have h2 : leTy ts' ps.dropLast = Bool.true := leTy_cov hslots hdl
            simp only [hlen, h2, Bool.and_true, Bool.true_and, Bool.or_true]
      exact ⟨complPayload snd, by
        simp only [typeOfE, hsig, hts', if_pos hguard'], slotLe_refl _,
        tyCov_refl _ _⟩

  | case16 =>
      rename_i f as ps snd hsig ts hts hguard ih1
      intro _ _ t ht
      rw [show typeOfE sigs Γ (.call f as) = none from by
        simp only [typeOfE, hsig, hts, if_neg hguard]] at ht
      exact absurd ht (by simp)

  | case17 =>
      rename_i f as ps snd hsig hnone ih1
      intro _ _ t ht
      rw [show typeOfE sigs Γ (.call f as) = none from by
        simp only [typeOfE, hsig, hnone]] at ht
      exact absurd ht (by simp)

  | case18 =>
      rename_i f as hsig
      intro _ _ t ht
      simp only [typeOfE, hsig] at ht
      exact absurd ht (by simp)

  | case19 =>
      rename_i nm recv args k harity hguard ih2 ih1
      intro hle hcov t ht
      rw [Bool.and_eq_true] at hguard
      obtain ⟨hAB, h3⟩ := hguard
      rw [Bool.and_eq_true] at hAB
      obtain ⟨h1, h2⟩ := hAB
      cases hrecv : typeOfE sigs Γ recv with
      | none => rw [hrecv] at h2; simp at h2
      | some tr =>
          rw [hrecv] at h2
          simp only at h2
          obtain ⟨tr', htr', hslotr, -⟩ := ih2 hle hcov tr hrecv
          have h2' : (match typeOfE sigs Γ' recv with
              | some t2 => tmoves t2 objT
              | none => Bool.false) = Bool.true := by
            rw [htr']
            exact tmoves_trans hslotr.1 h2
          have htr'move : tmoves tr' objT = Bool.true :=
            tmoves_trans hslotr.1 h2
          have h3' : (typesOf sigs Γ' args).isSome = Bool.true := by
            cases hc : typesOf sigs Γ args with
            | none => rw [hc] at h3; simp at h3
            | some sv =>
                obtain ⟨sv', hsv', _⟩ := ih1 hle hcov sv hc
                rw [hsv']
                rfl
          have hguard' : ((args.length == k &&
              (match typeOfE sigs Γ' recv with
              | some t2 => tmoves t2 objT
              | none => Bool.false)) && (typesOf sigs Γ' args).isSome)
              = Bool.true :=
            by
              simp only [htr', htr'move, h1, h3', Bool.true_and, Bool.and_true]
          simp only [typeOfE, harity] at ht
          rw [if_pos (by
            simp only [hrecv, h1, h2, h3, Bool.true_and, Bool.and_true])] at ht
          simp only [Option.some.injEq] at ht
          subst ht
          refine ⟨mopPayload nm, ?_, slotLe_refl _, tyCov_refl _ _⟩
          rw [show typeOfE sigs Γ' (Expr.imeth nm recv args)
              = some (mopPayload nm) from by
            simp only [typeOfE, harity, htr', htr'move, h1, h3',
              Bool.true_and, Bool.and_true, if_true]]

  | case20 =>
      rename_i nm recv args k harity hguard ih2 ih1
      intro _ _ t ht
      simp only [typeOfE, harity] at ht
      rw [if_neg hguard] at ht
      exact absurd ht (by simp)

  | case21 =>
      rename_i nm recv args hnone
      intro _ _ t ht
      simp only [typeOfE, hnone] at ht
      exact absurd ht (by simp)

  | case22 =>
      rename_i nm x hval ps1 hx1 ps hpay ih
      intro hle hcov t ht
      simp only [typeOfE, if_pos hval, hx1, hpay] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      obtain ⟨ps1', hx1', hslot, hps1cov⟩ := ih hle hcov ps1 hx1
      obtain ⟨ps', hpay', hslot'⟩ := payloadOf_cov hslot hpay
      obtain ⟨ps2, hpay2, hpc'⟩ := payloadOf_tyCov hps1cov hslot hpay
      have hpc'' : tyCov η ps' ps :=
        (Option.some.inj (hpay2.symm.trans hpay')) ▸ hpc'
      exact ⟨ps', by
        simp only [typeOfE, if_pos hval, hx1', hpay'], hslot', hpc''⟩

  | case23 =>
      rename_i nm x hval ps1 hx1 hpnone ih
      intro hle hcov t ht
      simp only [typeOfE, if_pos hval, hx1, hpnone] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      obtain ⟨ps1', hx1', hslot, hps1cov⟩ := ih hle hcov ps1 hx1
      have hmopne : mopPayload nm ≠ [] := by
        have hv : nm = "Value" := beq_iff_eq.mp hval
        subst hv
        have hmp : mopPayload "Value" = langT := rfl
        intro hc
        rw [hmp] at hc
        simp [langT, anyOf, langTags] at hc
      cases hpay' : payloadOf ps1' with
      | some ps' =>
          obtain ⟨heq, hne1'⟩ := payloadOf_eq' hpay'
          have hpure1' := payloadOf_pure ps1' ps' hpay'
          refine ⟨ps', by
            simp only [typeOfE, if_pos hval, hx1', hpay'], ?_, ?_⟩
          · refine ⟨?_, ?_⟩
            · rw [heq]
              unfold tyLe tmoves
              simp only [List.all_eq_true, List.any_eq_true, List.mem_append]
              intro a ha
              obtain ⟨b, hb, hab⟩ := payloadsOf_cov (tyLe_cov_atoms hslot.1) a
                (heq ▸ ha)
              exact ⟨b, Or.inl hb, hab⟩
            · intro _
              rw [heq]
              exact payloadsOf_ne hne1' hpure1'
          · rw [heq]
            intro a ha
            obtain ⟨b, hb, hab⟩ := payloadsOf_tyCov hps1cov a ha
            exact ⟨b, List.mem_append.mpr (Or.inl hb), hab⟩
      | none =>
          refine ⟨payloadsOf ps1' ++ mopPayload nm, by
            simp only [typeOfE, if_pos hval, hx1', hpay'], ?_, ?_⟩
          · refine ⟨?_, ?_⟩
            · unfold tyLe tmoves
              simp only [List.all_eq_true, List.any_eq_true, List.mem_append]
              intro a ha
              rcases ha with h | h
              · obtain ⟨b, hb, hab⟩ :=
                  payloadsOf_cov (tyLe_cov_atoms hslot.1) a h
                exact ⟨b, Or.inl hb, hab⟩
              · exact ⟨a, Or.inr h, tmovesV_refl a⟩
            · intro _
              intro hnil
              cases hpl : payloadsOf ps1' with
              | cons y ys => rw [hpl] at hnil; simp at hnil
              | nil =>
                  rw [hpl] at hnil
                  simp only [List.nil_append] at hnil
                  exact hmopne hnil
          · exact tyCov_append (payloadsOf_tyCov hps1cov) (tyCov_refl _ _)

  | case24 =>
      rename_i nm x hval hnone ih
      intro _ _ t ht
      simp only [typeOfE, if_pos hval, hnone] at ht
      exact absurd ht (by simp)

  | case25 =>
      rename_i nm x hnv hsame ih
      intro hle hcov t ht
      simp only [typeOfE, if_neg hnv, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle hcov sv hc
            rw [hsv']
            rfl
      exact ⟨mopPayload nm, by
        simp only [typeOfE, if_neg hnv, if_pos hx'], slotLe_refl _, tyCov_refl _ _⟩

  | case26 =>
      rename_i nm x hnv hnone ih
      intro _ _ t ht
      simp only [typeOfE, if_neg hnv] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case27 =>
      rename_i es hsame ih1
      intro hle hcov t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typesOf sigs Γ' es).isSome = Bool.true := by
        cases hc : typesOf sigs Γ es with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih1 hle hcov sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .list], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _, tyCov_refl _ _⟩

  | case28 =>
      rename_i es hnone ih1
      intro _ _ t ht
      simp only [typeOfE] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case29 =>
      rename_i x ps hx hobj ih
      intro hle hcov t ht
      simp only [typeOfE, hx, if_pos hobj] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      obtain ⟨ps', hx', hslot, -⟩ := ih hle hcov ps hx
      refine ⟨[.isValue (.boolean Bool.true)], ?_, slotLe_refl _,
        tyCov_refl _ _⟩
      simp only [typeOfE, hx']
      rw [if_pos (show tmoves ps' objT = Bool.true
        from tmoves_trans hslot.1 hobj)]

  | case30 =>
      rename_i x ps hx hnobj hf ih
      exfalso
      rw [Bool.and_eq_true] at hf
      obtain ⟨hrne, hpne⟩ := hf
      have hnil : removeTy ps objT = [] := by
        simpa using hrne
      exact absurd (removeTy_nil_imp
        (t := ps) (T := objT) (by
          intro b hb
          simp only [objT, List.mem_cons, List.mem_singleton] at hb
          cases b with
          | isValue v =>
              cases v <;> simp_all
          | _ => simp_all)
        hnil) hnobj

  | case31 =>
      rename_i x ps hx hnobj hnf ih
      intro hle hcov t ht
      simp only [typeOfE, hx, if_neg hnobj, if_neg hnf] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      obtain ⟨ps', hx', hslot, -⟩ := ih hle hcov ps hx
      by_cases h1 : tmoves ps' objT = Bool.true
      · refine ⟨[.isValue (.boolean Bool.true)], ?_,
          ⟨isObject_result_le _ (Or.inl rfl), by intro _; simp⟩,
          atomCov_single atomCov_boolSing_class⟩
        simp only [typeOfE, hx']
        rw [if_pos h1]
      · by_cases h2 : (List.isEmpty (removeTy ps' objT)
            && !List.isEmpty ps') = Bool.true
        · refine ⟨[.isValue (.boolean Bool.false)], ?_,
            ⟨isObject_result_le _ (Or.inr (Or.inl rfl)), by intro _; simp⟩,
            atomCov_single atomCov_boolSing_class⟩
          simp only [typeOfE, hx']
          rw [if_neg h1, if_pos h2]
        · refine ⟨[.anyValue .bool], ?_, slotLe_refl _, tyCov_refl _ _⟩
          simp only [typeOfE, hx']
          rw [if_neg h1, if_neg h2]

  | case32 =>
      rename_i x hnone ih
      intro _ _ t ht
      simp only [typeOfE, hnone] at ht
      exact absurd ht (by simp)

  | case33 =>
      rename_i x hsame ih
      intro hle hcov t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle hcov sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .bool], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _, tyCov_refl _ _⟩

  | case34 =>
      rename_i x hnone ih
      intro _ _ t ht
      simp only [typeOfE] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case35 =>
      rename_i x hsame ih
      intro hle hcov t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle hcov sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .bool], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _, tyCov_refl _ _⟩

  | case36 =>
      rename_i x hnone ih
      intro _ _ t ht
      simp only [typeOfE] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case37 =>
      rename_i x hsame ih
      intro hle hcov t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle hcov sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .bool], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _, tyCov_refl _ _⟩

  | case38 =>
      rename_i x hnone ih
      intro _ _ t ht
      simp only [typeOfE] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case39 =>
      rename_i x hsame ih
      intro hle hcov t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle hcov sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .bool], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _, tyCov_refl _ _⟩

  | case40 =>
      rename_i x hnone ih
      intro _ _ t ht
      simp only [typeOfE] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case41 =>
      rename_i x hsame ih
      intro hle hcov t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle hcov sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .bool], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _, tyCov_refl _ _⟩

  | case42 =>
      rename_i x hnone ih
      intro _ _ t ht
      simp only [typeOfE] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case43 =>
      rename_i b x hsame ih
      intro hle hcov t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle hcov sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .bool], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _, tyCov_refl _ _⟩

  | case44 =>
      rename_i b x hnone ih
      intro _ _ t ht
      simp only [typeOfE] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case45 =>
      rename_i s x hsame ih
      intro hle hcov t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle hcov sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .bool], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _, tyCov_refl _ _⟩

  | case46 =>
      rename_i s x hnone ih
      intro _ _ t ht
      simp only [typeOfE] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case47 =>
      rename_i x hsame ih
      intro hle hcov t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle hcov sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .bool], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _, tyCov_refl _ _⟩

  | case48 =>
      rename_i x hnone ih
      intro _ _ t ht
      simp only [typeOfE] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case49 =>
      rename_i x hsame ih
      intro hle hcov t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle hcov sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .bool], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _, tyCov_refl _ _⟩

  | case50 =>
      rename_i x hnone ih
      intro _ _ t ht
      simp only [typeOfE] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case51 =>
      rename_i ty x hsame ih
      intro hle hcov t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle hcov sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .bool], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _, tyCov_refl _ _⟩

  | case52 =>
      rename_i ty x hnone ih
      intro _ _ t ht
      simp only [typeOfE] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case53 =>
      rename_i name x hsame ih
      intro hle hcov t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle hcov sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .bool], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _, tyCov_refl _ _⟩

  | case54 =>
      rename_i name x hnone ih
      intro _ _ t ht
      simp only [typeOfE] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)



/- ## Proof layer X: covariance of one machine step -/

theorem stackLe_take : ∀ {σ' σ : List Ty} (n : Nat),
    stackLe σ' σ → stackLe (σ'.take n) (σ.take n)
  | _, _, 0, _ => True.intro
  | [], [], _, _ => by simp only [List.take_nil]; exact True.intro
  | a' :: σ', a :: σ, n + 1, h => by
      obtain ⟨hslot, hrest⟩ := h
      exact ⟨hslot, stackLe_take n hrest⟩
termination_by σ' => sizeOf σ'
decreasing_by all_goals simp_wf <;> omega

theorem stackLe_drop : ∀ {σ' σ : List Ty} (n : Nat),
    stackLe σ' σ → stackLe (σ'.drop n) (σ.drop n)
  | _, _, 0, _ => by simpa using ‹_›
  | [], [], _, _ => by simp only [List.drop_nil]; exact True.intro
  | a' :: σ', a :: σ, n + 1, h => by
      obtain ⟨-, hrest⟩ := h
      exact stackLe_drop n hrest
termination_by σ' => sizeOf σ'
decreasing_by all_goals simp_wf <;> omega

theorem popTy_cov {T t' t : Ty} {σ' σ : List Ty}
    (hslot : slotLe t' t) (hrest : stackLe σ' σ) {σ0 : List Ty}
    (hp : popTy T (t :: σ) = some σ0) : popTy T (t' :: σ') = some σ' := by
  simp only [popTy] at hp ⊢
  cases hif : tmoves t T with
  | false => rw [hif] at hp; simp at hp
  | true =>
      rw [hif] at hp
      simp only [reduceIte, Option.some.injEq] at hp
      subst hp
      rw [if_pos (show tmoves t' T = Bool.true from
        tmoves_trans hslot.1 hif)]

/-- A one-slot pop that succeeds returns exactly the tail. -/
theorem popTy_cons_some_eq {T t : Ty} {σ r : List Ty}
    (hp : popTy T (t :: σ) = some r) : r = σ := by
  simp only [popTy] at hp
  cases hif : tmoves t T with
  | false => rw [hif] at hp; simp at hp
  | true =>
      rw [hif] at hp
      simp only [reduceIte, Option.some.injEq] at hp
      exact hp.symm

/-- Coverage forces the verdict of a covered slot. -/
theorem tyCov_tmoves {η : HeapCallableTy} {t' t T : Ty}
    (h : tyCov η t' t) (ht : tmoves t T = Bool.true) :
    tmoves t' T = Bool.true := by
  unfold tmoves at ht ⊢
  simp only [List.all_eq_true] at ht ⊢
  intro a' ha'
  obtain ⟨a, ha, hac⟩ := h a' ha'
  have h1 := atomCov_tmoves hac
  obtain ⟨b, hb, hab⟩ := List.any_eq_true.mp (ht a ha)
  exact List.any_eq_true.mpr ⟨b, hb, tmovesV_trans h1 hab⟩

theorem popTy_ty_cov {T t' t : Ty} {σ' σ : List Ty} {η : HeapCallableTy}
    (hcov : stackCov η (t' :: σ') (t :: σ))
    (hp : popTy T (t :: σ) = some σ) :
    popTy T (t' :: σ') = some σ' := by
  have hT : tmoves t T = Bool.true := by
    simp only [popTy] at hp
    cases hif : tmoves t T with
    | false => rw [hif] at hp; simp at hp
    | true => rfl
  have h1 := tyCov_tmoves hcov.1 hT
  simp only [popTy, h1, reduceIte]

theorem popTyN_ty_cov (n : Nat) : ∀ (T : Ty) {η : HeapCallableTy}
    {σ' σ σ0 : List Ty},
    stackCov η σ' σ → popTyN n T σ = some σ0 →
    ∃ σ0', popTyN n T σ' = some σ0' ∧ stackCov η σ0' σ0 := by
  induction n with
  | zero =>
      intro T η σ' σ σ0 hcov hp
      simp only [popTyN] at hp
      cases hp
      exact ⟨σ', rfl, hcov⟩
  | succ m ih =>
      intro T η σ' σ σ0 hcov hp
      cases σ with
      | nil =>
          cases σ' with
          | nil =>
              simp only [popTyN, popTy] at hp
              simp at hp
          | cons a' r' => exact absurd hcov (by simp [stackCov])
      | cons a r =>
          cases σ' with
          | nil => exact absurd hcov (by simp [stackCov])
          | cons a' r' =>
              obtain ⟨hslot1, hrest⟩ := hcov
              cases hpop : popTy T (a :: r) with
              | none => simp only [popTyN, hpop] at hp; simp at hp
              | some mid =>
                  have hmr : mid = r := popTy_cons_some_eq hpop
                  subst hmr
                  have hpop' : popTy T (a' :: r') = some r' :=
                    popTy_ty_cov (η := η) ⟨hslot1, hrest⟩ hpop
                  simp only [popTyN, hpop, reduceIte] at hp
                  obtain ⟨mid', hp', hle'⟩ := ih T hrest hp
                  exact ⟨mid', by
                    simp only [popTyN, hpop', hp', reduceIte], hle'⟩

/-- Characterize a successful unwrap: the payloads are exactly the
    complN atoms of the slot (order aside). -/
theorem unwrapSlot_char : ∀ (t ps : Ty), unwrapSlot t = some ps →
    (∀ p ∈ ps, VTy.complN p ∈ t) ∧
    (∀ c ∈ t, ∃ q, c = VTy.complN q ∧ q ∈ ps)
  | [], ps, hu => by
      simp only [unwrapSlot, Option.some.injEq] at hu
      subst hu
      exact ⟨(by intro p hp; cases hp), (by intro c hc; cases hc)⟩
  | .complN p :: r, ps, hu => by
      simp only [unwrapSlot] at hu
      cases hr : unwrapSlot r with
      | none => rw [hr] at hu; simp at hu
      | some rs =>
          rw [hr, Option.map_some, Option.some.injEq] at hu
          subst hu
          obtain ⟨ih1, ih2⟩ := unwrapSlot_char r rs hr
          constructor
          · intro q hq
            simp only [List.mem_cons] at hq
            rcases hq with hq | hq
            · subst hq; exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (ih1 q hq)
          · intro c hc
            simp only [List.mem_cons] at hc
            rcases hc with hc | hc
            · subst hc
              exact ⟨p, rfl, by simp⟩
            · obtain ⟨q, hq1, hq2⟩ := ih2 c hc
              exact ⟨q, hq1, by simp [hq2]⟩
  | .complT :: r, ps, hu => by simp only [unwrapSlot] at hu; contradiction
  | .anyValue c :: r, ps, hu => by simp only [unwrapSlot] at hu; contradiction
  | .isValue v :: r, ps, hu => by simp only [unwrapSlot] at hu; contradiction
  | .desc fs :: r, ps, hu => by simp only [unwrapSlot] at hu; contradiction
  | .notPresent :: r, ps, hu => by simp only [unwrapSlot] at hu; contradiction

/-- A failed unwrap on a nonempty slot leaves a non-complN atom. -/
theorem unwrapSlot_none_mem : ∀ (t : Ty), unwrapSlot t = none → t ≠ [] →
    ∃ c ∈ t, ∀ q, c ≠ VTy.complN q
  | [], hu, _ => by simp [unwrapSlot] at hu
  | .complN p :: r, hu, _ => by
      simp only [unwrapSlot, Option.map_eq_none_iff] at hu
      obtain ⟨c, hc, hcc⟩ := unwrapSlot_none_mem r hu (by
        intro hc2
        rw [hc2] at hu
        simp [unwrapSlot] at hu)
      exact ⟨c, by simp [hc], hcc⟩
  | .complT :: r, _, _ => ⟨.complT, by simp, by intro q hq; exact VTy.noConfusion hq⟩
  | .anyValue c :: r, _, _ => ⟨.anyValue c, by simp, by intro q hq; exact VTy.noConfusion hq⟩
  | .isValue v :: r, _, _ => ⟨.isValue v, by simp, by intro q hq; exact VTy.noConfusion hq⟩
  | .desc fs :: r, _, _ => ⟨.desc fs, by simp, by intro q hq; exact VTy.noConfusion hq⟩
  | .notPresent :: r, _, _ => ⟨.notPresent, by simp, by intro q hq; exact VTy.noConfusion hq⟩

/-- payloadsOf agrees with a successful unwrapSlot. -/
theorem payloadsOf_eq_unwrap : ∀ (t ps : Ty), unwrapSlot t = some ps →
    payloadsOf t = ps
  | [], ps, hu => by
      simp only [unwrapSlot, Option.some.injEq] at hu
      subst hu
      rfl
  | .complN p :: r, ps, hu => by
      simp only [unwrapSlot] at hu
      cases hr : unwrapSlot r with
      | none => rw [hr] at hu; simp at hu
      | some rs =>
          rw [hr, Option.map_some, Option.some.injEq] at hu
          subst hu
          show payloadsOf (VTy.complN p :: r) = p :: rs
          have := payloadsOf_eq_unwrap r rs hr
          unfold payloadsOf at this ⊢
          simp only [List.flatMap_cons]
          rw [this]
          simp
  | .complT :: r, ps, hu => by simp only [unwrapSlot] at hu; contradiction
  | .anyValue c :: r, ps, hu => by simp only [unwrapSlot] at hu; contradiction
  | .isValue v :: r, ps, hu => by simp only [unwrapSlot] at hu; contradiction
  | .desc fs :: r, ps, hu => by simp only [unwrapSlot] at hu; contradiction
  | .notPresent :: r, ps, hu => by simp only [unwrapSlot] at hu; contradiction

/-- Unwrapping preserves coverage (payloads through the complN
    recursion). -/
theorem unwrapSlot_ty_cov {η : HeapCallableTy} {t' t : Ty}
    (h : tyCov η t' t) {ps : Ty}
    (hu : unwrapSlot t = some ps) :
    ∃ ps', unwrapSlot t' = some ps' ∧ tyCov η ps' ps := by
  obtain ⟨c1, c2⟩ := unwrapSlot_char t ps hu
  cases ht' : unwrapSlot t' with
  | none =>
      cases t' with
      | nil => exact absurd ht' (by simp [unwrapSlot])
      | cons a r =>
          exfalso
          obtain ⟨c, hcm, hcc⟩ := unwrapSlot_none_mem (a :: r) ht' (by simp)
          obtain ⟨b, hb, hac⟩ := h c hcm
          obtain ⟨q, hq, -⟩ := c2 b hb
          rw [hq] at hac
          have h1 := atomCov_tmoves hac
          cases c with
          | complN p => exact absurd rfl (hcc p)
          | complT | anyValue _ | isValue _ | desc _ | notPresent =>
              simp [tmovesV] at h1
  | some ps' =>
      refine ⟨ps', rfl, ?_⟩
      obtain ⟨c1', -⟩ := unwrapSlot_char t' ps' ht'
      intro x hx
      have hxmem : VTy.complN x ∈ t' := c1' x hx
      obtain ⟨b, hb, hac⟩ := h _ hxmem
      obtain ⟨q, hq, hqmem⟩ := c2 b hb
      rw [hq] at hac
      have hq' : q ∈ ps := by
        obtain ⟨q2, hq2, hq2m⟩ := c2 (VTy.complN q) (hq ▸ hb)
        cases hq2
        exact hq2m
      exact ⟨q, hq', atomCov_pay hac⟩

theorem popAObj_cons_eq {t : Ty} {σ σ2 : List Ty}
    (hp : popAObj (t :: σ) = some σ2) : σ2 = σ := by
  unfold popAObj popA at hp
  cases h1 : popTy [.anyValue (.obj Bool.true)] (t :: σ) with
  | some σ0 =>
      rw [h1] at hp
      have h2 : (some σ0 : Option _) = some σ2 := hp
      injection h2 with h2
      have h0 : σ0 = σ := popTy_cons_some_eq h1
      exact h2.symm.trans h0
  | none =>
      rw [h1] at hp
      have h2 : popTy [.anyValue (.obj Bool.false)] (t :: σ) = some σ2 := hp
      exact popTy_cons_some_eq h2

/-- Object pops are covariant: a refined stack below a successful
    object pop also pops, to the same tail. -/
theorem popAObj_cov {t' t : Ty} {σ' σ : List Ty}
    (hslot : slotLe t' t) (hrest : stackLe σ' σ)
    (hp : popAObj (t :: σ) = some σ) : popAObj (t' :: σ') = some σ' := by
  have main : ∀ (b : Bool),
      popTy [.anyValue (.obj b)] (t :: σ) = some σ →
      popTy [.anyValue (.obj b)] (t' :: σ') = some σ' :=
    fun _ hb => popTy_cov hslot hrest hb
  unfold popAObj popA at hp ⊢
  cases h1 : popTy [.anyValue (.obj Bool.true)] (t :: σ) with
  | some σ0 =>
      rw [h1] at hp
      have h2 : (some σ0 : Option _) = some σ := hp
      injection h2 with h2
      have h0 : σ0 = σ := popTy_cons_some_eq h1
      rw [h0] at h1
      rw [main Bool.true h1]
      rfl
  | none =>
      rw [h1] at hp
      have h2 : popTy [.anyValue (.obj Bool.false)] (t :: σ) = some σ := hp
      cases h1' : popTy [.anyValue (.obj Bool.true)] (t' :: σ') with
      | some r => exact congrArg some (popTy_cons_some_eq h1')
      | none =>
          rw [main Bool.false h2]
          rfl


theorem popTyN_cov (n : Nat) : ∀ (T : Ty) {σ' σ σ0 : List Ty},
    stackLe σ' σ → popTyN n T σ = some σ0 →
    ∃ σ0', popTyN n T σ' = some σ0' ∧ stackLe σ0' σ0 := by
  induction n with
  | zero =>
      intro T σ' σ σ0 h hp
      simp only [popTyN] at hp
      cases hp
      exact ⟨σ', rfl, h⟩
  | succ m ih =>
      intro T σ' σ σ0 h hp
      cases σ with
      | nil =>
          cases σ' with
          | nil =>
              simp only [popTyN, popTy] at hp
              simp at hp
          | cons a' r' => exact absurd h (by simp [stackLe])
      | cons a r =>
          cases σ' with
          | nil => exact absurd h (by simp [stackLe])
          | cons a' r' =>
              obtain ⟨hslot, hrest⟩ := h
              cases hpop : tmoves a T with
              | false =>
                  simp only [popTyN, popTy, hpop, reduceIte] at hp
                  simp at hp
              | true =>
                  have haT : tmoves a' T = Bool.true := tmoves_trans hslot.1 hpop
                  simp only [popTyN, popTy, hpop, reduceIte] at hp
                  simp only [popTyN, popTy, haT, reduceIte] at ⊢
                  obtain ⟨σ0', hp', hle'⟩ := ih T hrest hp
                  exact ⟨σ0', hp', hle'⟩

theorem stackLe_slotsLe : ∀ {σ' σ : List Ty}, stackLe σ' σ →
    slotsLe σ' σ
  | [], [], _ => True.intro
  | a' :: σ', a :: σ, h => by
      obtain ⟨h1, h2⟩ := h
      exact ⟨h1, stackLe_slotsLe h2⟩

theorem stackLe_length : ∀ {σ' σ : List Ty}, stackLe σ' σ →
    σ'.length = σ.length
  | [], [], _ => rfl
  | a' :: σ', a :: σ, h => by
      obtain ⟨-, hrest⟩ := h
      rw [List.length_cons, List.length_cons, stackLe_length hrest]

theorem stackLe_append : ∀ {a' a b' b : List Ty},
    stackLe a' a → stackLe b' b → stackLe (a' ++ b') (a ++ b)
  | [], [], b', b, _, hb => hb
  | a1 :: ar, b1 :: br, b', b, ha, hb => ⟨ha.1, stackLe_append ha.2 hb⟩
  | [], _ :: _, _, _, h, _ => absurd h (by simp [stackLe])
  | _ :: _, [], _, _, h, _ => absurd h (by simp [stackLe])

theorem stackLe_reverse : ∀ {σ' σ : List Ty}, stackLe σ' σ →
    stackLe σ'.reverse σ.reverse
  | [], [], _ => True.intro
  | a' :: σ', a :: σ, h => by
      obtain ⟨h1, h2⟩ := h
      rw [List.reverse_cons, List.reverse_cons]
      exact stackLe_append (stackLe_reverse h2) ⟨h1, True.intro⟩

theorem popArgs_cov {ps : List Ty} {σ' σ : List Ty}
    (h : stackLe σ' σ) (hp : popArgs ps σ = Bool.true) :
    popArgs ps σ' = Bool.true := by
  simp only [popArgs] at hp ⊢
  rw [Bool.and_eq_true] at hp
  obtain ⟨hlen, hle⟩ := hp
  have hge : σ.length ≥ ps.length := of_decide_eq_true hlen
  have hlen' : σ'.length = σ.length := stackLe_length h
  refine (Bool.and_eq_true _ _) |>.mpr ⟨?_, ?_⟩
  · simp only [decide_eq_true_eq, ge_iff_le]
    omega
  · exact leTy_cov
        (stackLe_slotsLe (stackLe_reverse (stackLe_take ps.length h))) hle

theorem bareSlot_pure : ∀ (t wt : Ty), bareSlot t = some wt →
    ∀ a ∈ t, isBareVTy a = Bool.true := by
  intro t
  induction t with
  | nil => intro wt hb a ha; cases ha
  | cons b rest ih =>
      intro wt hb a ha
      simp only [bareSlot] at hb
      cases hib : isBareVTy b with
      | false => rw [hib] at hb; simp at hb
      | true =>
          rw [hib] at hb
          cases hrest : bareSlot rest with
          | none => rw [hrest] at hb; simp at hb
          | some rs =>
              rw [hrest] at hb
              simp only [Option.map_some, Option.some.injEq] at hb
              subst hb
              match List.mem_cons.mp ha with
              | Or.inl he => rw [he]; exact hib
              | Or.inr hr => exact ih rs hrest a hr

theorem bareSlot_eq_self : ∀ (t : Ty), (∀ a ∈ t, isBareVTy a = Bool.true) →
    bareSlot t = some t
  | [], _ => rfl
  | a :: rest, hp => by
      have hrest : ∀ x ∈ rest, isBareVTy x = Bool.true :=
        fun x hx => hp x (List.mem_cons_of_mem _ hx)
      simp only [bareSlot, hp a (List.mem_cons_self ..),
        bareSlot_eq_self rest hrest]
      rfl

theorem bareSlot_cov {t' t : Ty} (h : slotLe t' t) {wt : Ty}
    (hb : bareSlot t = some wt) :
    bareSlot t' = some t' ∧ slotLe (t'.map VTy.complN) (wt.map VTy.complN) := by
  have hpure := bareSlot_pure t wt hb
  have hpure' : ∀ a' ∈ t', isBareVTy a' = Bool.true := by
    intro a' ha'
    obtain ⟨a, ha, haa⟩ := tyLe_cov_atoms h.1 a' ha'
    exact isBareVTy_of_cover (hpure a ha) haa
  have hwt : wt = t := by
    have hs := bareSlot_eq_self t hpure
    rw [hs] at hb
    simp only [Option.some.injEq] at hb
    exact hb.symm
  subst hwt
  exact ⟨bareSlot_eq_self t' hpure', complN_map_cov h⟩

theorem unwrapSlot_pure : ∀ (t ps : Ty), unwrapSlot t = some ps →
    ∀ a ∈ t, ∃ p, a = .complN p := by
  intro t
  induction t with
  | nil => intro ps hu a ha; cases ha
  | cons b rest ih =>
      intro ps hu a ha
      cases b with
      | complN p =>
          rw [show unwrapSlot (VTy.complN p :: rest) =
            Option.map (fun ps => p :: ps) (unwrapSlot rest) from rfl] at hu
          cases hrest : unwrapSlot rest with
          | none =>
              rw [hrest] at hu
              have hnone : none = some ps := hu
              cases hnone
          | some rs =>
              rw [hrest] at hu
              simp only [Option.map_some, Option.some.injEq] at hu
              match List.mem_cons.mp ha with
              | Or.inl he => exact ⟨p, he⟩
              | Or.inr hr => exact ih rs hrest a hr
      | complT | anyValue _ | isValue _ | desc _ | notPresent =>
          simp only [unwrapSlot] at hu
          simp at hu

theorem unwrapSlot_eq {t ps : Ty} (hu : unwrapSlot t = some ps) :
    ps = payloadsOf t := by
  induction t generalizing ps with
  | nil =>
      simp only [unwrapSlot, payloadsOf] at hu ⊢
      simp only [Option.some.injEq] at hu
      exact hu.symm
  | cons b rest ih =>
      cases b with
      | complN p =>
          rw [show unwrapSlot (VTy.complN p :: rest) =
            Option.map (fun ps => p :: ps) (unwrapSlot rest) from rfl] at hu
          cases hrest : unwrapSlot rest with
          | none =>
              rw [hrest] at hu
              have hnone : none = some ps := hu
              cases hnone
          | some rs =>
              rw [hrest] at hu
              simp only [Option.map_some, Option.some.injEq] at hu
              subst hu
              simp only [payloadsOf, List.flatMap_cons]
              congr 1
              exact ih hrest
      | complT | anyValue _ | isValue _ | desc _ | notPresent =>
          simp only [unwrapSlot] at hu
          simp at hu

theorem unwrapSlot_eq_self : ∀ (t : Ty), (∀ a ∈ t, ∃ p, a = .complN p) →
    unwrapSlot t = some (payloadsOf t)
  | [], _ => rfl
  | a :: rest, hp => by
      cases a with
      | complN p =>
          have hrest := unwrapSlot_eq_self rest
            (fun x hx => hp x (List.mem_cons_of_mem _ hx))
          rw [show unwrapSlot (VTy.complN p :: rest) =
            Option.map (fun ps => p :: ps) (unwrapSlot rest) from rfl, hrest]
          simp [payloadsOf]
      | complT | anyValue _ | isValue _ | desc _ | notPresent =>
          obtain ⟨q, hq⟩ := hp _ (List.mem_cons_self ..)
          exact VTy.noConfusion hq

theorem unwrapSlot_cov {t' t : Ty} (h : slotLe t' t) {ps : Ty}
    (hu : unwrapSlot t = some ps) :
    unwrapSlot t' = some (payloadsOf t') ∧ slotLe (payloadsOf t') ps := by
  have hpure := unwrapSlot_pure t ps hu
  have hps : ps = payloadsOf t := unwrapSlot_eq hu
  subst hps
  have hpure' : ∀ a' ∈ t', ∃ p, a' = .complN p := by
    intro a' ha'
    obtain ⟨a, ha, haa⟩ := tyLe_cov_atoms h.1 a' ha'
    obtain ⟨q, hq⟩ := hpure a ha
    rw [hq] at haa
    cases a' with
    | complN p' => exact ⟨p', rfl⟩
    | complT | anyValue _ | isValue _ | desc _ | notPresent =>
        simp [tmovesV] at haa
  have heq' : unwrapSlot t' = some (payloadsOf t') :=
    unwrapSlot_eq_self t' hpure'
  refine ⟨heq', ?_, ?_⟩
  · unfold tyLe tmoves
    simp only [List.all_eq_true, List.any_eq_true]
    exact payloadsOf_cov (tyLe_cov_atoms h.1)
  · intro hpsne
    have hne : t ≠ [] := by
      intro hc
      subst hc
      simp only [payloadsOf, List.flatMap_nil] at hpsne
      exact hpsne rfl
    have hne' : t' ≠ [] := h.2 hne
    exact payloadsOf_ne hne' hpure'


/- ## Proof layer XI: meet/remove/completion-kind covariance (the
    split sites' lattice behavior). The atom-cover (∀∃) interface:
    refined split outputs are covered by coarse split outputs. -/

theorem tyLe_of_atom_cov {t' t : Ty}
    (h : ∀ a' ∈ t', ∃ a ∈ t, tmovesV a' a = Bool.true) : tyLe t' t := by
  unfold tyLe tmoves
  simp only [List.all_eq_true, List.any_eq_true]
  exact h


/-- The three stubborn meetAtom combos, as standalone lemmas in
    ORIGINAL form (for exact-wiring into the grid). -/

theorem meetAtom_le_left : ∀ a b m, meetAtom a b = some m →
    tmovesV m a = Bool.true := by
  intro a b m h
  cases b with
  | complN q | complT =>
      simp only [meetAtom] at h
      exact absurd h (by simp)
  | notPresent | anyValue c2 | isValue w | desc fs2 =>
      cases a <;>
        simp only [meetAtom, tmovesV, beq_iff_eq, decide_eq_true_eq,
          Option.some.injEq] at h ⊢ <;>
        (try split at h) <;>
        simp_all [tmovesV_refl, tagOf] <;>
        first
        | rfl
        | (next htag => subst h; exact decide_eq_true htag)
        | (subst h; simp [tmovesV])
        | (subst h; exact tmovesV_refl _)

theorem meetTy_le_left (S T : Ty) : tyLe (meetTy S T) S := by
  unfold tyLe tmoves meetTy
  simp only [List.all_eq_true]
  intro m hm
  simp only [List.mem_flatMap] at hm
  obtain ⟨a, ha, ⟨b, hb, hm⟩⟩ := hm
  cases hma : meetAtom a b with
  | none => simp [hma] at hm
  | some m' =>
      simp only [hma, List.mem_singleton] at hm
      subst hm
      apply List.any_eq_true.mpr
      exact ⟨a, ha, meetAtom_le_left a b _ hma⟩

theorem removeAtom_le_left : ∀ a T a', a' ∈ removeAtom a T →
    tmovesV a' a = Bool.true := by
  intro a T a' h
  simp only [removeAtom] at h
  by_cases hd : T.any (fun b => tmovesV a b) = Bool.true
  · rw [if_pos hd] at h; cases h
  · rw [if_neg hd] at h
    cases a with
    | anyValue c =>
        cases c with
        | bool =>
            simp only [isBoolClass] at h
            repeat' split at h
            all_goals simp_all [isBoolSing, tmovesV] <;>
              first | rfl | simp [tagOf] | exact tmovesV_refl _
        | undef | null | num | str | obj b | list | desc =>
            simp only [isBoolClass] at h
            simp at h
            subst h
            exact tmovesV_refl _
    | complN p | complT | isValue v | desc fs | notPresent =>
        simp only [isBoolClass] at h
        simp at h
        subst h
        exact tmovesV_refl _

theorem removeTy_le_left (S T : Ty) : tyLe (removeTy S T) S := by
  unfold tyLe tmoves removeTy
  simp only [List.all_eq_true]
  intro a' ha'
  simp only [List.mem_flatMap] at ha'
  obtain ⟨a, ha, hmem⟩ := ha'
  apply List.any_eq_true.mpr
  exact ⟨a, ha, removeAtom_le_left a T a' hmem⟩

theorem meetAtom_cov_aad {c1 c2 : Ctor} {fs : List Field} {m' : VTy}
    (hcov : tmovesV (VTy.desc fs) (VTy.anyValue c1) = Bool.true)
    (hm' : meetAtom (VTy.desc fs) (VTy.anyValue c2) = some m') :
    ∃ m, meetAtom (VTy.anyValue c1) (VTy.anyValue c2) = some m
      ∧ tmovesV m' m = Bool.true := by
  cases c1 with
  | desc =>
      cases c2 with
      | desc =>
          simp only [meetAtom, Option.some.injEq] at hm'
          subst hm'
          exact ⟨.anyValue Ctor.desc, rfl, by simp [tmovesV]⟩
      | undef | null | bool | num | str | obj _ | list =>
          exact absurd hm' (by simp [meetAtom])
  | undef | null | bool | num | str | obj _ | list =>
      exact absurd hcov (by simp [tmovesV])

theorem meetAtom_cov_aai {c1 c2 : Ctor} {v : JSValue} {m' : VTy}
    (hcov : tmovesV (VTy.isValue v) (VTy.anyValue c1) = Bool.true)
    (hm' : meetAtom (VTy.isValue v) (VTy.anyValue c2) = some m') :
    ∃ m, meetAtom (VTy.anyValue c1) (VTy.anyValue c2) = some m
      ∧ tmovesV m' m = Bool.true := by
  simp only [meetAtom, tmovesV] at hm' hcov ⊢
  split at hm'
  · next hcond =>
      have h1 : tagOf v = c1 := of_decide_eq_true hcov
      simp only [Option.some.injEq] at hm'
      subst hm'
      refine ⟨VTy.anyValue c1, ?_, ?_⟩
      · rw [if_pos (show c1 = c2 from h1.symm.trans hcond)]
      · exact decide_eq_true h1
  · exact absurd hm' (by simp)

theorem meetAtom_cov_dad {fs2 : List Field} {c : Ctor} {fs : List Field} {m' : VTy}
    (hcov : tmovesV (VTy.desc fs) (VTy.anyValue c) = Bool.true)
    (hm' : meetAtom (VTy.desc fs) (VTy.desc fs2) = some m') :
    ∃ m, meetAtom (VTy.anyValue c) (VTy.desc fs2) = some m
      ∧ tmovesV m' m = Bool.true := by
  simp only [meetAtom, tmovesV] at hm' hcov ⊢
  split at hm'
  · next hcond =>
      simp only [Option.some.injEq] at hm'
      subst hm'
      cases c <;> simp_all [meetAtom, tmovesV, tmovesV_refl]
  · exact absurd hm' (by simp)

theorem meetAtom_cov_iii {v v' w : JSValue} {m' : VTy}
    (hcov : tmovesV (VTy.isValue v') (VTy.isValue v) = Bool.true)
    (hm' : meetAtom (VTy.isValue v') (VTy.isValue w) = some m') :
    ∃ m, meetAtom (VTy.isValue v) (VTy.isValue w) = some m
      ∧ tmovesV m' m = Bool.true := by
  simp only [meetAtom, tmovesV, beq_iff_eq, decide_eq_true_eq,
    Option.some.injEq] at hm' hcov ⊢
  split at hm'
  · next hcond =>
      simp only [Option.some.injEq] at hm'
      subst hm'
      refine ⟨VTy.isValue v, ?_, ?_⟩
      · rw [if_pos (show (v == w) = Bool.true by
          rw [← hcov]
          exact hcond)]
      · simp [tmovesV, hcov]
  · exact absurd hm' (by simp)

theorem meetAtom_cov_iai {c : Ctor} {v w : JSValue} {m' : VTy}
    (hcov : tmovesV (VTy.isValue v) (VTy.anyValue c) = Bool.true)
    (hm' : meetAtom (VTy.isValue v) (VTy.isValue w) = some m') :
    ∃ m, meetAtom (VTy.anyValue c) (VTy.isValue w) = some m
      ∧ tmovesV m' m = Bool.true := by
  simp only [meetAtom, tmovesV] at hm' hcov ⊢
  split at hm'
  · next hcond =>
      have h1 : tagOf v = c := of_decide_eq_true hcov
      have h2 : v = w := by simpa [beq_iff_eq] using hcond
      simp only [Option.some.injEq] at hm'
      subst hm'
      refine ⟨VTy.isValue w, ?_, ?_⟩
      · rw [if_pos (show (tagOf w = c) from h2 ▸ h1)]
      · rw [h2]
        exact tmovesV_refl _
  · exact absurd hm' (by simp)

set_option maxHeartbeats 4000000 in
theorem meetAtom_cov {a' a b : VTy} (hcov : tmovesV a' a = Bool.true) {m' : VTy}
    (hm' : meetAtom a' b = some m') :
    ∃ m, meetAtom a b = some m ∧ tmovesV m' m = Bool.true := by
  cases b with
  | complN q | complT =>
      simp only [meetAtom] at hm'
      exact absurd hm' (by simp)
  | notPresent =>
      cases a <;> cases a' <;>
        first
        | (simp only [meetAtom, tmovesV, beq_iff_eq, decide_eq_true_eq,
            Option.some.injEq] at hm' hcov ⊢
           simp_all [tmovesV_refl])
  | anyValue c2 =>
      cases a <;> cases a' <;>
        first
        | exact meetAtom_cov_aai hcov hm'
        | exact meetAtom_cov_aad hcov hm'
        | (simp only [meetAtom, tmovesV, beq_iff_eq, decide_eq_true_eq,
            Option.some.injEq] at hm' hcov ⊢
           simp_all [tmovesV_refl])
  | isValue w =>
      cases a <;> cases a' <;>
        first
        | exact meetAtom_cov_iii hcov hm'
        | exact meetAtom_cov_iai hcov hm'
        | (simp only [meetAtom, tmovesV, beq_iff_eq, decide_eq_true_eq,
            Option.some.injEq] at hm' hcov ⊢
           simp_all [tmovesV_refl])
  | desc fs2 =>
      cases a <;> cases a' <;>
        first
        | exact meetAtom_cov_dad hcov hm'
        | (simp only [meetAtom, tmovesV, beq_iff_eq, decide_eq_true_eq,
            Option.some.injEq] at hm' hcov ⊢
           simp_all [tmovesV_refl])

theorem meetTy_cov {S' S T : Ty}
    (hcov : ∀ a' ∈ S', ∃ a ∈ S, tmovesV a' a = Bool.true) :
    ∀ m' ∈ meetTy S' T, ∃ m ∈ meetTy S T, tmovesV m' m = Bool.true := by
  intro m' hm'
  simp only [meetTy, List.mem_flatMap] at hm' ⊢
  obtain ⟨a', ha', b, hb, hmem⟩ := hm'
  cases hmeet : meetAtom a' b with
  | none =>
      exfalso
      rw [hmeet] at hmem
      cases hmem
  | some w =>
      rw [hmeet] at hmem
      have hwm : m' = w := by simpa using hmem
      subst hwm
      obtain ⟨a, ha, haa⟩ := hcov _ ha'
      obtain ⟨m, hm, hcover⟩ := meetAtom_cov haa hmeet
      refine ⟨m, ⟨a, ha, ⟨b, hb, ?_⟩⟩, hcover⟩
      rw [hm]
      exact List.mem_singleton.mpr rfl

/- ## Proof layer XII preamble: slot purity.

    kTest covariance needs the coarse slot to be pure-completion:
    every push in the checker is pure (complTy/completionOf push
    pure-completion slots; all other pushes are pure-bare), and
    purity is inherited downward under slotLe. -/

def slotCompl (t : Ty) : Prop :=
  ∀ a ∈ t, (∃ p, a = .complN p) ∨ a = .complT

theorem slotCompl_of_cover {t' t : Ty} (h : slotLe t' t)
    (ht : slotCompl t) : slotCompl t' := by
  intro a' ha'
  obtain ⟨a, ha, haa⟩ := tyLe_cov_atoms h.1 a' ha'
  obtain ⟨p, hp⟩ | ht2 := ht a ha
  · cases a' with
    | complN p' => exact Or.inl ⟨p', rfl⟩
    | complT => simp [tmovesV, hp] at haa
    | anyValue _ | isValue _ | desc _ | notPresent => simp [tmovesV, hp] at haa
  · cases a' with
    | complT => exact Or.inr rfl
    | complN p => exact Or.inl ⟨p, rfl⟩
    | anyValue _ | isValue _ | desc _ | notPresent => simp [tmovesV, ht2] at haa

theorem complTy_compl : ∀ (cs : List Pending), slotCompl (complTy cs)
  | [] => by
      intro a ha
      simp only [complTy, List.filterMap_nil, List.flatten_nil,
        List.append_nil, complCanThrow, List.any_nil, Bool.or_false,
        if_false] at ha
      cases ha
  | c :: rest => by
      intro a ha
      have ih := complTy_compl rest
      cases c with
      | normal t =>
          simp only [complTy, List.filterMap_cons, List.flatten_cons] at ha
          rcases List.mem_append.mp ha with h1 | h2
          · rcases List.mem_append.mp h1 with h3 | h4
            · simp only [List.mem_map] at h3
              obtain ⟨p, -, hpa⟩ := h3
              exact Or.inl ⟨p, hpa.symm⟩
            · exact ih a (List.mem_append.mpr (Or.inl h4))
          · exact ih a (List.mem_append.mpr (Or.inr h2))
      | throw =>
          simp only [complTy, List.filterMap_cons, List.flatten_cons,
            complCanThrow, List.any_cons, Bool.true_or, if_true] at ha
          rcases List.mem_append.mp ha with h1 | h2
          · exact ih a (List.mem_append.mpr (Or.inl h1))
          · simp only [List.mem_singleton] at h2
            exact Or.inr h2

theorem complOnly_of_compl {t : Ty} (ht : slotCompl t) :
    complOnly t = Bool.true := by
  induction t with
  | nil => rfl
  | cons a rest ih =>
      simp only [complOnly, Bool.and_eq_true]
      refine ⟨?_, ih (fun b hb => ht b (List.mem_cons_of_mem _ hb))⟩
      obtain ⟨p, hp⟩ | ht2 := ht a (List.mem_cons_self ..)
      · subst hp; rfl
      · subst ht2; rfl

theorem complOnly_compl {t : Ty} (h : complOnly t = Bool.true) :
    slotCompl t := by
  induction t with
  | nil => intro a ha; cases ha
  | cons a rest ih =>
      intro b hb
      simp only [complOnly, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      cases a with
      | complN p =>
          rcases List.mem_cons.mp hb with he | hr
          · rw [he]; exact Or.inl ⟨p, rfl⟩
          · exact ih h2 b hr
      | complT =>
          rcases List.mem_cons.mp hb with he | hr
          · rw [he]; exact Or.inr rfl
          · exact ih h2 b hr
      | anyValue _ | isValue _ | desc _ | notPresent => simp at h1

theorem slotCompl_side {t : Ty} (ht : slotCompl t) (hne : t ≠ []) :
    complNormals t ≠ [] ∨ complHasThrow t = Bool.true := by
  cases t with
  | nil => exact absurd rfl hne
  | cons a rest =>
      obtain ⟨p, hp⟩ | ht2 := ht a (List.mem_cons_self ..)
      · subst hp
        exact Or.inl (fun hc => absurd hc (by simp [complNormals]))
      · subst ht2
        exact Or.inr (by
          simp only [complHasThrow, List.any_cons, Bool.true_or])

/-- removeAtom is covariant: any atom surviving the refined atom's
    removal is covered by an atom surviving the coarse atom's
    removal. -/
theorem removeAtom_cov {a' a : VTy} (haa : tmovesV a' a = Bool.true)
    (T : Ty) : ∀ x' ∈ removeAtom a' T,
    ∃ x ∈ removeAtom a T, tmovesV x' x = Bool.true := by
  intro x' hx'
  cases hf' : T.any (fun c => tmovesV a' c) with
  | true =>
      simp only [removeAtom, hf', reduceIte] at hx'
      cases hx'
  | false =>
      have hbf : T.any (fun c => tmovesV a c) = Bool.false := by
        cases hbf : T.any (fun c => tmovesV a c) with
        | true =>
            exfalso
            obtain ⟨c, hc1, hc2⟩ := List.any_eq_true.mp hbf
            rw [List.any_eq_true.mpr ⟨c, hc1, tmovesV_trans haa hc2⟩]
              at hf'
            exact Bool.noConfusion hf'
        | false => rfl
      cases hb'eq : isBoolClass a' with
      | true =>
          -- a' IS the bool class; only the class covers it
          have ha'cl : a' = .anyValue .bool := isBoolClass_inv hb'eq
          rw [ha'cl] at haa hx'
          have hbl : a = .anyValue .bool := boolClass_cover haa
          rw [hbl]
          exact ⟨x', hx', tmovesV_refl _⟩
      | false =>
          simp only [removeAtom, hf', hb'eq] at hx'
          simp at hx'
          obtain rfl : x' = a' := hx'
          cases hbeq : isBoolClass a with
          | false =>
              refine ⟨a, ?_, haa⟩
              simp only [removeAtom, hbf, hbeq] at ⊢
              simp
          | true =>
              -- a = the bool class; a' is one of its singletons
              have hbl : a = .anyValue .bool := isBoolClass_inv hbeq
              rw [hbl] at haa hbf ⊢
              rcases covers_boolClass haa with rfl | rfl | rfl
              · exact absurd hb'eq (by simp [isBoolClass])
              · -- a' = the TRUE singleton; its presence in T would
                -- have filtered a' (hf'), so the puncture keeps it
                by_cases hc : T.any (isBoolSing Bool.true) = Bool.true
                · exfalso
                  rw [List.any_eq_true.mpr ⟨_, T_has_sing T Bool.true hc,
                    tmovesV_refl _⟩] at hf'
                  exact Bool.noConfusion hf'
                · -- puncture of the class: hasFalse → [TRUE-sing],
                  -- else the class itself; both cover TRUE-sing
                  by_cases h2 : T.any (isBoolSing Bool.false) = Bool.true
                  · refine ⟨VTy.isValue (.boolean Bool.true), ?_,
                      tmovesV_refl _⟩
                    have hc2 : ¬((T.any (isBoolSing Bool.true)
                        && T.any (isBoolSing Bool.false))
                        = Bool.true) := by
                      intro hcc
                      rw [Bool.and_eq_true] at hcc
                      exact hc hcc.1
                    simp only [removeAtom]
                    rw [if_neg (by rw [hbf]; exact fun h => Bool.noConfusion h),
                      if_pos isBoolClass_reduce, if_neg hc2, if_neg hc,
                      if_pos h2]
                    exact List.mem_singleton.mpr rfl
                  · refine ⟨.anyValue .bool, ?_, haa⟩
                    have hc2 : ¬((T.any (isBoolSing Bool.true)
                        && T.any (isBoolSing Bool.false))
                        = Bool.true) := by
                      intro hcc
                      rw [Bool.and_eq_true] at hcc
                      exact hc hcc.1
                    simp only [removeAtom]
                    rw [if_neg (by rw [hbf]; exact fun h => Bool.noConfusion h),
                      if_pos isBoolClass_reduce, if_neg hc2, if_neg hc,
                      if_neg h2]
                    exact List.mem_singleton.mpr rfl
              · -- a' = the FALSE singleton; symmetric
                by_cases hc : T.any (isBoolSing Bool.false) = Bool.true
                · exfalso
                  rw [List.any_eq_true.mpr ⟨_, T_has_sing T Bool.false hc,
                    tmovesV_refl _⟩] at hf'
                  exact Bool.noConfusion hf'
                · by_cases h1 : T.any (isBoolSing Bool.true) = Bool.true
                  · refine ⟨VTy.isValue (.boolean Bool.false), ?_,
                      tmovesV_refl _⟩
                    have hc2 : ¬((T.any (isBoolSing Bool.true)
                        && T.any (isBoolSing Bool.false))
                        = Bool.true) := by
                      intro hcc
                      rw [Bool.and_eq_true] at hcc
                      exact hc hcc.2
                    simp only [removeAtom]
                    rw [if_neg (by rw [hbf]; exact fun h => Bool.noConfusion h),
                      if_pos isBoolClass_reduce, if_neg hc2, if_pos h1]
                    exact List.mem_singleton.mpr rfl
                  · refine ⟨.anyValue .bool, ?_, haa⟩
                    have hc2 : ¬((T.any (isBoolSing Bool.true)
                        && T.any (isBoolSing Bool.false))
                        = Bool.true) := by
                      intro hcc
                      rw [Bool.and_eq_true] at hcc
                      exact hc hcc.2
                    simp only [removeAtom]
                    rw [if_neg (by rw [hbf]; exact fun h => Bool.noConfusion h),
                      if_pos isBoolClass_reduce, if_neg hc2, if_neg h1,
                      if_neg hc]
                    exact List.mem_singleton.mpr rfl

theorem removeTy_cov {t' t T : Ty}
    (hcov : ∀ a' ∈ t', ∃ a ∈ t, tmovesV a' a = Bool.true) :
    ∀ x' ∈ removeTy t' T, ∃ x ∈ removeTy t T, tmovesV x' x = Bool.true := by
  intro x' hx'
  simp only [removeTy, List.mem_flatMap] at hx'
  obtain ⟨a', ha', hxm⟩ := hx'
  obtain ⟨a, ha, haa⟩ := hcov a' ha'
  obtain ⟨x, hx, hxx⟩ := removeAtom_cov haa T x' hxm
  exact ⟨x, List.mem_flatMap.mpr ⟨a, ha, hx⟩, hxx⟩

theorem complNormals_cov {t' t : Ty}
    (hcov : ∀ a' ∈ t', ∃ a ∈ t, tmovesV a' a = Bool.true) :
    ∀ x' ∈ complNormals t', ∃ x ∈ complNormals t, tmovesV x' x = Bool.true := by
  intro x' hx'
  simp only [complNormals, List.mem_filterMap] at hx'
  obtain ⟨a', ha', hmem⟩ := hx'
  cases a' with
  | complN p =>
      have hxe : x' = .complN p := by
        have h0 : (some (VTy.complN p) : Option VTy) = some x' := hmem
        have h1 : VTy.complN p = x' := by simpa using h0
        exact h1.symm
      subst hxe
      obtain ⟨a, ha, haa⟩ := hcov _ ha'
      obtain ⟨q, hq⟩ := tmovesV_complN_inv haa
      subst hq
      exact ⟨.complN q, by
        simp only [complNormals, List.mem_filterMap]
        exact ⟨.complN q, ha, rfl⟩, haa⟩
  | complT | anyValue _ | isValue _ | desc _ | notPresent =>
      exfalso
      have h0 : (none : Option VTy) = some x' := hmem
      cases h0

theorem complHasThrow_cov {t' t : Ty}
    (hcov : ∀ a' ∈ t', ∃ a ∈ t, tmovesV a' a = Bool.true) :
    complHasThrow t' = Bool.true → complHasThrow t = Bool.true := by
  intro h
  obtain ⟨a', ha', hab⟩ := List.any_eq_true.mp h
  obtain ⟨a, ha, haa⟩ := hcov a' ha'
  cases a' with
  | complT =>
      cases a with
      | complT =>
          exact List.any_eq_true.mpr ⟨.complT, ha, rfl⟩
      | complN p | anyValue _ | isValue _ | desc _ | notPresent =>
          simp [tmovesV] at haa
  | complN p | anyValue _ | isValue _ | desc _ | notPresent =>
      exfalso
      simp at hab

/- ## Proof layer II: the abstraction commutes with machine pushes -/

/-- frameOk at above = none is exactly frameChecks. -/
theorem frameOk_none_elim {sigs : SigTable} {η : HeapCallableTy} {f : Fr}
    (h : frameOk sigs η none f) : frameChecks sigs η f := by
  obtain ⟨-, hchk⟩ := h
  exact hchk

theorem frameOk_none_intro {sigs : SigTable} {η : HeapCallableTy} {f : Fr}
    (h : frameChecks sigs η f) : frameOk sigs η none f :=
  ⟨Or.inl rfl, h⟩



/- ## Proof layer II: the abstraction commutes with machine pushes -/

theorem mapM_singleton {α β : Type} {f : α → Option β} (a : α) :
    List.mapM f [a] = (f a).map (fun b => [b]) := by
  simp only [List.mapM, List.mapM.loop]
  cases f a <;> rfl

theorem markThrow_const (sigs : SigTable) (v : JSValue) (res : TCResult) :
    markThrow sigs (.const v) res = res := by
  cases res with
  | flows fb =>
      simp only [markThrow, exprCanThrow]
      cases v <;> simp [exprCanThrow]
  | reject site why => rfl

theorem checkSeq_kEval_const {sigs : SigTable} {r : Ty} {W : World} {v : JSValue}
    {rest : List Instr} :
    checkSeq sigs r W (.kEval (.const v) :: rest)
      = checkSeq sigs r
          { W with σ := [normalizeAtom W.η (typeOfV v)] :: W.σ } rest := by
  simp only [checkSeq, typeOfE, typeOfV, normalizeTy, List.map,
    markThrow_const]


/-- kEval of a nat literal: push the singleton number. -/
theorem checkSeq_kEval_nat {sigs : SigTable} {r : Ty} {W : World} {n : Nat}
    {rest : List Instr} :
    checkSeq sigs r W (.kEval (.nat n) :: rest)
      = checkSeq sigs r
          { W with σ := [normalizeAtom W.η (VTy.isValue (.number (↑n : Int)))] :: W.σ } rest := by
  simp only [checkSeq, typeOfE, normalizeTy, List.map]
  cases checkSeq sigs r
      { W with σ := [normalizeAtom W.η (VTy.isValue (.number (↑n : Int)))] :: W.σ } rest with
  | flows fb => simp only [markThrow, exprCanThrow, Bool.or_false]
  | reject site why => rfl

/-- kEval of a bound variable: push the looked-up (canonical) type. -/
theorem checkSeq_kEval_nv {sigs : SigTable} {r : Ty} {W : World} {x : «String»}
    {v : JSValue} {rest : List Instr}
    (hΓ : tyLookup W.Γ x = some [normalizeAtom W.η (typeOfV v)]) :
    checkSeq sigs r W (.kEval (.nv x) :: rest)
      = checkSeq sigs r
          { W with σ := [normalizeAtom W.η (typeOfV v)] :: W.σ } rest := by
  simp only [checkSeq, typeOfE, hΓ, normalizeTy, List.map,
    normalizeAtom_idem]
  cases checkSeq sigs r
      { W with σ := [normalizeAtom W.η (typeOfV v)] :: W.σ } rest with
  | flows fb => simp only [markThrow, exprCanThrow, Bool.or_false]
  | reject site why => rfl

/-- kPop: drop the top slot (the machine fells on an empty stack -
    those states are ill-typed and never reach this lemma). -/
theorem mergeTC_noFlows (res : TCResult) : mergeTC noFlows res = res := by
  cases res with
  | flows f => rfl
  | reject site why => rfl

theorem forkTC_cons (site : Instr) (u : World) (k : World → TCResult) :
    forkTC site [u] k = k u := by
  simp only [forkTC, List.foldl, mergeTC_noFlows, forkTC_cons]

theorem checkSeq_kPop {sigs : SigTable} {r : Ty} {W : World} {ts : Ty} {σ' : List Ty}
    {rest : List Instr} (hσ : W.σ = ts :: σ') :
    checkSeq sigs r W (.kPop :: rest)
      = checkSeq sigs r { W with σ := σ' } rest := by
  simp only [checkSeq, step1, hσ, List.foldl, mergeTC_noFlows, forkTC_cons]

/-- kSet: bind the top slot into Γ (a completion-typed binding is
    fine — first-class completions). -/
theorem checkSeq_kSet {sigs : SigTable} {r : Ty} {W : World} {x : «String»}
    {ts : Ty} {σ' : List Ty} {rest : List Instr}
    (hσ : W.σ = ts :: σ') :
    checkSeq sigs r W (.kSet x :: rest)
      = checkSeq sigs r { W with Γ := (x, ts) :: W.Γ, σ := σ'} rest := by
  simp only [checkSeq, step1, hσ, List.foldl, mergeTC_noFlows, forkTC_cons]


/- ## Proof layer V: the exact-match sr arms (head frame, above = none) -/


theorem lookup_mem {x : «String»} {v : JSValue} {env : Env}
    (h : lookup env x = some v) : (x, v) ∈ env := by
  induction env with
  | nil => simp [lookup] at h
  | cons hd tl ih =>
      obtain ⟨n, w⟩ := hd
      by_cases hx : n == x
      · simp only [lookup, hx, if_true, Option.some.injEq] at h
        rw [← h, beq_iff_eq.mp hx]
        exact List.Mem.head _
      · simp [lookup, hx] at h
        exact List.Mem.tail _ (ih h)

theorem checkSeq_reject_kPop {sigs : SigTable} {r : Ty} {W : World}
    {rest : List Instr} (hbad : step1 sigs .kPop W = none) :
    ∃ why, checkSeq sigs r W (.kPop :: rest)
      = TCResult.reject .kPop why := by
  simp only [checkSeq, hbad]
  exact ⟨_, rfl⟩

theorem checkSeq_reject_kWrapC {sigs : SigTable} {r : Ty} {W : World}
    {rest : List Instr} (hbad : step1 sigs (.kPrim1 .pWrapC) W = none) :
    ∃ why, checkSeq sigs r W (.kPrim1 .pWrapC :: rest)
      = TCResult.reject (.kPrim1 .pWrapC) why := by
  simp only [checkSeq, hbad]
  exact ⟨_, rfl⟩

theorem checkSeq_reject_kSet {sigs : SigTable} {r : Ty} {W : World} {x : «String»}
    {rest : List Instr} (hbad : step1 sigs (.kSet x) W = none) :
    ∃ why, checkSeq sigs r W (.kSet x :: rest)
      = TCResult.reject (.kSet x) why := by
  simp only [checkSeq, hbad]
  exact ⟨_, rfl⟩

/- Result accessors (reject-projectable). -/
def exitsT : TCResult → Bool
  | .flows f => f.exits
  | .reject _ _ => Bool.false

def throwsT : TCResult → Bool
  | .flows f => f.throws
  | .reject _ _ => Bool.false

def fallsT : TCResult → Worlds
  | .flows f => f.falls
  | .reject _ _ => []

def assumesT : TCResult → List «String»
  | .flows f => f.assumes
  | .reject _ _ => []

theorem fold_reject_absorb {α : Type} (J : α → TCResult) (s : Instr) (w : «String») :
    ∀ (as : List α),
      as.foldl (fun x a => mergeTC x (J a)) (TCResult.reject s w) = TCResult.reject s w := by
  intro as
  induction as with
  | nil => rfl
  | cons b bs ihb =>
      have h : (b :: bs).foldl (fun x a => mergeTC x (J a)) (TCResult.reject s w)
          = bs.foldl (fun x a => mergeTC x (J a)) (mergeTC (TCResult.reject s w) (J b)) := rfl
      rw [h]
      exact ihb

/-- Full characterization of the mergeTC fold: it rejects iff a
    component rejects; otherwise the record merges componentwise. -/
theorem fold_merge_flows {α : Type} (J : α → TCResult) :
    ∀ (ts : List α) (acc : TCResult),
      (∀ s w, ts.foldl (fun x a => mergeTC x (J a)) acc ≠ TCResult.reject s w) →
      (∀ a ∈ ts, ∃ fb, J a = TCResult.flows fb)
        ∧ ts.foldl (fun x a => mergeTC x (J a)) acc
            = TCResult.flows
                { exits := exitsT acc || ts.any (fun a => exitsT (J a)),
                  throws := throwsT acc || ts.any (fun a => throwsT (J a)),
                  falls := fallsT acc ++ ts.flatMap (fun a => fallsT (J a)),
                  assumes := assumesT acc ++ ts.flatMap (fun a => assumesT (J a)) } := by
  intro ts
  induction ts with
  | nil =>
      intro acc hnr
      refine ⟨?_, ?_⟩
      · intro a ha; cases ha
      · cases acc with
        | flows fb₀ =>
            cases fb₀
            simp [List.any_nil, List.flatMap_nil, exitsT, throwsT, fallsT, assumesT]
        | reject s w => exact absurd rfl (hnr s w)
  | cons a as ih =>
      intro acc hnr
      have hstep : (a :: as).foldl (fun x a => mergeTC x (J a)) acc
          = as.foldl (fun x a => mergeTC x (J a)) (mergeTC acc (J a)) := rfl
      rw [hstep] at hnr ⊢
      cases acc with
      | reject s w =>
          have hseed : mergeTC (TCResult.reject s w) (J a) = TCResult.reject s w := rfl
          rw [hseed, fold_reject_absorb J s w as] at hnr
          exact absurd rfl (hnr s w)
      | flows fb₀ =>
          cases hJa : J a with
          | reject s w =>
              have hseed : mergeTC (TCResult.flows fb₀) (TCResult.reject s w)
                  = TCResult.reject s w := rfl
              rw [hJa, hseed, fold_reject_absorb J s w as] at hnr
              exact absurd rfl (hnr s w)
          | flows fba =>
              rw [hJa] at hnr
              obtain ⟨hmem, heq⟩ := ih _ hnr
              refine ⟨?_, ?_⟩
              · intro a' ha'
                cases List.mem_cons.mp ha' with
                | inl h => subst h; exact ⟨_, hJa⟩
                | inr h => exact hmem a' h
              · rw [heq]
                simp only [mergeTC, exitsT, throwsT, fallsT, assumesT, hJa,
                  List.any_cons, List.flatMap_cons]
                simp [Bool.or_assoc, List.append_assoc]

/-- A flows result never equals a reject. -/
theorem ne_reject_of_flows {res : TCResult} {fb : Flows}
    (h : res = TCResult.flows fb) : ∀ s w, res ≠ TCResult.reject s w := by
  intro s w hsw
  rw [hsw] at h
  exact TCResult.noConfusion h

/-- The noFlows-seeded fork fold over a NONEMPTY successor set: an
    empty-falls total forces every component to fall-empty, and the
    head component's IH forces its exits — hence the fold's exits. -/
theorem fold_noFlows_exits {sigs : SigTable} {r : Ty} {rest : List Instr}
    (ih1 : ∀ (u : World) (fbu : Flows), checkSeq sigs r u rest = TCResult.flows fbu
      → fbu.falls = [] → fbu.exits = Bool.true) :
    ∀ (ws : Worlds) (fr : Flows),
      ws.foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows = TCResult.flows fr
        → fr.falls = [] → ws ≠ [] → fr.exits = Bool.true := by
  intro ws
  induction ws with
  | nil => intro fr _ _ hne; exact absurd rfl hne
  | cons u us ihw =>
      intro fr heq hf _
      have hstep : (u :: us).foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows
          = us.foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest))
              (mergeTC noFlows (checkSeq sigs r u rest)) := rfl
      rw [hstep] at heq
      cases hK : checkSeq sigs r u rest with
      | reject s w =>
          rw [hK] at heq
          have hseed : mergeTC noFlows (TCResult.reject s w) = TCResult.reject s w := rfl
          rw [hseed, fold_reject_absorb _ s w us] at heq
          exact TCResult.noConfusion heq
      | flows fbu =>
          have hseed : mergeTC noFlows (TCResult.flows fbu)
              = TCResult.flows
                  { exits := Bool.false || fbu.exits, throws := Bool.false || fbu.throws,
                    falls := [] ++ fbu.falls, assumes := [] ++ fbu.assumes } := rfl
          rw [hK, hseed] at heq
          cases us with
          | nil =>
              have hinj := TCResult.flows.inj heq
              subst hinj
              show Bool.false || fbu.exits = Bool.true
              rw [ih1 u fbu hK hf]
              rfl
          | cons v vs =>
              obtain ⟨-, heq2⟩ := fold_merge_flows (fun u => checkSeq sigs r u rest)
                (v :: vs) _ (ne_reject_of_flows heq)
              rw [heq2] at heq
              have hinj := TCResult.flows.inj heq
              subst hinj
              have hf' : fbu.falls = [] := by
                cases hfb : fbu.falls with
                | nil => rfl
                | cons x xs =>
                    rw [hfb] at hf
                    simp only [fallsT, List.nil_append, List.cons_append] at hf
                    exact absurd hf (List.cons_ne_nil _ _)
              show (Bool.false || fbu.exits)
                  || (v :: vs).any (fun u => exitsT (checkSeq sigs r u rest)) = Bool.true
              rw [ih1 u fbu hK hf']
              simp

/-- forkTC preserves the invariant: a flows result is a nonempty
    fold, and the head component carries the exits. -/
theorem forkTC_exits {sigs : SigTable} {r : Ty} {site : Instr} {rest : List Instr}
    {ws : Worlds} {fb : Flows}
    (h : forkTC site ws (fun u => checkSeq sigs r u rest) = TCResult.flows fb)
    (hf : fb.falls = [])
    (ih1 : ∀ (u : World) (fbu : Flows), checkSeq sigs r u rest = TCResult.flows fbu
      → fbu.falls = [] → fbu.exits = Bool.true) :
    fb.exits = Bool.true := by
  cases ws with
  | nil => rw [forkTC] at h; exact TCResult.noConfusion h
  | cons u us =>
      have hfok : forkTC site (u :: us) (fun u => checkSeq sigs r u rest)
          = (u :: us).foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows := by
        simp only [forkTC]
      rw [hfok] at h
      exact fold_noFlows_exits ih1 _ _ h hf (by simp)

/-- markThrow preserves falls and exits. -/
theorem markThrow_exits {sigs : SigTable} {ex : Expr} {res : TCResult} {fb : Flows}
    (h : markThrow sigs ex res = TCResult.flows fb) (hf : fb.falls = [])
    (ih : ∀ fb', res = TCResult.flows fb' → fb'.falls = [] → fb'.exits = Bool.true) :
    fb.exits = Bool.true := by
  cases hres : res with
  | reject s w => rw [hres] at h; simp only [markThrow] at h; exact TCResult.noConfusion h
  | flows fb' =>
      rw [hres] at h
      simp only [markThrow] at h
      have hinj := TCResult.flows.inj h
      subst hinj
      have hf' : fb'.falls = [] := hf
      show fb'.exits = Bool.true
      exact ih fb' hres hf'

/-- THE NO-SILENT-FALLS INVARIANT: every checkSeq result that is
    flows with empty falls EXITED. The load-bearing structural fact
    of the checker — type_safety's frame demand (terminal) is
    of the checker — type_safety's frame demand (terminal) is
    transferable across instruction boundaries only because of it. -/
theorem complNormals_empty_cov {t' t : Ty}
    (hcov : ∀ a' ∈ t', ∃ a ∈ t, tmovesV a' a = Bool.true)
    (hnorm : complNormals t = []) : complNormals t' = [] := by
  cases hc : complNormals t' with
  | nil => rfl
  | cons x' xs =>
      exfalso
      obtain ⟨x, hx, -⟩ := complNormals_cov hcov x' (by rw [hc]; exact List.mem_cons_self ..)
      rw [hnorm] at hx
      cases hx

theorem complAtom_not_covered_bare {a' a : VTy}
    (h : tmovesV a' a = Bool.true) (hba : isBareVTy a = Bool.true) :
    isBareVTy a' = Bool.true := isBareVTy_of_cover hba h

theorem complOnly_cons_elim {a : VTy} {rest : Ty}
    (h : complOnly (a :: rest) = Bool.true) :
    (∃ p, a = .complN p) ∨ a = .complT := by
  simp only [complOnly, Bool.and_eq_true] at h
  cases a with
  | complN p => exact Or.inl ⟨p, rfl⟩
  | complT => exact Or.inr rfl
  | anyValue _ | isValue _ | desc _ | notPresent =>
      exact absurd h.1 (by simp)

theorem isBareVTy_of_bareSlot_mem : ∀ (t : Ty) (wt : Ty), bareSlot t = some wt →
    ∀ (a : VTy), a ∈ t → isBareVTy a = Bool.true
  | [], _, _, a, ha => by cases ha
  | b :: rest, wt, hb, a, ha => by
      cases hib : isBareVTy b with
      | true =>
          match List.mem_cons.mp ha with
          | Or.inl he => rw [he]; exact hib
          | Or.inr hr =>
              simp only [bareSlot, hib, Bool.and_eq_true] at hb
              cases hbs : bareSlot rest with
              | none => rw [hbs] at hb; simp at hb
              | some rs => exact isBareVTy_of_bareSlot_mem rest rs hbs a hr
      | false =>
          simp only [bareSlot, hib] at hb
          exact absurd hb (by simp)

theorem tmovesV_complN_bare_false : ∀ (a p : VTy), isBareVTy a = Bool.true →
    tmovesV (.complN p) a = Bool.false
  | .complN q, _, h => by
      simp only [isBareVTy, Bool.false_eq_true] at h
  | .complT, _, _ => rfl
  | .anyValue _, _, _ => rfl
  | .isValue _, _, _ => rfl
  | .desc _, _, _ => rfl
  | .notPresent, _, _ => rfl

/-- bareSlot preserves coverage (through the complN wrap). -/
theorem bareSlot_tyCov {η : HeapCallableTy} {t' t : Ty}
    (hcov : tyCov η t' t) {wt : Ty} (hb : bareSlot t = some wt) :
    bareSlot t' = some t' ∧ tyCov η (t'.map VTy.complN) (wt.map VTy.complN) := by
  have hpure := bareSlot_pure t wt hb
  have hwt : wt = t := by
    have hs := bareSlot_eq_self (t := t) hpure
    rw [hs] at hb
    simp only [Option.some.injEq] at hb
    exact hb.symm
  subst hwt
  have hpure' : ∀ a' ∈ t', isBareVTy a' = Bool.true := by
    intro a' ha'
    obtain ⟨a, ha, hac⟩ := hcov a' ha'
    exact isBareVTy_of_cover (hpure a ha) (atomCov_tmoves hac)
  refine ⟨bareSlot_eq_self t' hpure', ?_⟩
  intro b hbm
  simp only [List.mem_map] at hbm
  obtain ⟨a', ha', rfl⟩ := hbm
  obtain ⟨a, ha, hac⟩ := hcov a' ha'
  exact ⟨.complN a, by simp [ha], atomCov_complN_of hac⟩


theorem normalizeTy_slotLe {η : HeapCallableTy} {t' t : Ty}
    (hslot : slotLe t' t) (hcov : tyCov η t' t) :
    slotLe (normalizeTy η t') (normalizeTy η t) := by
  refine ⟨tyLe_of_atom_cov (fun a' ha' => ?_), ?_⟩
  · obtain ⟨b', hb', rfl⟩ := List.mem_map.mp ha'
    obtain ⟨a, ha, hac⟩ := hcov b' hb'
    exact ⟨normalizeAtom η a, List.mem_map.mpr ⟨a, ha, rfl⟩,
      atomCov_tmoves (normalizeAtom_cov hac)⟩
  · intro hne
    have ht : t ≠ [] := by
      intro hte; rw [hte] at hne; simp [normalizeTy] at hne
    have ht' := hslot.2 ht
    cases t' with
    | nil => exact absurd rfl ht'
    | cons a r => simp [normalizeTy]

theorem step1_cov (sigs : SigTable) (i : Instr) :
    ∀ (w' w : World), worldLe w' w → ∀ ws, step1 sigs i w = some ws →
      ∃ ws', step1 sigs i w' = some ws' ∧
        ∀ u' ∈ ws', ∃ u ∈ ws, worldLe u' u := by
  intro w' w hwl ws hstep
  obtain ⟨η', Γ', σ'⟩ := w'
  obtain ⟨η, Γ, σ⟩ := w
  obtain ⟨hη, hΓ, hσ, hcovΓ, hcovσ⟩ := hwl
  cases i with
  | kEval e | kIte t e | kRet | kAssert | kTestVar x p
  | kRepeatWhile c b | kRepeatTest c b | kForStart x b | kForBody x l b =>
      simp only [step1, Option.some.injEq] at hstep
      subst hstep
      refine ⟨(⟨η', Γ', σ'⟩ : World) :: [], rfl, ?_⟩
      intro u' hu'
      simp only [List.mem_singleton] at hu'
      subst hu'
      exact ⟨⟨η, Γ, σ⟩, List.mem_singleton.mpr rfl, hη, hΓ, hσ, hcovΓ, hcovσ⟩
  | kPop =>
      cases σ with
      | nil => exact absurd hstep (by simp [step1])
      | cons t σr =>
          cases σ' with
          | nil => exact absurd hσ (by simp [stackLe])
          | cons t' σr' =>
              simp only [step1, Option.some.injEq] at hstep
              subst hstep
              refine ⟨(⟨η', Γ', σr'⟩ : World) :: [], rfl, ?_⟩
              intro u' hu'
              simp only [List.mem_singleton] at hu'
              subst hu'
              exact ⟨⟨η, Γ, σr⟩, List.mem_singleton.mpr rfl, hη, hΓ, hσ.2, hcovΓ, hcovσ.2⟩
  | kSet x =>
      cases σ with
      | nil => exact absurd hstep (by simp [step1])
      | cons t σr =>
          cases σ' with
          | nil => exact absurd hσ (by simp [stackLe])
          | cons t' σr' =>
              obtain ⟨hslot, hrest⟩ := hσ
              simp only [step1, Option.some.injEq] at hstep
              subst hstep
              refine ⟨(⟨η', (x, t') :: Γ', σr'⟩ : World) :: [], rfl, ?_⟩
              intro u' hu'
              simp only [List.mem_singleton] at hu'
              subst hu'
              exact ⟨⟨η, (x, t) :: Γ, σr⟩, List.mem_singleton.mpr rfl,
                hη, envLe_cons hΓ hslot, hrest,
                envCov_cons hcovΓ hcovσ.1, hcovσ.2⟩
  | kMkList n =>
      simp only [step1] at hstep
      cases hpop : popTyN n anyT σ with
      | none => simp only [hpop] at hstep; exact absurd hstep (by simp)
      | some mid =>
          simp only [hpop, Option.some.injEq] at hstep
          subst hstep
          obtain ⟨mid', hpop', hle'⟩ := popTyN_cov n anyT hσ hpop
          obtain ⟨mid2, hpop2, hle2⟩ := popTyN_ty_cov n anyT hcovσ hpop
          have hmid : mid' = mid2 :=
            Option.some.inj (hpop'.symm.trans hpop2)
          subst hmid
          refine ⟨(⟨η', Γ', [.anyValue .list] :: mid'⟩ : World) :: [], ?_, ?_⟩
          · simp only [step1, hpop']
          · intro u' hu2
            simp only [List.mem_singleton] at hu2
            subst hu2
            exact ⟨⟨η, Γ, [.anyValue .list] :: mid⟩, List.mem_singleton.mpr rfl,
              hη, hΓ, ⟨slotLe_refl _, hle'⟩, hcovΓ,
              stackCov_cons_intro (tyCov_refl _ _) hle2⟩
  | kNewSlot sn =>
      simp only [step1] at hstep
      cases hsn : slotOfName sn with
      | none => simp only [hsn] at hstep; exact absurd hstep (by simp)
      | some sl =>
          simp only [hsn] at hstep
          cases σ with
          | nil => exact absurd hstep (by simp [popTy])
          | cons t σr =>
              cases σ' with
              | nil => exact absurd hσ (by simp [stackLe])
              | cons t' σr' =>
                  obtain ⟨hslot, hrest⟩ := hσ
                  cases hpop : popTy anyT (t :: σr) with
                  | none => simp only [hpop] at hstep; exact absurd hstep (by simp)
                  | some mid =>
                      have hmid : mid = σr := by
                        simp only [popTy] at hpop
                        cases hif : tmoves t anyT with
                        | false => rw [hif] at hpop; simp at hpop
                        | true =>
                            rw [hif] at hpop
                            simp only [Option.some.injEq, reduceIte] at hpop
                            exact hpop.symm
                      subst hmid
                      have hpop' : popTy anyT (t' :: σr') = some σr' :=
                        popTy_cov hslot hrest hpop
                      simp only [hpop, Option.some.injEq] at hstep
                      subst hstep
                      refine ⟨(⟨η', Γ', objT :: σr'⟩ : World) :: [], ?_, ?_⟩
                      · simp only [step1, hsn, hpop']
                      · intro u' hu2
                        simp only [List.mem_singleton] at hu2
                        subst hu2
                        exact ⟨⟨η, Γ, objT :: mid⟩,
                          List.mem_singleton.mpr rfl, hη, hΓ,
                          ⟨slotLe_refl _, hrest⟩, hcovΓ,
                          stackCov_cons_intro (tyCov_refl _ _) hcovσ.2⟩
  | kUnwrap =>
      cases σ with
      | nil => exact absurd hstep (by simp [step1])
      | cons t σr =>
          cases σ' with
          | nil => exact absurd hσ (by simp [stackLe])
          | cons t' σr' =>
              obtain ⟨hslot, hrest⟩ := hσ
              simp only [step1] at hstep
              cases hu : unwrapSlot t with
              | none => simp only [hu] at hstep; exact absurd hstep (by simp)
              | some ps =>
                  simp only [hu, Option.map_some, Option.some.injEq] at hstep
                  subst hstep
                  obtain ⟨hu', hslot2⟩ := unwrapSlot_cov hslot hu
                  simp only [step1, hu', Option.map_some]
                  obtain ⟨ps2, hps2, hps2c⟩ := unwrapSlot_ty_cov hcovσ.1 hu
                  have hpe : payloadsOf t' = ps2 := payloadsOf_eq_unwrap t' ps2 hps2
                  rw [hpe] at hslot2 ⊢
                  refine ⟨(⟨η', Γ', ps2 :: σr'⟩ : World) :: [], rfl, ?_⟩
                  intro u' hu2
                  simp only [List.mem_singleton] at hu2
                  subst hu2
                  exact ⟨⟨η, Γ, ps :: σr⟩, List.mem_singleton.mpr rfl, hη, hΓ,
                    ⟨hslot2, hrest⟩, hcovΓ,
                    stackCov_cons_intro hps2c hcovσ.2⟩
  | kPrim1 p =>
      cases hpt : primTys p with
      | none =>
          cases p with
          | pWrapC =>
              cases σ with
              | nil => exact absurd hstep (by simp [step1])
              | cons t σr =>
                  cases σ' with
                  | nil => exact absurd hσ (by simp [stackLe])
                  | cons t' σr' =>
                      obtain ⟨hslot, hrest⟩ := hσ
                      simp only [step1] at hstep
                      cases hco : complOnly t with
                      | true =>
                          -- coarse: identity push of t. The refined
                          -- slot inherits completion-purity, so the
                          -- refined branch is identity too.
                          have hco' : complOnly t' = Bool.true :=
                            complOnly_of_compl
                              (slotCompl_of_cover hslot (complOnly_compl hco))
                          simp only [hco, hco', reduceIte,
                            Option.some.injEq] at hstep
                          subst hstep
                          simp only [step1, hco', reduceIte]
                          refine ⟨(⟨η', Γ', t' :: σr'⟩ : World) :: [], rfl, ?_⟩
                          intro u' hu2
                          simp only [List.mem_singleton] at hu2
                          subst hu2
                          exact ⟨⟨η, Γ, t :: σr⟩, List.mem_singleton.mpr rfl,
                            hη, hΓ, ⟨hslot, hrest⟩, hcovΓ, hcovσ⟩
                      | false =>
                          -- coarse NOT compl-pure but accepted: the
                          -- bareSlot branch fired, so t is pure-bare.
                          -- A completion atom of t' would need a
                          -- completion cover in t - impossible - so
                          -- t' is pure-bare (false) or empty (true).
                          simp only [hco, reduceIte] at hstep
                          cases hb : bareSlot t with
                          | none => simp only [hb] at hstep
                                    exact absurd hstep (by simp)
                          | some wt =>
                              simp only [hb, Option.map_some,
                                Option.some.injEq] at hstep
                              obtain ⟨hb', hslot2⟩ := bareSlot_cov hslot hb
                              cases hc2 : complOnly t' with
                              | true =>
                                  cases t' with
                                  | nil =>
                                      cases hstep
                                      simp only [step1, hc2, reduceIte]
                                      refine ⟨(⟨η', Γ', ([] : Ty) :: σr'⟩ : World) :: [], rfl, ?_⟩
                                      intro u' hu2
                                      simp only [List.mem_singleton] at hu2
                                      subst hu2
                                      exact ⟨⟨η, Γ, wt.map VTy.complN :: σr⟩,
                                         List.mem_singleton.mpr rfl, hη, hΓ,
                                         ⟨hslot2, hrest⟩, hcovΓ,
                                         stackCov_cons_intro tyCov_nil hcovσ.2⟩
                                   | cons a' rest' =>
                                      exfalso
                                      -- hc2: every atom of t' compl; a
                                      -- completion atom can never be
                                      -- covered by t's pure-bare atoms
                                      cases hcp : a' with
                                      | complN p =>
                                          obtain ⟨a, ha, haa⟩ :=
                                            tyLe_cov_atoms hslot.1
                                              (.complN p)
                                              (by rw [hcp]; exact List.mem_cons_self ..)
                                          have hbar : isBareVTy a = Bool.true :=
                                            isBareVTy_of_bareSlot_mem t wt hb a ha
                                          rw [tmovesV_complN_bare_false a p
                                            hbar] at haa
                                          exact Bool.noConfusion haa
                                      | complT =>
                                          obtain ⟨a, ha, haa⟩ :=
                                            tyLe_cov_atoms hslot.1 .complT
                                              (by rw [hcp]; exact List.mem_cons_self ..)
                                          have hbar : isBareVTy a = Bool.true :=
                                            isBareVTy_of_bareSlot_mem t wt hb a ha
                                          cases a with
                                          | complT =>
                                              simp [isBareVTy] at hbar
                                          | complN q | anyValue _
                                          | isValue _ | desc _ | notPresent =>
                                              simp [tmovesV] at haa
                                      | anyValue _ | isValue _ | desc _
                                      | notPresent =>
                                          have := complOnly_cons_elim hc2
                                          exact absurd this (by
                                            intro h
                                            rcases h with ⟨p, hp⟩ | hp
                                            · rw [hcp] at hp; simp at hp
                                            · rw [hcp] at hp; simp at hp)
                              | false =>
                                  cases hstep
                                  simp only [step1, hc2, reduceIte, hb',
                                    Option.map_some]
                                  refine ⟨(⟨η', Γ', t'.map VTy.complN :: σr'⟩ : World) :: [], rfl, ?_⟩
                                  intro u' hu2
                                  simp only [List.mem_singleton] at hu2
                                  subst hu2
                                  exact ⟨⟨η, Γ, wt.map VTy.complN :: σr⟩,
                                     List.mem_singleton.mpr rfl, hη, hΓ,
                                     ⟨hslot2, hrest⟩, hcovΓ,
                                     stackCov_cons_intro
                                       (bareSlot_tyCov hcovσ.1 hb).2 hcovσ.2⟩
           | pThrowC =>
              cases σ with
              | nil => exact absurd hstep (by simp [step1])
              | cons t σr =>
                  cases σ' with
                  | nil => exact absurd hσ (by simp [stackLe])
                  | cons t' σr' =>
                      obtain ⟨-, hrest⟩ := hσ
                      simp only [step1, Option.some.injEq] at hstep
                      subst hstep
                      refine ⟨(⟨η', Γ', [VTy.complT] :: σr'⟩ : World) :: [], rfl, ?_⟩
                      intro u' hu2
                      simp only [List.mem_singleton] at hu2
                      subst hu2
                      exact ⟨⟨η, Γ, [VTy.complT] :: σr⟩,
                         List.mem_singleton.mpr rfl, hη, hΓ,
                         ⟨slotLe_refl _, hrest⟩, hcovΓ,
                         stackCov_cons_intro (tyCov_refl _ _) hcovσ.2⟩
          | pIsObj | pIsNotObj | pIsNotU | pHasCall | pHasCtor | pIsU
          | pIsTrue | pIsFalse | pNullOrUnd | pIsNull
          | pIsType _ | pHasField _ | pIsStr _ | pDescField _
          | pUnwrapC | pIsNormalC | pIsThrowC | pIsCompletion | pPred _ _ =>
              simp only [step1, hpt, Option.some.injEq] at hstep
              subst hstep
              refine ⟨(⟨η', Γ', σ'⟩ : World) :: [], by
                simp only [step1, hpt], ?_⟩
              intro u' hu2
              simp only [List.mem_singleton] at hu2
              subst hu2
              exact ⟨⟨η, Γ, σ⟩, List.mem_singleton.mpr rfl, hη, hΓ, hσ, hcovΓ, hcovσ⟩
      | some tt =>
          obtain ⟨tin, tout⟩ := tt
          cases p with
          | pWrapC | pThrowC => exact absurd hpt (by simp [primTys])
          | pIsObj | pIsNotObj | pIsNotU | pHasCall | pHasCtor | pIsU
          | pIsTrue | pIsFalse | pNullOrUnd | pIsNull
          | pIsType _ | pHasField _ | pIsStr _ | pDescField _
          | pUnwrapC | pIsNormalC | pIsThrowC | pIsCompletion | pPred _ _ =>
          cases σ with
          | nil => simp only [step1, hpt] at hstep
                   exact absurd hstep (by simp [popTy])
          | cons t σr =>
              cases σ' with
              | nil => exact absurd hσ (by simp [stackLe])
              | cons t' σr' =>
                  obtain ⟨hslot, hrest⟩ := hσ
                  simp only [step1, hpt] at hstep
                  cases hpop : popTy tin (t :: σr) with
                  | none => simp only [hpop] at hstep
                            exact absurd hstep (by simp)
                  | some mid =>
                      have hmid : mid = σr := by
                        simp only [popTy] at hpop
                        cases hif : tmoves t tin with
                        | false => rw [hif] at hpop; simp at hpop
                        | true =>
                            rw [hif] at hpop
                            simp only [Option.some.injEq, reduceIte] at hpop
                            exact hpop.symm
                      subst hmid
                      have hpop' : popTy tin (t' :: σr') = some σr' :=
                        popTy_cov hslot hrest hpop
                      simp only [hpop, Option.some.injEq] at hstep
                      subst hstep
                      refine ⟨(⟨η', Γ', tout :: σr'⟩ : World) :: [], ?_, ?_⟩
                      · simp only [step1, hpt, hpop']
                      · intro u' hu2
                        simp only [List.mem_singleton] at hu2
                        subst hu2
                        exact ⟨⟨η, Γ, tout :: mid⟩,
                           List.mem_singleton.mpr rfl, hη, hΓ,
                           ⟨slotLe_refl _, hrest⟩, hcovΓ,
                           stackCov_cons_intro (tyCov_refl _ _) hcovσ.2⟩
  | kCall f n =>
      simp only [step1] at hstep
      cases hsig : sigFind sigs f with
      | none => simp only [hsig] at hstep; exact absurd hstep (by simp)
      | some s =>
          obtain ⟨ps, retj⟩ := s
          simp only [hsig] at hstep
          cases har : (ps.length == n) || (ps.length == n + 1) with
          | false => simp only [har] at hstep; exact absurd hstep (by simp)
          | true =>
              simp only [har] at hstep
              cases hpa : popArgs (if ps.length == n then ps else ps.take n) σ with
              | false => simp only [hpa] at hstep
                         exact absurd hstep (by simp)
              | true =>
                  simp only [hpa, Option.some.injEq] at hstep
                  subst hstep
                  have hpa' : popArgs (if ps.length == n then ps else ps.take n) σ'
                      = Bool.true := popArgs_cov hσ hpa
                  refine ⟨(⟨η', Γ', complTy retj :: σ'.drop n⟩ : World) :: [], ?_, ?_⟩
                  · simp only [step1, hsig, har, hpa']
                  · intro u' hu2
                    simp only [List.mem_singleton] at hu2
                    subst hu2
                    exact ⟨⟨η, Γ, complTy retj :: σ.drop n⟩,
                       List.mem_singleton.mpr rfl, hη, hΓ,
                       ⟨slotLe_refl _, stackLe_drop n hσ⟩, hcovΓ,
                       stackCov_cons_intro (tyCov_refl _ _)
                         (stackCov_drop n hcovσ)⟩
  | kIMeth nm n =>
      simp only [step1] at hstep
      cases har : mopArity nm == some n with
      | false => simp only [har] at hstep; exact absurd hstep (by simp)
      | true =>
          simp only [har] at hstep
          cases hpop : popTyN n anyT σ with
          | none => simp only [hpop] at hstep
                    exact absurd hstep (by simp)
          | some mid =>
              simp only [hpop] at hstep
              cases mid with
              | nil => exact absurd hstep (by simp [popAObj, popA, popTy])
              | cons m mr =>
                  cases hpop2 : popAObj (m :: mr) with
                  | none => simp only [hpop2] at hstep
                            exact absurd hstep (by simp)
                  | some m2 =>
                      have hm2 : m2 = mr := popAObj_cons_eq hpop2
                      subst hm2
                      simp only [hpop2, Option.some.injEq] at hstep
                      subst hstep
                      obtain ⟨mid', hpop', hle'⟩ := popTyN_cov n anyT hσ hpop
                      obtain ⟨midc, hpopc, hcovc⟩ := popTyN_ty_cov n anyT hcovσ hpop
                      cases mid' with
                      | nil => exact absurd hle' (by simp [stackLe])
                      | cons m' mr' =>
                          have hmc : midc = m' :: mr' :=
                            (Option.some.inj (hpop'.symm.trans hpopc)).symm
                          rw [hmc] at hcovc
                          obtain ⟨hslotm, hrestm⟩ := hle'
                          have hpa' : popAObj (m' :: mr')
                              = some mr' := popAObj_cov hslotm hrestm hpop2
                          refine ⟨(⟨η', Γ', complTy (mopResult nm) :: mr'⟩ : World) :: [], ?_, ?_⟩
                          · simp only [step1, har, hpop']
                            rw [hpa']
                          · intro u' hu2
                            simp only [List.mem_singleton] at hu2
                            subst hu2
                            exact ⟨⟨η, Γ, complTy (mopResult nm) :: m2⟩,
                              List.mem_singleton.mpr rfl, hη, hΓ,
                              ⟨slotLe_refl _, hrestm⟩, hcovΓ,
                              stackCov_cons_intro (tyCov_refl _ _) hcovc.2⟩
  | kTest =>
      cases σ with
      | nil => exact absurd hstep (by simp [step1])
      | cons t σr =>
          cases σ' with
          | nil => exact absurd hσ (by simp [stackLe])
          | cons t' σr' =>
              obtain ⟨hslot, hrest⟩ := hσ
              simp only [step1] at hstep
              cases hco : complOnly t with
              | false => simp only [hco, reduceIte] at hstep
                         exact absurd hstep (by simp)
              | true =>
                  simp only [hco, reduceIte] at hstep
                  have hpure : slotCompl t := complOnly_compl hco
                  have hpure' : slotCompl t' := slotCompl_of_cover hslot hpure
                  have hcov : ∀ a' ∈ t', ∃ a ∈ t, tmovesV a' a = Bool.true :=
                    tyLe_cov_atoms hslot.1
                  have hne : t ≠ [] := by
                    intro hc
                    subst hc
                    simp only [complNormals, List.filterMap_nil,
                      complHasThrow, List.any_nil, Bool.or_false,
                      List.nil_append, reduceIte] at hstep
                    exact absurd hstep (by simp)
                  have hne' : t' ≠ [] := hslot.2 hne
                  cases hnorm : complNormals t with
                  | nil =>
                      have hnorm' : complNormals t' = [] :=
                        complNormals_empty_cov hcov hnorm
                      cases hthrow : complHasThrow t with
                      | false =>
                          simp only [hnorm, hthrow, List.append_nil,
                            reduceIte] at hstep
                          exact absurd hstep (by simp)
                      | true =>
                          simp only [hnorm, hthrow, List.nil_append, reduceIte,
                            Option.some.injEq] at hstep
                          subst hstep
                          cases hthrow' : complHasThrow t' with
                          | false =>
                              rcases slotCompl_side hpure' hne' with H | H
                              · rw [hnorm'] at H; exact absurd rfl H
                              · rw [hthrow'] at H; exact Bool.noConfusion H
                          | true =>
                              have hco' : complOnly t' = Bool.true :=
                                complOnly_of_compl hpure'
                              simp only [step1, hco', hnorm', hthrow', reduceIte,
                                List.nil_append]
                              refine ⟨(⟨η', Γ', [.isValue (.boolean Bool.true)]
                                :: [VTy.complT] :: σr'⟩ : World) :: [], rfl, ?_⟩
                              intro u' hu2
                              simp only [List.mem_singleton] at hu2
                              subst hu2
                              exact ⟨⟨η, Γ, [.isValue (.boolean Bool.true)]
                                 :: [VTy.complT] :: σr⟩,
                                 List.mem_singleton.mpr rfl, hη, hΓ,
                                 ⟨slotLe_refl _, ⟨slotLe_refl _, hrest⟩⟩, hcovΓ,
                                 stackCov_cons_intro (tyCov_refl _ _)
                                   (stackCov_cons_intro (tyCov_refl _ _) hcovσ.2)⟩
                   | cons n1 ns =>
                      cases hthrow : complHasThrow t with
                      | false =>
                          simp only [hnorm, hthrow, List.append_nil, reduceIte,
                            Option.some.injEq] at hstep
                          subst hstep
                          have hnorm'ne : complNormals t' ≠ [] := by
                            rcases slotCompl_side hpure' hne' with H | H
                            · exact H
                            · exact absurd (complHasThrow_cov hcov H)
                                (by rw [hthrow]; simp)
                          cases hnorm' : complNormals t' with
                          | nil => exact absurd hnorm' hnorm'ne
                          | cons h1 hs =>
                              have hco' : complOnly t' = Bool.true :=
                                complOnly_of_compl hpure'
                              cases hthrow' : complHasThrow t' with
                              | false =>
                                  simp only [step1, hco', hnorm', hthrow', reduceIte,
                                    List.append_nil]
                                  refine ⟨(⟨η', Γ', [.isValue (.boolean Bool.false)]
                                    :: (h1 :: hs) :: σr'⟩ : World) :: [], rfl, ?_⟩
                                  intro u' hu2
                                  simp only [List.mem_singleton] at hu2
                                  subst hu2
                                  have hle : tyLe (h1 :: hs) (n1 :: ns) := by
                                    have hle2 := tyLe_of_atom_cov
                                      (complNormals_cov hcov)
                                    rw [hnorm', hnorm] at hle2
                                    exact hle2
                                  have hcn : tyCov η' (h1 :: hs) (n1 :: ns) := by
                                    rw [← hnorm', ← hnorm]
                                    exact tyCov_complNormals hcovσ.1
                                  exact ⟨⟨η, Γ, [.isValue (.boolean Bool.false)]
                                    :: (n1 :: ns) :: σr⟩,
                                    List.mem_singleton.mpr rfl, hη, hΓ,
                                    ⟨slotLe_refl _, ⟨⟨hle, by
                                      intro _ hc2
                                      exact List.cons_ne_nil h1 hs hc2⟩, hrest⟩⟩,
                                    hcovΓ,
                                    stackCov_cons_intro (tyCov_refl _ _)
                                      (stackCov_cons_intro hcn hcovσ.2)⟩
                              | true =>
                                  exact absurd (complHasThrow_cov hcov hthrow')
                                    (by rw [hthrow]; simp)
                      | true =>
                          simp only [hnorm, hthrow, List.cons_append,
                            List.nil_append, reduceIte,
                            Option.some.injEq] at hstep
                          subst hstep
                          cases hnorm' : complNormals t' with
                          | nil =>
                              have hthrow' : complHasThrow t' = Bool.true := by
                                rcases slotCompl_side hpure' hne' with H | H
                                · rw [hnorm'] at H; exact absurd rfl H
                                · exact H
                              have hco' : complOnly t' = Bool.true :=
                                complOnly_of_compl hpure'
                              simp only [step1, hco', hnorm', hthrow', reduceIte,
                                List.cons_append, List.nil_append]
                              refine ⟨(⟨η', Γ', [.isValue (.boolean Bool.true)]
                                :: [VTy.complT] :: σr'⟩ : World) :: [], rfl, ?_⟩
                              intro u' hu2
                              simp only [List.mem_singleton] at hu2
                              subst hu2
                              exact ⟨⟨η, Γ, [.isValue (.boolean Bool.true)]
                                :: [VTy.complT] :: σr⟩,
                                 List.mem_cons.mpr (Or.inr
                                   (List.mem_singleton.mpr rfl)), hη, hΓ,
                                 ⟨slotLe_refl _, ⟨slotLe_refl _, hrest⟩⟩, hcovΓ,
                                 stackCov_cons_intro (tyCov_refl _ _)
                                   (stackCov_cons_intro (tyCov_refl _ _) hcovσ.2)⟩
                          | cons h1 hs =>
                              have hco' : complOnly t' = Bool.true :=
                                complOnly_of_compl hpure'
                              cases hthrow' : complHasThrow t' with
                              | false =>
                                  simp only [step1, hco', hnorm', hthrow',
                                    reduceIte, List.append_nil]
                                  refine ⟨(⟨η', Γ', [.isValue (.boolean Bool.false)]
                                    :: (h1 :: hs) :: σr'⟩ : World) :: [], rfl, ?_⟩
                                  intro u' hu2
                                  simp only [List.mem_singleton] at hu2
                                  subst hu2
                                  have hle : tyLe (h1 :: hs) (n1 :: ns) := by
                                    have hle2 := tyLe_of_atom_cov
                                      (complNormals_cov hcov)
                                    rw [hnorm', hnorm] at hle2
                                    exact hle2
                                  have hcn : tyCov η' (h1 :: hs) (n1 :: ns) := by
                                    rw [← hnorm', ← hnorm]
                                    exact tyCov_complNormals hcovσ.1
                                  exact ⟨⟨η, Γ, [.isValue (.boolean Bool.false)]
                                    :: (n1 :: ns) :: σr⟩,
                                    List.mem_cons.mpr (Or.inl rfl), hη, hΓ,
                                    ⟨slotLe_refl _, ⟨⟨hle, by
                                      intro _ hc2
                                      exact List.cons_ne_nil h1 hs hc2⟩, hrest⟩⟩,
                                    hcovΓ,
                                    stackCov_cons_intro (tyCov_refl _ _)
                                      (stackCov_cons_intro hcn hcovσ.2)⟩
                              | true =>
                                  simp only [step1, hco', hnorm', hthrow',
                                    reduceIte, List.cons_append, List.nil_append]
                                  have hle : tyLe (h1 :: hs) (n1 :: ns) := by
                                    have hle2 := tyLe_of_atom_cov
                                      (complNormals_cov hcov)
                                    rw [hnorm', hnorm] at hle2
                                    exact hle2
                                  have hcn : tyCov η' (h1 :: hs) (n1 :: ns) := by
                                    rw [← hnorm', ← hnorm]
                                    exact tyCov_complNormals hcovσ.1
                                  refine ⟨(⟨η', Γ', [.isValue (.boolean Bool.false)]
                                    :: (h1 :: hs) :: σr'⟩ : World)
                                    :: (⟨η', Γ', [.isValue (.boolean Bool.true)]
                                    :: [VTy.complT] :: σr'⟩ : World) :: [],
                                    ?_, ?_⟩
                                  · rfl
                                  · intro u' hu2
                                    simp only [List.mem_cons, List.mem_singleton] at hu2
                                    rcases hu2 with rfl | hu2
                                    · exact ⟨⟨η, Γ, [.isValue (.boolean Bool.false)]
                                        :: (n1 :: ns) :: σr⟩,
                                        List.mem_cons.mpr (Or.inl rfl), hη, hΓ,
                                        ⟨slotLe_refl _, ⟨⟨hle, by
                                          intro _ hc2
                                          exact List.cons_ne_nil h1 hs hc2⟩, hrest⟩⟩,
                                        hcovΓ,
                                        stackCov_cons_intro (tyCov_refl _ _)
                                          (stackCov_cons_intro hcn hcovσ.2)⟩
                                    · rcases hu2 with h2 | h2
                                      · subst h2
                                        exact ⟨⟨η, Γ, [.isValue (.boolean Bool.true)]
                                          :: [VTy.complT] :: σr⟩,
                                          List.mem_cons.mpr
                                            (Or.inr (List.mem_singleton.mpr rfl)),
                                          hη, hΓ, ⟨slotLe_refl _,
                                          ⟨slotLe_refl _, hrest⟩⟩, hcovΓ,
                                          stackCov_cons_intro (tyCov_refl _ _)
                                            (stackCov_cons_intro
                                              (tyCov_refl _ _) hcovσ.2)⟩
                                      · cases h2
theorem boolBranchTC_exits {site : Instr} {ts : Ty}
    {trueResult falseResult : TCResult} {fb : Flows}
    (h : boolBranchTC site ts trueResult falseResult = TCResult.flows fb) :
    fb.exits = Bool.true := by
  unfold boolBranchTC at h
  have hnr : ∀ s w, ts.foldl
      (fun acc a => mergeTC acc
        (match a with
         | .isValue (.boolean Bool.true) => trueResult
         | .isValue (.boolean Bool.false) => falseResult
         | .anyValue .bool => mergeTC trueResult falseResult
         | _ => .reject site "loop verdict is not boolean"))
      vacOk ≠ TCResult.reject s w := by
    intro s w hsw
    exact TCResult.noConfusion (h.symm.trans hsw)
  obtain ⟨-, heq⟩ := fold_merge_flows
    (fun a => match a with
      | .isValue (.boolean Bool.true) => trueResult
      | .isValue (.boolean Bool.false) => falseResult
      | .anyValue .bool => mergeTC trueResult falseResult
      | _ => .reject site "loop verdict is not boolean")
    ts vacOk hnr
  have hinj := TCResult.flows.inj (h.symm.trans heq)
  subst hinj
  simp [exitsT, vacOk]

/- ## THE NO-SILENT-FALLS INVARIANT: every checkSeq result that is
    flows with empty falls EXITED (re-derived on the flat
    completion universe). -/
theorem checkSeq_exits (sigs : SigTable) (r : Ty) (w : World) (seq : List Instr) :
    ∀ (fb : Flows), checkSeq sigs r w seq = TCResult.flows fb →
      fb.falls = [] → fb.exits = Bool.true := by
  induction sigs, r, w, seq using checkSeq.induct
  case case1 =>
    rename_i sigs r w
    intro fb h hf
    simp only [checkSeq] at h
    cases h
    have hf' : [w] = [] := hf
    exact absurd hf' (List.cons_ne_nil _ _)
  case case2 =>
    rename_i sigs r w tail ts σ' hσ hle
    intro fb h hf
    simp only [checkSeq, hσ, hle] at h
    have hinj := TCResult.flows.inj h
    subst hinj
    rfl
  case case3 =>
    rename_i sigs r w tail ts σ' hσ hnt
    intro fb h hf
    simp only [checkSeq, hσ] at h
    split at h
    · next hcond => exact absurd hcond hnt
    · exact TCResult.noConfusion h
  case case4 =>
    rename_i sigs r w tail hσ
    intro fb h hf
    simp only [checkSeq, hσ] at h
    exact TCResult.noConfusion h
  case case5 =>
    rename_i sigs r w t e rest hσ
    intro fb h hf
    simp only [checkSeq, hσ] at h
    exact TCResult.noConfusion h
  case case6 =>
    rename_i sigs r w t e rest ts σ' hσ ih2 ih1
    intro fb h hf
    simp only [checkSeq, hσ] at h
    obtain ⟨-, heq⟩ := fold_merge_flows _ ts vacOk (ne_reject_of_flows h)
    rw [heq] at h
    have hinj := TCResult.flows.inj h
    subst hinj
    rfl
  case case7 =>
    rename_i sigs r w x rest hlook ih1
    intro fb h hf
    simp only [checkSeq, hlook] at h
    exact ih1 fb h hf
  case case8 =>
    rename_i sigs r w x rest S hlook ih1
    intro fb h hf
    simp only [checkSeq, hlook] at h
    exact forkTC_exits h hf ih1
  case case9 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_5] at h
    exact ih1 fb h hf
  case case10 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_6] at h
    exact ih1 fb h hf
  case case11 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_7] at h
    exact ih1 fb h hf
  case case12 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_8] at h
    exact ih1 fb h hf
  case case13 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_9] at h
    exact ih1 fb h hf
  case case14 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_10] at h
    exact ih1 fb h hf
  case case15 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_11] at h
    exact ih1 fb h hf
  case case16 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_12] at h
    exact ih1 fb h hf
  case case17 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_13] at h
    exact ih1 fb h hf
  case case18 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_14] at h
    exact ih1 fb h hf
  case case19 =>
    rename_i sigs r w s x rest ih1
    intro fb h hf
    rw [checkSeq.eq_15] at h
    exact ih1 fb h hf
  case case20 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_16] at h
    exact ih1 fb h hf
  case case21 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_17] at h
    exact ih1 fb h hf
  case case22 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_18] at h
    exact ih1 fb h hf

  case case23 =>
    rename_i sigs r w ty x rest ih1
    intro fb h hf
    rw [checkSeq.eq_19] at h
    exact ih1 fb h hf
  case case24 =>
    rename_i sigs r w nm x rest ih1
    intro fb h hf
    rw [checkSeq.eq_20] at h
    exact ih1 fb h hf
  case case25 =>
    rename_i sigs r w b f x rest hfused ih1
    intro fb h hf
    rw [checkSeq.eq_21, if_pos hfused] at h
    exact ih1 fb h hf
  case case26 =>
    rename_i sigs r w b f x rest hfused hty
    intro fb h hf
    simp only [checkSeq] at h
    split at h
    · next hcond => exact absurd hcond hfused
    · rw [hty] at h
      dsimp only at h
      exact TCResult.noConfusion h
  case case27 =>
    rename_i sigs r w b f x rest hfused S hty ih1
    intro fb h hf
    simp only [checkSeq] at h
    split at h
    · next hcond => exact absurd hcond hfused
    · rw [hty] at h
      dsimp only at h
      exact markThrow_exits h hf ih1
  case case28 =>
    rename_i _body _rest hempty condTy hbool ihbody ihrestu ihrest _
    intro fb h hf
    rw [checkSeq, hempty] at h
    split at h
    · exact boolBranchTC_exits h
    · exact TCResult.noConfusion h
  case case29 =>
    rename_i _body _rest hempty condTy hnt
    intro fb h hf
    simp only [checkSeq, hempty] at h
    split at h
    · next hcond => exact absurd hcond hnt
    · exact TCResult.noConfusion h
  case case30 =>
    rename_i _body _rest hempty hnone
    intro fb h hf
    simp only [checkSeq, hempty, hnone] at h
    exact TCResult.noConfusion h
  case case31 =>
    rename_i cond loopBody loopRest hne
    intro fb h hf
    simp only [checkSeq] at h
    exact TCResult.noConfusion h
  case case32 =>
    rename_i sigs r w ex rest hdisj hty
    intro fb h hf
    simp only [checkSeq, hty] at h
    exact TCResult.noConfusion h
  case case33 =>
    rename_i sigs r w ex rest hdisj S hty ih1
    intro fb h hf
    simp only [checkSeq, hty] at h
    exact markThrow_exits h hf ih1
  case case34 =>
    rename_i sigs r w x rest f b dec hdec ih1
    intro fb h hf
    rw [checkSeq.eq_24, hdec] at h
    exact forkTC_exits h hf ih1
  case case35 =>
    rename_i sigs r w x rest f b hdec hlook
    intro fb h hf
    rw [checkSeq.eq_24, hdec, hlook] at h
    dsimp only at h
    exact TCResult.noConfusion h
  case case36 =>
    rename_i sigs r w x rest f b hdec S hlook ih1
    intro fb h hf
    rw [checkSeq.eq_24, hdec, hlook] at h
    first
    | exact ih1 fb h hf
    | (dsimp only at h; exact ih1 fb h hf)
    | exact ih1 fb (by dsimp only at h; exact h) hf
  case case37 =>
    rename_i sigs r w x rest dec hdec ih1
    intro fb h hf
    rw [checkSeq.eq_25] at h
    exact forkTC_exits h hf ih1
  case case38 =>
    rename_i sigs r w x rest hdec hlook
    intro fb h hf
    exact absurd hlook (by simp [primDecide])
  case case39 =>
    rename_i sigs r w x rest hdec S hlook ih1
    intro fb h hf
    exact absurd hlook (by simp [primDecide])
  case case40 =>
    rename_i sigs r w x rest dec hdec ih1
    intro fb h hf
    rw [checkSeq.eq_26] at h
    exact forkTC_exits h hf ih1
  case case41 =>
    rename_i sigs r w x rest hdec hlook
    intro fb h hf
    exact absurd hlook (by simp [primDecide])
  case case42 =>
    rename_i sigs r w x rest hdec S hlook ih1
    intro fb h hf
    exact absurd hlook (by simp [primDecide])
  case case43 =>
    rename_i sigs r w x p rest ps hT hpred hn hc ih1
    intro fb h hf
    simp only [checkSeq, hpred, hn, hc, hT] at h
    exact forkTC_exits h hf ih1
  case case44 =>
    rename_i sigs r w x p rest hT hlook hpred hn hc
    intro fb h hf
    simp only [checkSeq, hpred, hn, hc, hT, hlook] at h
    exact TCResult.noConfusion h
  case case45 =>
    rename_i sigs r w x p rest hT S hlook hpred hn hc ih1
    intro fb h hf
    simp only [checkSeq, hpred, hn, hc, hT, hlook] at h
    exact ih1 fb h hf
  case case46 =>
    rename_i sigs r w c body rest hpop
    intro fb h hf
    simp only [checkSeq, hpop] at h
    exact TCResult.noConfusion h
  case case47 =>
    rename_i sigs r w c body rest hpop ih2 ih1
    intro fb h hf
    simp only [checkSeq, hpop] at h
    cases hbody : checkSeq sigs r { η := w.η, Γ := w.Γ, σ := []} body with
    | reject s w' =>
        rw [hbody] at h
        simp only [checkLoopBody] at h
        exact TCResult.noConfusion h
    | flows fb₁ =>
        rw [hbody] at h
        simp only [checkLoopBody] at h
        split at h
        · cases hkf : fb₁.falls.foldl
              (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows with
          | reject s w' =>
              rw [hkf] at h
              dsimp only at h
              exact TCResult.noConfusion h
          | flows fr =>
              rw [hkf] at h
              dsimp only at h
              have hinj := TCResult.flows.inj h
              subst hinj
              match hfalls : fb₁.falls with
              | [] =>
                  rw [ih2 fb₁ hbody hfalls]
                  simp
              | u :: us =>
                  have hfr : fr.falls = [] := hf
                  rw [fold_noFlows_exits ih1 _ fr hkf hfr (by simp [hfalls])]
                  simp
        · exact TCResult.noConfusion h
  case case48 =>
    rename_i sigs r w c body rest hd htl hpop
    intro fb h hf
    simp only [checkSeq, hpop] at h
    exact TCResult.noConfusion h
  case case49 =>
    rename_i sigs r w x body rest hpop
    intro fb h hf
    simp only [checkSeq, hpop] at h
    exact TCResult.noConfusion h
  case case50 =>
    rename_i sigs r w x body rest hpop ih2 ih1
    intro fb h hf
    simp only [checkSeq, hpop] at h
    cases hbody : checkSeq sigs r { η := w.η, Γ := (x, langT) :: w.Γ, σ := []} body with
    | reject s w' =>
        rw [hbody] at h
        simp only [checkLoopBody] at h
        exact TCResult.noConfusion h
    | flows fb₁ =>
        rw [hbody] at h
        simp only [checkLoopBody] at h
        split at h
        · cases hkf : fb₁.falls.foldl
              (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows with
          | reject s w' =>
              rw [hkf] at h
              dsimp only at h
              exact TCResult.noConfusion h
          | flows fr =>
              rw [hkf] at h
              dsimp only at h
              have hinj := TCResult.flows.inj h
              subst hinj
              match hfalls : fb₁.falls with
              | [] =>
                  rw [ih2 fb₁ hbody hfalls]
                  simp
              | u :: us =>
                  have hfr : fr.falls = [] := hf
                  rw [fold_noFlows_exits ih1 _ fr hkf hfr (by simp [hfalls])]
                  simp
        · exact TCResult.noConfusion h
  case case51 =>
    rename_i sigs r w x body rest hd htl hpop
    intro fb h hf
    simp only [checkSeq, hpop] at h
    exact TCResult.noConfusion h
  case case52 =>
    rename_i sigs r w x elems body rest hempty ih2 ih1
    intro fb h hf
    simp only [checkSeq, hempty] at h
    cases hbody : checkSeq sigs r { η := w.η, Γ := (x, langT) :: w.Γ, σ := [] } body with
    | reject s w' =>
        rw [hbody] at h
        simp only [checkLoopBody] at h
        exact TCResult.noConfusion h
    | flows fb₁ =>
        rw [hbody] at h
        simp only [checkLoopBody] at h
        split at h
        · cases hkf : fb₁.falls.foldl
              (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows with
          | reject s w' =>
              rw [hkf] at h
              dsimp only at h
              exact TCResult.noConfusion h
          | flows fr =>
              rw [hkf] at h
              dsimp only at h
              have hinj := TCResult.flows.inj h
              subst hinj
              rw [← hempty] at hbody
              match hfalls : fb₁.falls with
              | [] =>
                  rw [ih2 fb₁ hbody hfalls]
                  simp
              | u :: us =>
                  have hfr : fr.falls = [] := hf
                  rw [fold_noFlows_exits ih1 _ fr hkf hfr (by simp [hfalls])]
                  simp
        · exact TCResult.noConfusion h
  case case53 =>
    rename_i sigs r w x elems body rest hne
    intro fb h hf
    cases hσ : w.σ with
    | nil => exact absurd hσ hne
    | cons a as =>
        simp only [checkSeq, hσ] at h
        exact TCResult.noConfusion h
  case case54 =>
    rename_i sigs r w rest hσ
    intro fb h hf
    simp only [checkSeq, hσ] at h
    exact TCResult.noConfusion h
  case case55 =>
    rename_i sigs r w rest ts σ' hσ ih1
    intro fb h hf
    simp only [checkSeq, hσ] at h
    obtain ⟨-, heq⟩ := fold_merge_flows _ ts vacOk (ne_reject_of_flows h)
    rw [heq] at h
    have hinj := TCResult.flows.inj h
    subst hinj
    rfl
  case case56 =>
    rename_i sigs r w i rest hdisj hstep
    intro fb h hf
    simp only [checkSeq, hstep] at h
    exact TCResult.noConfusion h
  case case57 =>
    rename_i sigs r w i rest hdisj ws' hstep ih1
    intro fb h hf
    simp only [checkSeq, hstep] at h
    exact forkTC_exits h hf ih1


/- ## Proof layer VI: the completion-stack identities

    Completions are stack values; every protocol step is a plain
    σ-operation. Runtime slots are singletons, so the identities
    are stated for singleton tops. -/

theorem checkSeq_kTest_normal {sigs : SigTable} {r : Ty} {W : World} {p : VTy}
    {σ' : List Ty} {rest : List Instr} (hσ : W.σ = [VTy.complN p] :: σ') :
    checkSeq sigs r W (.kTest :: rest)
      = checkSeq sigs r { W with σ := [.isValue (.boolean Bool.false)] :: [VTy.complN p] :: σ' } rest := by
  simp only [checkSeq, step1, hσ, complOnly, complNormals, complHasThrow, List.filterMap_cons, List.filterMap_nil, List.any_cons, List.any_nil, Bool.true_or, List.isEmpty_cons, ite_true, if_true, Bool.false_or, Bool.true_and, List.cons_append, List.nil_append, forkTC, List.foldl, mergeTC_noFlows]

theorem checkSeq_kTest_throw {sigs : SigTable} {r : Ty} {W : World}
    {σ' : List Ty} {rest : List Instr} (hσ : W.σ = [VTy.complT] :: σ') :
    checkSeq sigs r W (.kTest :: rest)
      = checkSeq sigs r { W with σ := [.isValue (.boolean Bool.true)] :: [VTy.complT] :: σ' } rest := by
  simp only [checkSeq, step1, hσ, complOnly, complNormals, complHasThrow, List.filterMap_cons, List.filterMap_nil, List.any_cons, List.any_nil, Bool.true_or, List.isEmpty_cons, ite_true, if_true, Bool.false_or, Bool.true_and, List.cons_append, List.nil_append, forkTC, List.foldl, mergeTC_noFlows]

theorem checkSeq_kUnwrap {sigs : SigTable} {r : Ty} {W : World} {p : VTy}
    {σ' : List Ty} {rest : List Instr} (hσ : W.σ = [VTy.complN p] :: σ') :
    checkSeq sigs r W (.kUnwrap :: rest)
      = checkSeq sigs r { W with σ := [p] :: σ' } rest := by
  simp only [checkSeq, step1, hσ, unwrapSlot, Option.map_some, forkTC, List.foldl,
    mergeTC_noFlows]

theorem checkSeq_pWrapC {sigs : SigTable} {r : Ty} {W : World} {v : JSValue}
    {σ' : List Ty} {rest : List Instr} (hσ : W.σ = [typeOfV v] :: σ')
    (hbar : isBareVTy (typeOfV v) = Bool.true) :
    checkSeq sigs r W (.kPrim1 .pWrapC :: rest)
      = checkSeq sigs r { W with σ := [VTy.complN (typeOfV v)] :: σ' } rest := by
  have hco : complOnly [typeOfV v] = Bool.false := by
    cases hv : typeOfV v with
    | complN p | complT =>
        rw [hv] at hbar
        simp [isBareVTy] at hbar
    | anyValue _ | isValue _ | desc _ | notPresent =>
        simp only [complOnly, hv, Bool.false_and, Bool.and_false]
  have hn : ¬(Bool.false = Bool.true) := by simp
  simp only [checkSeq, step1, hσ, hco, if_neg hn,
    bareSlot, hbar, Option.map_some, List.map, forkTC, List.foldl,
    mergeTC_noFlows]

theorem checkSeq_pThrowC {sigs : SigTable} {r : Ty} {W : World} {v : JSValue}
    {σ' : List Ty} {rest : List Instr} (hσ : W.σ = [typeOfV v] :: σ') :
    checkSeq sigs r W (.kPrim1 .pThrowC :: rest)
      = checkSeq sigs r { W with σ := [VTy.complT] :: σ' } rest := by
  simp only [checkSeq, step1, hσ, complOnly, complNormals, complHasThrow, List.filterMap_cons, List.filterMap_nil, List.any_cons, List.any_nil, Bool.true_or, List.isEmpty_cons, ite_true, if_true, Bool.false_or, Bool.true_and, List.cons_append, List.nil_append, forkTC, List.foldl, mergeTC_noFlows]

theorem isBareVTy_normalizeAtom (η : HeapCallableTy) (a : VTy) :
    isBareVTy (normalizeAtom η a) = isBareVTy a := by
  cases a with
  | complN p => rfl
  | isValue v =>
      cases v with
      | obj loc => rfl
      | undefined | null | boolean _ | number _ | str _ | listV _
        | descV _ | compl _ _ => rfl
  | complT | anyValue _ | desc _ | notPresent => rfl

theorem checkSeq_pThrowC_slot {sigs : SigTable} {r : Ty} {W : World} {t : VTy}
    {σ' : List Ty} {rest : List Instr} (hσ : W.σ = [t] :: σ') :
    checkSeq sigs r W (.kPrim1 .pThrowC :: rest)
      = checkSeq sigs r { W with σ := [VTy.complT] :: σ' } rest := by
  simp only [checkSeq, step1, hσ, complOnly, complNormals, complHasThrow, List.filterMap_cons, List.filterMap_nil, List.any_cons, List.any_nil, Bool.true_or, List.isEmpty_cons, ite_true, if_true, Bool.false_or, Bool.true_and, List.cons_append, List.nil_append, forkTC, List.foldl, mergeTC_noFlows]

theorem checkSeq_pWrapC_slot {sigs : SigTable} {r : Ty} {W : World} {t : VTy}
    {σ' : List Ty} {rest : List Instr} (hσ : W.σ = [t] :: σ')
    (hbar : isBareVTy t = Bool.true) :
    checkSeq sigs r W (.kPrim1 .pWrapC :: rest)
      = checkSeq sigs r { W with σ := [VTy.complN t] :: σ' } rest := by
  have hco : complOnly [t] = Bool.false := by
    cases hv : t with
    | complN p | complT =>
        rw [hv] at hbar
        simp [isBareVTy] at hbar
    | anyValue _ | isValue _ | desc _ | notPresent =>
        simp only [complOnly, hv, Bool.false_and, Bool.and_false]
  have hn : ¬(Bool.false = Bool.true) := by simp
  simp only [checkSeq, step1, hσ, hco, if_neg hn,
    bareSlot, hbar, Option.map_some, List.map, forkTC, List.foldl,
    mergeTC_noFlows]

/- ## Proof layer VII: the completion-protocol sr arms

    The machine is compl-as-value; the bridge is the pointwise
    singleton map (typeOfV completion-aware). Each arm is the
    identity transported across frameChecks. -/

theorem merge_vacOk_terminal {sigs : SigTable} {r : Ty} {W : World} {seq : List Instr}
    {fb : Flows}
    (h : mergeTC vacOk (checkSeq sigs r W seq) = TCResult.flows fb)
    (ht : terminal fb = Bool.true) :
    ∃ fbr, checkSeq sigs r W seq = TCResult.flows fbr ∧ terminal fbr = Bool.true := by
  cases hres : checkSeq sigs r W seq with
  | reject s w =>
      have hrej : mergeTC vacOk (TCResult.reject s w) = TCResult.reject s w := rfl
      rw [hres, hrej] at h
      exact TCResult.noConfusion h
  | flows fbr =>
      refine ⟨fbr, rfl, ?_⟩
      have hmerge : mergeTC vacOk (TCResult.flows fbr)
          = TCResult.flows
              { exits := Bool.true || fbr.exits, throws := Bool.false || fbr.throws,
                falls := [] ++ fbr.falls, assumes := [] ++ fbr.assumes } := rfl
      rw [hres, hmerge] at h
      have hinj := TCResult.flows.inj h
      subst hinj
      unfold terminal at ht ⊢
      have hfl : fbr.falls = [] := by simpa using ht
      rw [checkSeq_exits sigs r W seq fbr hres hfl]
      simp only [hfl]
      trivial

/-- kIte on a DECIDED singleton verdict: the fold is exactly the
    vacOk-merge of the chosen branch's continuation. -/
theorem checkSeq_kIte_true {sigs : SigTable} {r : Ty} {W : World} {t e : List Instr}
    {rest : List Instr} {σ' : List Ty}
    (hσ : W.σ = [.isValue (.boolean Bool.true)] :: σ') :
    checkSeq sigs r W (.kIte t e :: rest)
      = mergeTC vacOk (checkSeq sigs r { W with σ := σ' } (t ++ rest)) := by
  simp only [checkSeq, hσ, List.foldl]

theorem checkSeq_kIte_false {sigs : SigTable} {r : Ty} {W : World} {t e : List Instr}
    {rest : List Instr} {σ' : List Ty}
    (hσ : W.σ = [.isValue (.boolean Bool.false)] :: σ') :
    checkSeq sigs r W (.kIte t e :: rest)
      = mergeTC vacOk (checkSeq sigs r { W with σ := σ' } (e ++ rest)) := by
  simp only [checkSeq, hσ, List.foldl]

/-- sr_kIte: one machine step through a decided verdict commutes
    with the checker's dispatch. -/
theorem sr_kIte_loud {sigs : SigTable} {η : HeapCallableTy} {t e : List Instr}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»} {v : JSValue}
    (hv : ∀ b, v ≠ JSValue.boolean b)
    (h : frameOk sigs η none ⟨.kIte t e :: rest, env, v :: eval, ret⟩) : False := by
  obtain ⟨-, hchk⟩ := h
  rw [frameChecks] at hchk
  simp only [frameWorld, List.map_cons] at hchk
  have hrej : checkSeq sigs (sigRetTy sigs ret)
      { η := η, Γ := envTyOf η env,
        σ := [normalizeAtom η (typeOfV v)]
          :: eval.map (fun v => [normalizeAtom η (typeOfV v)])} (.kIte t e :: rest)
      = TCResult.reject (.kIte t e) "kIte: verdict is not boolean" := by
    cases v with
    | undefined => simp only [checkSeq, typeOfV, normalizeAtom, List.foldl, vacOk, mergeTC]
    | null => simp only [checkSeq, typeOfV, normalizeAtom, List.foldl, vacOk, mergeTC]
    | boolean b => exact absurd rfl (hv b)
    | number n => simp only [checkSeq, typeOfV, normalizeAtom, List.foldl, vacOk, mergeTC]
    | str s => simp only [checkSeq, typeOfV, normalizeAtom, List.foldl, vacOk, mergeTC]
    | listV l => simp only [checkSeq, typeOfV, normalizeAtom, List.foldl, vacOk, mergeTC]
    | obj o =>
        simp only [checkSeq, typeOfV, normalizeAtom, List.foldl, vacOk, mergeTC]
    | descV d => simp only [checkSeq, typeOfV, normalizeAtom, List.foldl, vacOk, mergeTC]
    | compl b pv =>
        cases b <;> simp only [checkSeq, typeOfV, normalizeAtom, List.foldl, vacOk, mergeTC]
  rw [hrej] at hchk
  exact hchk

/- ## Proof layer XVII: frameTyped (the type-machine judgement) and
    its step transfers. The abstraction function is frameWorld
    (defined with the bridge, above). -/

/-- The type machine accepts the abstracted frame: every
    exploration path returns inside r. -/
def frameTyped (sigs : SigTable) (η : HeapCallableTy) (r : Ty)
    (f : Fr) : Prop :=
  match checkSeq sigs r (frameWorld η f) f.stmts with
  | .flows fb => terminal fb = Bool.true  -- every world returns
  | _ => False

theorem frameTyped_eq_frameChecks (sigs : SigTable) (η : HeapCallableTy)
    (f : Fr) :
    frameTyped sigs η (sigRetTy sigs f.ret) f
      = frameChecks sigs η f := rfl

/-- kIte transfer: dispatching the singleton verdict atom equals the
    machine's jump. -/
theorem frameTyped_kIte {sigs : SigTable} {η : HeapCallableTy} {b : Bool}
    {t e : List Instr}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»} {r : Ty}
    (h : frameTyped sigs η r ⟨.kIte t e :: rest, env, .boolean b :: eval, ret⟩) :
    frameTyped sigs η r ⟨(if b then t else e) ++ rest, env, eval, ret⟩ := by
  simp only [frameTyped, frameWorld, Fr.stmts, Fr.env, Fr.eval, List.map_cons] at h ⊢
  cases hb : b with
  | true =>
      rw [hb] at h
      have hslot : [normalizeAtom η (typeOfV (JSValue.boolean Bool.true))]
          = [VTy.isValue (JSValue.boolean Bool.true)] := rfl
      rw [hslot] at h
      rw [checkSeq_kIte_true rfl] at h
      rw [if_pos rfl]
      cases hres : checkSeq sigs r
          { η := η, Γ := envTyOf η env,
            σ := eval.map (fun v => [normalizeAtom η (typeOfV v)]) } (t ++ rest) with
      | reject s w =>
          have hrej : mergeTC vacOk (TCResult.reject s w) = TCResult.reject s w := rfl
          rw [hres, hrej] at h
          exact h.elim
      | flows fbr =>
          cases hm : mergeTC vacOk (checkSeq sigs r
              { η := η, Γ := envTyOf η env,
                σ := eval.map (fun v => [normalizeAtom η (typeOfV v)]) } (t ++ rest)) with
          | reject s w =>
              rw [hm] at h
              exact h.elim
          | flows fbm =>
              rw [hm] at h
              obtain ⟨fbr', hfb, htr⟩ := merge_vacOk_terminal hm h
              have hbr' : fbr' = fbr := TCResult.flows.inj (hfb.symm.trans hres)
              subst hbr'
              exact htr
  | false =>
      rw [hb] at h
      have hslot : [normalizeAtom η (typeOfV (JSValue.boolean Bool.false))]
          = [VTy.isValue (JSValue.boolean Bool.false)] := rfl
      rw [hslot] at h
      rw [checkSeq_kIte_false rfl] at h
      rw [if_neg (by decide)]
      cases hres : checkSeq sigs r
          { η := η, Γ := envTyOf η env,
            σ := eval.map (fun v => [normalizeAtom η (typeOfV v)]) } (e ++ rest) with
      | reject s w =>
          have hrej : mergeTC vacOk (TCResult.reject s w) = TCResult.reject s w := rfl
          rw [hres, hrej] at h
          exact h.elim
      | flows fbr =>
          cases hm : mergeTC vacOk (checkSeq sigs r
              { η := η, Γ := envTyOf η env,
                σ := eval.map (fun v => [normalizeAtom η (typeOfV v)]) } (e ++ rest)) with
          | reject s w =>
              rw [hm] at h
              exact h.elim
          | flows fbm =>
              rw [hm] at h
              obtain ⟨fbr', hfb, htr⟩ := merge_vacOk_terminal hm h
              have hbr' : fbr' = fbr := TCResult.flows.inj (hfb.symm.trans hres)
              subst hbr'
              exact htr

/-- The loud kIte states: the type machine rejects an empty or
    non-boolean verdict slot. -/
theorem frameTyped_kIte_reject_nil {sigs : SigTable} {η : HeapCallableTy} {r : Ty}
    {t e : List Instr}
    {rest : List Instr} {env : Env} {ret : «String»} :
    frameTyped sigs η r ⟨.kIte t e :: rest, env, [], ret⟩ = False := by
  simp only [frameTyped, frameWorld, List.map, checkSeq]

theorem frameTyped_kIte_reject_nonbool {sigs : SigTable} {η : HeapCallableTy}
    {r : Ty} {t e : List Instr}
    {rest : List Instr} {env : Env} {eval' : List JSValue} {ret : «String»} {v : JSValue}
    (hv : ∀ b, v ≠ JSValue.boolean b) :
    frameTyped sigs η r ⟨.kIte t e :: rest, env, v :: eval', ret⟩ = False := by
  cases v with
  | boolean b => exact absurd rfl (hv b)
  | undefined | null | number _ | str _ | obj _ | listV _ | descV _ =>
      simp only [frameTyped, frameWorld, List.map, List.map_cons, typeOfV,
        normalizeAtom, checkSeq,
        List.foldl_cons, List.foldl_nil, mergeTC]
      rfl
  | compl a b =>
      cases a <;>
        simp only [frameTyped, frameWorld, List.map, List.map_cons, typeOfV,
          normalizeAtom, checkSeq,
          List.foldl_cons, List.foldl_nil, mergeTC]
      all_goals rfl

/-- kPop transfer. -/
theorem frameTyped_kPop {sigs : SigTable} {η : HeapCallableTy} {w : JSValue}
    {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»} {r : Ty}
    (h : frameTyped sigs η r ⟨.kPop :: rest, env, w :: eval, ret⟩) :
    frameTyped sigs η r ⟨rest, env, eval, ret⟩ := by
  simp only [frameTyped, frameWorld, Fr.stmts, Fr.env, Fr.eval, List.map_cons] at h ⊢
  rw [checkSeq_kPop rfl] at h
  exact h

theorem frameTyped_kPop_reject_nil {sigs : SigTable} {η : HeapCallableTy} {r : Ty}
    {rest : List Instr}
    {env : Env} {ret : «String»} :
    frameTyped sigs η r ⟨.kPop :: rest, env, [], ret⟩ = False := by
  simp only [frameTyped, frameWorld, List.map, checkSeq, step1]

/-- kSet transfer. -/
theorem frameTyped_kSet {sigs : SigTable} {η : HeapCallableTy} {x : «String»}
    {w : JSValue} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»} {r : Ty}
    (h : frameTyped sigs η r ⟨.kSet x :: rest, env, w :: eval, ret⟩) :
    frameTyped sigs η r ⟨rest, (x, w) :: env, eval, ret⟩ := by
  simp only [frameTyped, frameWorld, Fr.stmts, Fr.env, Fr.eval, List.map_cons] at h ⊢
  rw [checkSeq_kSet rfl] at h
  rw [envTyOf_cons]
  exact h

theorem frameTyped_kSet_reject_nil {sigs : SigTable} {η : HeapCallableTy} {r : Ty}
    {x : «String»} {rest : List Instr}
    {env : Env} {ret : «String»} :
    frameTyped sigs η r ⟨.kSet x :: rest, env, [], ret⟩ = False := by
  simp only [frameTyped, frameWorld, List.map, checkSeq, step1]

/-- kEval of a literal — ALL value shapes (compl literals use the
    checker's dedicated push arms; everything else the generic one). -/
theorem frameTyped_kEval_const {sigs : SigTable} {η : HeapCallableTy} {v : JSValue}
    {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»} {r : Ty}
    (h : frameTyped sigs η r ⟨.kEval (.const v) :: rest, env, eval, ret⟩) :
    frameTyped sigs η r ⟨rest, env, v :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, Fr.stmts, Fr.env, Fr.eval, List.map_cons] at h ⊢
  rw [checkSeq_kEval_const] at h
  exact h

/- ## Proof layer XVIII: THE SR_arm PREDICATE and the arm theorems

    SR_arm h s r, literally as specified: s is ANY value machine
    state, r ANY destiny.
      pre     = h inserted as the next step before s
      pre_t   = the typed abstraction of pre (frameWorld, inside
                frameTyped/frameChecks — no new abstraction functions)
      post    = fstep reg pre (the machine computes it — never
                transcribed)
      post_t  = the typed abstraction of post
    SR_arm h s r = registry premise → (pre_t inside r) →
                   (post_t inside r).

    stateTyped is the honest state abstraction: every frame at its
    OWN destiny (machineRet ties the bottom frame's destiny to r);
    the frame DIRECTLY UNDER a running callee carries the
    UNION-ANTICIPATED judgment — literally what the caller's own
    kCall check established (complTy of the callee's declared
    judgement pushed on the caller's stack) — so the kCall arm
    transfers it VERBATIM, no monotonicity needed. The refinement
    (anticipated union → delivered singleton) is the kRet arm's
    business. -/

/-- Insert h as the next instruction of the head frame (identity on
    done/fell — no head frame to extend). -/
def withHead (h : Instr) (m : FM) : FM :=
  match m with
  | .frames (f :: fs) heap nl =>
      .frames ({ f with stmts := h :: f.stmts } :: fs) heap nl
  | _ => m

/-- Judgment for a frame DIRECTLY UNDER a running callee: the
    union-anticipated check — exactly what the caller's own kCall
    check established. -/
def frameOkUnder (sigs : SigTable) (η : HeapCallableTy)
    (callee : «String») (f : Fr) : Prop :=
  match checkSeq sigs (sigRetTy sigs f.ret)
    { η := η, Γ := envTyOf η f.env,
      σ := complTy (sigCompls sigs callee)
          :: f.eval.map (fun v => [normalizeAtom η (typeOfV v)]) }
    f.stmts with
  | .flows fb => terminal fb = Bool.true
  | _ => False

/-- Each frame at its own destiny; the frame under f anticipates
    f's declared completions. -/
def framesTypedFrom (η : HeapCallableTy) (sigs : SigTable)
    (above : Option «String») : List Fr → Prop
  | [] => True
  | f :: fs =>
      (match above with
       | none => frameChecks sigs η f
       | some n => frameOkUnder sigs η n f)
      ∧ framesTypedFrom η sigs (some f.ret) fs

/-- The type machine's judgment on a WHOLE value state: every frame
    typed (heads at own destinies, under-callees anticipated), the
    bottom frame's destiny = r, the final answer inside r, stuck
    states untyped. The heap typing is carried with the frame typing:
    its callability projection is exactly the η used by checkSeq. -/
def stateTyped (sigs : SigTable) (η : HeapCallableTy) (r : Ty)
    (m : FM) : Prop :=
  match m with
  | .frames [] _ _ => False
  | .frames (f :: fs) heap nl =>
      heapCallabilityOk heap η
      ∧ heapOk heap nl (f :: fs)
      ∧ framesWf heap nl (f :: fs)
      ∧ framesTypedFrom η sigs none (f :: fs)
      ∧ machineRet sigs (f :: fs) = r
  | .fdone v _ heap _ _ =>
      tmoves [normalizeAtom η (typeOfV v)] r = Bool.true
  | .fell _ _ _ _ => False

/-- THE SR PREDICATE — one shape; every arm theorem instantiates it.
    The registry premise is part of the predicate: the callee's
    body is the one thing the caller's check never sees, so the
    kCall arm draws its post-frame typing from the registry's
    certificates. -/

def slotClosed (p : Ty) : Prop :=
  ∀ {t' t : Ty}, slotLe t' t → tmoves t' p = Bool.true → tmoves t p = Bool.true

theorem leTy_up_closed {ts' ts ps : List Ty} (hslots : slotsLe ts' ts)
    (hps : ∀ p ∈ ps, slotClosed p) (hle : leTy ts' ps = Bool.true) :
    leTy ts ps = Bool.true := by
  revert ps
  induction ts' generalizing ts with
  | nil =>
      intro ps hps hle
      cases ts with
      | nil => cases ps <;> simp [leTy] at hle ⊢
      | cons t ts => cases hslots
  | cons t' ts' ih =>
      intro ps hps hle
      cases ts with
      | nil => cases hslots
      | cons t ts =>
          obtain ⟨hslot, hslots'⟩ := hslots
          cases ps with
          | nil => simp [leTy] at hle
          | cons p ps =>
              simp only [leTy] at hle ⊢
              obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _) |>.mp hle
              have h1' : tmoves t p = Bool.true := hps p (by simp) hslot h1
              have h2' : leTy ts ps = Bool.true :=
                ih hslots' (fun q hq => hps q (by simp [hq])) h2
              exact (Bool.and_eq_true _ _) |>.mpr ⟨h1', h2'⟩

def atomStable : VTy → Prop
  | .anyValue .desc => False
  | .complN p => atomStable p
  | _ => True

def tyStable (t : Ty) : Prop := ∀ a ∈ t, atomStable a

theorem atomCov_flat_intro {η : HeapCallableTy} {a' a : VTy}
    (hmove : tmovesV a' a = Bool.true) (hdec : decAgree η a' a)
    (hne : ¬ ∃ p q, a' = .complN p ∧ a = .complN q) :
    atomCov η a' a := by
  cases a' with
  | complN p =>
      cases a with
      | complN q => exact absurd ⟨p, q, rfl, rfl⟩ hne
      | complT | anyValue _ | isValue _ | desc _ | notPresent =>
          simp only [atomCov]
          exact ⟨hmove, hdec, True.intro⟩
  | complT | anyValue _ | isValue _ | desc _ | notPresent =>
      cases a with
      | complN q | complT | anyValue _ | isValue _ | desc _ | notPresent =>
          simp only [atomCov]
          exact ⟨hmove, hdec, True.intro⟩

theorem atomCov_of_stable {η : HeapCallableTy} {a' a : VTy}
    (hnorm : normalizeAtom η a' = a') (hmove : tmovesV a' a = Bool.true)
    (hstable : atomStable a) : atomCov η a' a := by
  cases a with
  | anyValue c =>
      cases c with
      | desc => exact absurd hstable (by simp [atomStable])
      | undef | null | bool | num | str | obj callable | list =>
          refine atomCov_flat_intro hmove ?_ (by
            intro ⟨p, q, heq, heq2⟩
            simp_all)
          intro f dec hf
          cases a' with
          | complN p | complT | desc fs | notPresent =>
              simp_all [predDecide, tmovesV, tagOf]
          | isValue v =>
              cases v with
              | obj loc => simp [normalizeAtom] at hnorm
              | undefined | null | boolean _ | number _ | str _
                | listV _ | descV _ | compl _ _ =>
                  unfold predDecide at hf
                  split at hf
                  all_goals first
                    | (injection hf with hdec
                       subst hdec
                       simp_all [isCallableAtom, tmovesV, tagOf])
                    | cases hf
          | anyValue c' =>
              cases c' with
              | desc => simp_all [tmovesV, tagOf]
              | undef | null | bool | num | str | obj callable | list =>
                  simp_all [predDecide, isCallableAtom, tmovesV]
  | complN p =>
      cases a' with
      | complN p' =>
          have hpnorm : normalizeAtom η p' = p' := by
            simpa [normalizeAtom] using hnorm
          have hp : tmovesV p' p = Bool.true := by
            simpa [tmovesV] using hmove
          exact atomCov_complN_of (atomCov_of_stable hpnorm hp hstable)
      | complT | anyValue _ | isValue _ | desc _ | notPresent =>
          simp [tmovesV] at hmove
  | complT | isValue _ | desc _ | notPresent =>
      exact atomCov_flat_intro hmove
        (decAgree_of_pure_cover hmove (by trivial)) (by
          intro ⟨p, q, heq, heq2⟩
          simp_all)

def pendingStable : Pending → Prop
  | .normal t => tyStable t
  | .throw => True

def sigParamsClosed (sigs : SigTable) : Prop :=
  ∀ n ps ret, sigFind sigs n = some (ps, ret) →
    (∀ p ∈ ps, slotClosed p)
      ∧ ∀ c ∈ ret, pendingStable c

/-- kRet inversion: an accepted kRet had a top slot below the
    frame's destiny. -/
theorem checkSeq_kRet_elim {sigs : SigTable} {r : Ty} {W : World}
    {rest : List Instr} {fb : Flows}
    (h : checkSeq sigs r W (.kRet :: rest) = TCResult.flows fb) :
    ∃ t σ', W.σ = t :: σ' ∧ tmoves t r = Bool.true := by
  cases hσ : W.σ with
  | nil =>
      rw [checkSeq, hσ] at h
      cases h
  | cons t σ' =>
      rw [checkSeq, hσ] at h
      cases htr : tmoves t r with
      | false =>
          simp only [htr, reduceIte] at h
          cases h
      | true => exact ⟨t, σ', rfl, htr⟩

def SR_arm (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (h : Instr) (s : FM) (r : Ty) : Prop :=
  registryCertified sigs reg →
    closedRegistry sigs reg →
      sigParamsClosed sigs →
        stateTyped sigs η r (withHead h s) →
          ∃ η', stateTyped sigs η' r (fstep reg (withHead h s))

/- Machine-ret stability: swapping the head frame's non-ret fields
    (a same-frame step) does not change the machine's answer type;
    pushing a frame above does not either. -/
theorem getLast?_cons_cons {x y : Fr} {fs : List Fr} :
    (x :: y :: fs).getLast? = (y :: fs).getLast? := by
  cases fs <;> rfl

theorem machineRet_cons_cons {sigs : SigTable} {x y : Fr} {fs : List Fr} :
    machineRet sigs (x :: y :: fs) = machineRet sigs (y :: fs) := by
  simp only [machineRet, getLast?_cons_cons]

theorem machineRet_head_swap {sigs : SigTable} {s₁ e₁ v₁ s₂ e₂ v₂ : _} {ret : «String»}
    {fs : List Fr} :
    machineRet sigs (⟨s₁, e₁, v₁, ret⟩ :: fs)
      = machineRet sigs (⟨s₂, e₂, v₂, ret⟩ :: fs) := by
  cases fs <;> simp [machineRet]

/-- The bridge commutes with zip: the machine's env-zipping is the
    certificate's Γ-zipping. -/
theorem envTyOf_zipTy : ∀ (η : HeapCallableTy) (ps : List «String»)
    (vs : List JSValue),
    envTyOf η (ps.zip vs)
      = zipTy ps (vs.map (fun v => [normalizeAtom η (typeOfV v)])) := by
  intro η ps
  induction ps with
  | nil => intro vs; cases vs <;> simp [envTyOf, zipTy]
  | cons p pst ih =>
      intro vs
      cases vs with
      | nil => simp [List.zip, envTyOf, zipTy]
      | cons v vt =>
          show envTyOf η ((p, v) :: pst.zip vt)
            = (p, [normalizeAtom η (typeOfV v)])
                :: zipTy pst (vt.map (fun v => [normalizeAtom η (typeOfV v)]))
          rw [envTyOf_cons, ih]

def frameLocs (f : Fr) : List Nat :=
  f.eval.flatMap locsOf ++ (f.env.map Prod.snd).flatMap locsOf

theorem heapOk_cons_intro {heap : Heap} {nl : Nat} {f : Fr} {fs : List Fr}
    (hhead : ∀ l ∈ frameLocs f, l < nl ∧ (heap l).isSome = Bool.true)
    (htl : heapOk heap nl fs) : heapOk heap nl (f :: fs) := ⟨hhead, htl⟩

theorem heapOk_cons_elim {heap : Heap} {nl : Nat} {f : Fr} {fs : List Fr}
    (h : heapOk heap nl (f :: fs)) :
    (∀ l ∈ frameLocs f, l < nl ∧ (heap l).isSome = Bool.true)
      ∧ heapOk heap nl fs := h

theorem heapOk_cons_mono {heap : Heap} {nl : Nat} {f g : Fr} {fs : List Fr}
    (hsub : ∀ l ∈ frameLocs g, l ∈ frameLocs f)
    (h : heapOk heap nl (f :: fs)) : heapOk heap nl (g :: fs) :=
  ⟨fun l hl => h.1 l (hsub l hl), h.2⟩

theorem mem_frameLocs_cons_eval {stmts : List Instr} {env : Env} {v : JSValue}
    {eval : List JSValue} {ret : «String»} {l : Nat}
    (h : l ∈ frameLocs ⟨stmts, env, v :: eval, ret⟩) :
    l ∈ locsOf v ∨ l ∈ (List.flatMap locsOf eval
      ++ List.flatMap locsOf (List.map Prod.snd env)) := by
  have h1 : l ∈ (locsOf v ++ List.flatMap locsOf eval)
      ++ List.flatMap locsOf (List.map Prod.snd env) := h
  rcases List.mem_append.mp h1 with h1 | h1
  · rcases List.mem_append.mp h1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (List.mem_append.mpr (Or.inl h1))
  · exact Or.inr (List.mem_append.mpr (Or.inr h1))

theorem mem_frameLocs_eval_rest {i : Instr} {stmts : List Instr} {env : Env}
    {w : JSValue} {eval : List JSValue} {ret : «String»} {l : Nat}
    (h : l ∈ frameLocs ⟨stmts, env, eval, ret⟩) :
    l ∈ (locsOf w ++ List.flatMap locsOf eval)
      ++ List.flatMap locsOf (List.map Prod.snd env) := by
  have h1 : l ∈ List.flatMap locsOf eval
      ++ List.flatMap locsOf (List.map Prod.snd env) := h
  rcases List.mem_append.mp h1 with h1 | h1
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h1)))
  · exact List.mem_append.mpr (Or.inr h1)

theorem mem_frameLocs_env_exchange {i : Instr} {stmts : List Instr} {x : «String»}
    {env : Env} {w : JSValue} {eval : List JSValue} {ret : «String»} {l : Nat}
    (h : l ∈ frameLocs ⟨stmts, (x, w) :: env, eval, ret⟩) :
    l ∈ (locsOf w ++ List.flatMap locsOf eval)
      ++ List.flatMap locsOf (List.map Prod.snd env) := by
  have h1 : l ∈ List.flatMap locsOf eval
      ++ (locsOf w ++ List.flatMap locsOf (List.map Prod.snd env)) := h
  rcases List.mem_append.mp h1 with h1 | h1
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h1)))
  · rcases List.mem_append.mp h1 with h1 | h1
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h1)))
    · exact List.mem_append.mpr (Or.inr h1)

theorem mem_locsList : ∀ {vs : List JSValue} {l : Nat},
    l ∈ locsList vs → ∃ v ∈ vs, l ∈ locsOf v := by
  intro vs
  induction vs with
  | nil => intro l h; simp [locsList] at h
  | cons v vs' ih =>
      intro l h
      simp only [locsList, List.mem_append] at h
      rcases h with h | h
      · exact ⟨v, List.mem_cons.mpr (Or.inl rfl), h⟩
      · obtain ⟨v', hv', hl⟩ := ih h
        exact ⟨v', List.mem_cons.mpr (Or.inr hv'), hl⟩

theorem heapOk_drop_eval {heap : Heap} {nl : Nat} {i : Instr} {stmts : List Instr}
    {env : Env} {w : JSValue} {eval : List JSValue} {ret : «String»} {fs : List Fr}
    (h : heapOk heap nl (⟨i :: stmts, env, w :: eval, ret⟩ :: fs)) :
    heapOk heap nl (⟨stmts, env, eval, ret⟩ :: fs) :=
  heapOk_cons_mono (g := ⟨stmts, env, eval, ret⟩) (by
    intro l hl
    show l ∈ frameLocs ⟨i :: stmts, env, w :: eval, ret⟩
    exact mem_frameLocs_eval_rest (i := i) (w := w) hl) h

theorem heapOk_push_eval {heap : Heap} {nl : Nat} {i : Instr} {stmts : List Instr}
    {env : Env} {v : JSValue} {eval : List JSValue} {ret : «String»} {fs : List Fr}
    (hv : ∀ l ∈ locsOf v, l < nl ∧ (heap l).isSome = Bool.true)
    (h : heapOk heap nl (⟨i :: stmts, env, eval, ret⟩ :: fs)) :
    heapOk heap nl (⟨stmts, env, v :: eval, ret⟩ :: fs) :=
  heapOk_cons_intro (f := ⟨stmts, env, v :: eval, ret⟩) (by
    intro l hl
    rcases mem_frameLocs_cons_eval hl with hl | hl
    · exact hv l hl
    · exact h.1 l hl) h.2

theorem heapOk_push_env {heap : Heap} {nl : Nat} {i : Instr} {stmts : List Instr}
    {x : «String»} {env : Env} {w : JSValue} {eval : List JSValue} {ret : «String»}
    {fs : List Fr}
    (h : heapOk heap nl (⟨i :: stmts, env, w :: eval, ret⟩ :: fs)) :
    heapOk heap nl (⟨stmts, (x, w) :: env, eval, ret⟩ :: fs) :=
  heapOk_cons_intro (f := ⟨stmts, (x, w) :: env, eval, ret⟩) (by
    intro l hl
    exact h.1 l (mem_frameLocs_env_exchange (i := i) hl)) h.2

theorem zip_snd_mem {α β : Type} : ∀ (xs : List α) (ys : List β)
    {x : α} {y : β}, (x, y) ∈ List.zip xs ys → y ∈ ys := by
  intro xs
  induction xs with
  | nil => intro ys x y h; simp [List.zip] at h
  | cons a xs ih =>
      intro ys x y h
      cases ys with
      | nil => simp [List.zip] at h
      | cons b ys =>
          have h1 : (x, y) = (a, b) ∨ (x, y) ∈ List.zip xs ys := by
            simpa [List.zip] using h
          rcases h1 with h1 | h1
          · injection h1 with h1 h2
            subst h1
            subst h2
            simp
          · have h2 : y ∈ ys := ih ys h1
            simp [h2]

theorem mem_flatMap_of_mem_drop {eval : List JSValue} {n : Nat} {l : Nat}
    (h : l ∈ (eval.drop n).flatMap locsOf) : l ∈ eval.flatMap locsOf := by
  obtain ⟨v, hv, hl⟩ := List.mem_flatMap.mp h
  exact List.mem_flatMap.mpr ⟨v, List.mem_of_mem_drop hv, hl⟩

theorem mem_flatMap_of_mem_take {eval : List JSValue} {n : Nat} {l : Nat}
    (h : l ∈ (eval.take n).flatMap locsOf) : l ∈ eval.flatMap locsOf := by
  obtain ⟨v, hv, hl⟩ := List.mem_flatMap.mp h
  exact List.mem_flatMap.mpr ⟨v, List.mem_of_mem_take hv, hl⟩

theorem heapOk_swap_head {heap : Heap} {nl : Nat} {i : Instr} {stmts : List Instr}
    {env : Env} {v w : JSValue} {eval : List JSValue} {ret : «String»} {fs : List Fr}
    (hvl : locsOf v = locsOf w)
    (h : heapOk heap nl (⟨i :: stmts, env, w :: eval, ret⟩ :: fs)) :
    heapOk heap nl (⟨stmts, env, v :: eval, ret⟩ :: fs) :=
  heapOk_cons_mono (f := ⟨i :: stmts, env, w :: eval, ret⟩)
    (g := ⟨stmts, env, v :: eval, ret⟩) (by
      intro l hl
      have h1 : l ∈ (locsOf v ++ List.flatMap locsOf eval)
          ++ List.flatMap locsOf (List.map Prod.snd env) := hl
      rcases List.mem_append.mp h1 with h1 | h1
      · rcases List.mem_append.mp h1 with h1 | h1
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
            (Or.inl (by rw [← hvl]; exact h1))))
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h1)))
      · exact List.mem_append.mpr (Or.inr h1)) h

theorem heapOk_bool_swap {heap : Heap} {nl : Nat} {i : Instr} {stmts : List Instr}
    {env : Env} {w : JSValue} {eval : List JSValue} {ret : «String»} {fs : List Fr}
    {b : Bool}
    (h : heapOk heap nl (⟨i :: stmts, env, w :: eval, ret⟩ :: fs)) :
    heapOk heap nl (⟨stmts, env, .boolean b :: eval, ret⟩ :: fs) :=
  heapOk_cons_mono (f := ⟨i :: stmts, env, w :: eval, ret⟩)
    (g := ⟨stmts, env, .boolean b :: eval, ret⟩) (by
      intro l hl
      have h1 : l ∈ (locsOf (JSValue.boolean b) ++ List.flatMap locsOf eval)
          ++ List.flatMap locsOf (List.map Prod.snd env) := hl
      have hnil : locsOf (JSValue.boolean b) = [] := by simp [locsOf]
      rw [hnil] at h1
      rcases List.mem_append.mp h1 with h1 | h1
      · rw [List.nil_append] at h1
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h1)))
      · exact List.mem_append.mpr (Or.inr h1)) h

theorem lookup_mem_snd : ∀ {env : Env} {x : «String»} {v : JSValue},
    lookup env x = some v → v ∈ env.map Prod.snd
  | [], _, _, h => by simp [lookup] at h
  | (n, w) :: rest, x, v, h => by
      simp only [lookup] at h
      by_cases hnw : n = x
      · rw [if_pos (by simp [hnw])] at h
        obtain rfl := Option.some.inj h
        simp
      · rw [if_neg (by simp [hnw])] at h
        exact List.mem_cons_of_mem _ (lookup_mem_snd h)

theorem framesWf_cons_intro {heap : Heap} {nl : Nat} {f : Fr} {fs : List Fr}
    (hst : instrsWf heap nl f.stmts) (htl : framesWf heap nl fs) :
    framesWf heap nl (f :: fs) := ⟨hst, htl⟩

theorem framesWf_tail {heap : Heap} {nl : Nat} {f : Fr} {fs : List Fr}
    (h : framesWf heap nl (f :: fs)) : framesWf heap nl fs := h.2

theorem framesWf_head_stmts {heap : Heap} {nl : Nat} {i : Instr} {stmts : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»} {fs : List Fr}
    (h : framesWf heap nl (⟨i :: stmts, env, eval, ret⟩ :: fs)) :
    instrsWf heap nl stmts := h.1.2

theorem heapOk_framesWf_push {heap : Heap} {nl : Nat} {i : Instr} {stmts : List Instr}
    {env : Env} {v : JSValue} {eval : List JSValue} {ret : «String»} {fs : List Fr}
    (hv : ∀ l ∈ locsOf v, l < nl ∧ (heap l).isSome = Bool.true)
    (hheap : heapOk heap nl (⟨i :: stmts, env, eval, ret⟩ :: fs))
    (hwf : framesWf heap nl (⟨i :: stmts, env, eval, ret⟩ :: fs)) :
    heapOk heap nl (⟨stmts, env, v :: eval, ret⟩ :: fs)
      ∧ framesWf heap nl (⟨stmts, env, v :: eval, ret⟩ :: fs) :=
  ⟨heapOk_push_eval hv hheap,
    framesWf_cons_intro (f := ⟨stmts, env, v :: eval, ret⟩) hwf.1.2 hwf.2⟩

theorem heapOk_framesWf_push_nolocs {heap : Heap} {nl : Nat} {i : Instr}
    {stmts : List Instr} {env : Env} {v : JSValue} {eval : List JSValue}
    {ret : «String»} {fs : List Fr}
    (hvl : locsOf v = [])
    (hheap : heapOk heap nl (⟨i :: stmts, env, eval, ret⟩ :: fs))
    (hwf : framesWf heap nl (⟨i :: stmts, env, eval, ret⟩ :: fs)) :
    heapOk heap nl (⟨stmts, env, v :: eval, ret⟩ :: fs)
      ∧ framesWf heap nl (⟨stmts, env, v :: eval, ret⟩ :: fs) :=
  heapOk_framesWf_push (fun l hl => absurd hl (by rw [hvl]; simp)) hheap hwf


theorem heapSet_get_ne {heap : Heap} {nl : Nat} {o : JsObj} {l : Nat}
    (hne : l ≠ nl) : heapSet heap nl o l = heap l := by
  simp [heapSet, hne]

theorem heapSet_get_self (heap : Heap) (nl : Nat) (o : JsObj) :
    heapSet heap nl o nl = some o := by
  simp [heapSet]

theorem heapOk_heapSet_succ {heap : Heap} {nl : Nat} {o : JsObj}
    (hobj : objRefs o = []) :
    ∀ (fs : List Fr), heapOk heap nl fs → heapOk (heapSet heap nl o) (nl + 1) fs := by
  intro fs
  induction fs with
  | nil =>
      intro h
      refine ⟨?_, ?_⟩
      · intro l hl o' ho'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hlt | heq
        · rw [heapSet_get_ne (Nat.ne_of_lt hlt)] at ho'
          have h2 := h.1 l hlt o' ho'
          simp only [List.all_eq_true] at h2 ⊢
          intro r hr
          have hr2 := h2 r hr
          simp only [decide_eq_true_eq] at hr2 ⊢
          exact ⟨Nat.lt_succ_of_lt hr2.1, by
            rw [heapSet_get_ne (Nat.ne_of_lt hr2.1)]; exact hr2.2⟩
        · subst heq
          rw [heapSet_get_self] at ho'
          obtain rfl := Option.some.inj ho'
          rw [hobj]
          simp
      · intro l hl
        by_cases heq : l = nl
        · exact absurd (heq ▸ hl) (Nat.not_succ_le_self nl)
        · rw [heapSet_get_ne heq]
          exact h.2 l (Nat.le_trans (Nat.le_succ nl) hl)
  | cons f fs ih =>
      intro h
      refine ⟨?_, ih h.2⟩
      intro l hl
      have h1 := h.1 l hl
      exact ⟨Nat.lt_succ_of_lt h1.1, by
        rw [heapSet_get_ne (Nat.ne_of_lt h1.1)]; exact h1.2⟩

theorem instrsWf_heapSet_succ {heap : Heap} {nl : Nat} {o : JsObj} :
    ∀ (ls : List Instr), instrsWf heap nl ls → instrsWf (heapSet heap nl o) (nl + 1) ls := by
  intro ls h
  rw [instrsWf_iff_locs] at h ⊢
  intro l hl
  have h1 := h l hl
  exact ⟨Nat.lt_succ_of_lt h1.1, by
    rw [heapSet_get_ne (Nat.ne_of_lt h1.1)]; exact h1.2⟩

theorem framesWf_heapSet_succ {heap : Heap} {nl : Nat} {o : JsObj} :
    ∀ (fs : List Fr), framesWf heap nl fs → framesWf (heapSet heap nl o) (nl + 1) fs := by
  intro fs
  induction fs with
  | nil => intro _; exact trivial
  | cons f fs ih =>
      intro h
      exact ⟨instrsWf_heapSet_succ _ h.1, ih h.2⟩

theorem runtimeCallable_heapSet_ne {heap : Heap} {nl : Nat} {o : JsObj} {l : Nat}
    (hne : l ≠ nl) :
    runtimeCallable (heapSet heap nl o) l = runtimeCallable heap l := by
  simp only [runtimeCallable, heapSet_get_ne hne]

theorem runtimeCallable_heapSet_self (heap : Heap) (nl : Nat) (o : JsObj) :
    runtimeCallable (heapSet heap nl o) nl = kindCallable o.kind := by
  simp only [runtimeCallable, heapSet_get_self]

theorem heapOk_framesWf_swap_head {heap : Heap} {nl : Nat} {i : Instr}
    {stmts : List Instr} {env : Env} {v w : JSValue} {eval : List JSValue}
    {ret : «String»} {fs : List Fr}
    (hvl : locsOf v = locsOf w)
    (hheap : heapOk heap nl (⟨i :: stmts, env, w :: eval, ret⟩ :: fs))
    (hwf : framesWf heap nl (⟨i :: stmts, env, w :: eval, ret⟩ :: fs)) :
    heapOk heap nl (⟨stmts, env, v :: eval, ret⟩ :: fs)
      ∧ framesWf heap nl (⟨stmts, env, v :: eval, ret⟩ :: fs) :=
  ⟨heapOk_swap_head hvl hheap,
    framesWf_cons_intro (f := ⟨stmts, env, v :: eval, ret⟩) hwf.1.2 hwf.2⟩

theorem heapOk_framesWf_pushempty {heap : Heap} {nl : Nat} {i : Instr}
    {stmts : List Instr} {env : Env} {w v' : JSValue} {eval : List JSValue}
    {ret : «String»} {fs : List Fr}
    (hv : locsOf v' = [])
    (hheap : heapOk heap nl (⟨i :: stmts, env, w :: eval, ret⟩ :: fs))
    (hwf : framesWf heap nl (⟨i :: stmts, env, w :: eval, ret⟩ :: fs)) :
    heapOk heap nl (⟨stmts, env, v' :: eval, ret⟩ :: fs)
      ∧ framesWf heap nl (⟨stmts, env, v' :: eval, ret⟩ :: fs) :=
  ⟨heapOk_cons_mono (f := ⟨i :: stmts, env, w :: eval, ret⟩)
      (g := ⟨stmts, env, v' :: eval, ret⟩) (by
        intro l hl
        have h1 : l ∈ (locsOf v' ++ List.flatMap locsOf eval)
            ++ List.flatMap locsOf (List.map Prod.snd env) := hl
        rw [hv] at h1
        rcases List.mem_append.mp h1 with h1 | h1
        · rw [List.nil_append] at h1
          exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h1)))
        · exact List.mem_append.mpr (Or.inr h1)) hheap,
    framesWf_cons_intro (f := ⟨stmts, env, v' :: eval, ret⟩) hwf.1.2 hwf.2⟩

theorem heapOk_framesWf_stmts_swap {heap : Heap} {nl : Nat} {i j : Instr}
    {stmts stmts' : List Instr} {env : Env} {eval : List JSValue}
    {ret : «String»} {fs : List Fr}
    (hheap : heapOk heap nl (⟨i :: stmts, env, eval, ret⟩ :: fs))
    (hwf : framesWf heap nl (⟨i :: stmts, env, eval, ret⟩ :: fs))
    (hst : instrsWf heap nl (j :: stmts')) :
    heapOk heap nl (⟨j :: stmts', env, eval, ret⟩ :: fs)
      ∧ framesWf heap nl (⟨j :: stmts', env, eval, ret⟩ :: fs) :=
  ⟨heapOk_cons_mono (f := ⟨i :: stmts, env, eval, ret⟩)
      (g := ⟨j :: stmts', env, eval, ret⟩) (fun _ hl => hl) hheap,
    ⟨hst, hwf.2⟩⟩

theorem instrWf_kTestVar {heap : Heap} {nl : Nat} {x : «String»} {pr : Prim} :
    instrWf heap nl (.kTestVar x pr) := by
  intro l hl
  simp only [instrLocs] at hl
  simp at hl

theorem heapOk_framesWf_mkList {heap : Heap} {nl : Nat} {stmts : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»} {fs : List Fr} {n : Nat}
    (hheap : heapOk heap nl (⟨.kMkList n :: stmts, env, eval, ret⟩ :: fs))
    (hwf : framesWf heap nl (⟨.kMkList n :: stmts, env, eval, ret⟩ :: fs)) :
    heapOk heap nl (⟨stmts, env, .listV (eval.take n).reverse :: eval.drop n, ret⟩ :: fs)
      ∧ framesWf heap nl
        (⟨stmts, env, .listV (eval.take n).reverse :: eval.drop n, ret⟩ :: fs) :=
  ⟨heapOk_cons_mono (f := ⟨.kMkList n :: stmts, env, eval, ret⟩)
      (g := ⟨stmts, env, .listV (eval.take n).reverse :: eval.drop n, ret⟩) (by
        intro l hl
        show l ∈ (List.flatMap locsOf eval
          ++ List.flatMap locsOf (List.map Prod.snd env))
        have h1 : l ∈ (locsOf (.listV (List.take n eval).reverse)
            ++ List.flatMap locsOf (List.drop n eval))
            ++ List.flatMap locsOf (List.map Prod.snd env) := hl
        rcases List.mem_append.mp h1 with h1 | h1
        · rcases List.mem_append.mp h1 with h1 | h1
          · simp only [locsOf] at h1
            obtain ⟨v, hv, hpl⟩ := mem_locsList h1
            exact List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr
              ⟨v, List.mem_of_mem_take (List.mem_reverse.mp hv), hpl⟩))
          · exact List.mem_append.mpr (Or.inl (mem_flatMap_of_mem_drop h1))
        · exact List.mem_append.mpr (Or.inr h1)) hheap,
    framesWf_cons_intro
      (f := ⟨stmts, env, .listV (eval.take n).reverse :: eval.drop n, ret⟩)
      hwf.1.2 hwf.2⟩

theorem heapCallabilityOk_heapSet (heap : Heap) (nl : Nat) (o : JsObj)
    (hord : kindCallable o.kind = Bool.false) (η : HeapCallableTy)
    (hheap : heapCallabilityOk heap η) :
    heapCallabilityOk (heapSet heap nl o)
      (fun l => if l = nl then Bool.false else η l) := by
  intro l
  by_cases hln : l = nl
  · subst hln
    show (if l = l then Bool.false else η l) = runtimeCallable (heapSet heap l o) l
    rw [if_pos rfl, runtimeCallable_heapSet_self, hord]
  · show (if l = nl then Bool.false else η l)
      = runtimeCallable (heapSet heap nl o) l
    rw [if_neg hln, runtimeCallable_heapSet_ne hln]
    exact hheap l

/-- The kIte arm. -/
theorem SR_kIte (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (t e : List Instr) (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kIte t e) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone v fs heap nl n => exact ⟨η, hpre⟩
  | fell fs heap nl n => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases eval with
          | nil =>
              have h1 : frameTyped sigs η (sigRetTy sigs ret)
                  ⟨.kIte t e :: stmts, env, [], ret⟩ := hpre.2.2.2.1.1
              rw [frameTyped_kIte_reject_nil] at h1
              exact h1.elim
          | cons v eval' =>
              cases v with
              | boolean b =>
                  refine ⟨η, hpre.1,
                    heapOk_drop_eval (i := .kIte t e) (w := .boolean b) hpre.2.1, ?_,
                    ⟨frameTyped_kIte hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
                  · cases b
                    · exact framesWf_cons_intro
                        (f := ⟨e ++ stmts, env, eval', ret⟩)
                        (instrsWf_append_intro _ _
                          (instrWf_kIte_elim hpre.2.2.1.1.1).2 hpre.2.2.1.1.2)
                        hpre.2.2.1.2
                    · exact framesWf_cons_intro
                        (f := ⟨t ++ stmts, env, eval', ret⟩)
                        (instrsWf_append_intro _ _
                          (instrWf_kIte_elim hpre.2.2.1.1.1).1 hpre.2.2.1.1.2)
                        hpre.2.2.1.2
                  · rw [machineRet_head_swap]
                    exact hpre.2.2.2.2
              | undefined =>
                  exfalso
                  have h1 : frameTyped sigs η (sigRetTy sigs ret)
                      ⟨.kIte t e :: stmts, env, .undefined :: eval', ret⟩ := hpre.2.2.2.1.1
                  rw [frameTyped_kIte_reject_nonbool
                    (by intro b hb; exact JSValue.noConfusion hb)] at h1
                  exact h1.elim
              | null =>
                  exfalso
                  have h1 : frameTyped sigs η (sigRetTy sigs ret)
                      ⟨.kIte t e :: stmts, env, .null :: eval', ret⟩ := hpre.2.2.2.1.1
                  rw [frameTyped_kIte_reject_nonbool
                    (by intro b hb; exact JSValue.noConfusion hb)] at h1
                  exact h1.elim
              | number m =>
                  exfalso
                  have h1 : frameTyped sigs η (sigRetTy sigs ret)
                      ⟨.kIte t e :: stmts, env, .number m :: eval', ret⟩ := hpre.2.2.2.1.1
                  rw [frameTyped_kIte_reject_nonbool
                    (by intro b hb; exact JSValue.noConfusion hb)] at h1
                  exact h1.elim
              | str m =>
                  exfalso
                  have h1 : frameTyped sigs η (sigRetTy sigs ret)
                      ⟨.kIte t e :: stmts, env, .str m :: eval', ret⟩ := hpre.2.2.2.1.1
                  rw [frameTyped_kIte_reject_nonbool
                    (by intro b hb; exact JSValue.noConfusion hb)] at h1
                  exact h1.elim
              | obj m =>
                  exfalso
                  have h1 : frameTyped sigs η (sigRetTy sigs ret)
                      ⟨.kIte t e :: stmts, env, .obj m :: eval', ret⟩ := hpre.2.2.2.1.1
                  rw [frameTyped_kIte_reject_nonbool
                    (by intro b hb; exact JSValue.noConfusion hb)] at h1
                  exact h1.elim
              | listV m =>
                  exfalso
                  have h1 : frameTyped sigs η (sigRetTy sigs ret)
                      ⟨.kIte t e :: stmts, env, .listV m :: eval', ret⟩ := hpre.2.2.2.1.1
                  rw [frameTyped_kIte_reject_nonbool
                    (by intro b hb; exact JSValue.noConfusion hb)] at h1
                  exact h1.elim
              | descV m =>
                  exfalso
                  have h1 : frameTyped sigs η (sigRetTy sigs ret)
                      ⟨.kIte t e :: stmts, env, .descV m :: eval', ret⟩ := hpre.2.2.2.1.1
                  rw [frameTyped_kIte_reject_nonbool
                    (by intro b hb; exact JSValue.noConfusion hb)] at h1
                  exact h1.elim
              | compl a b =>
                  exfalso
                  have h1 : frameTyped sigs η (sigRetTy sigs ret)
                      ⟨.kIte t e :: stmts, env, .compl a b :: eval', ret⟩ := hpre.2.2.2.1.1
                  rw [frameTyped_kIte_reject_nonbool
                    (by intro b hb; exact JSValue.noConfusion hb)] at h1
                  exact h1.elim

/-- The kPop arm. -/
theorem SR_kPop (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy) (s : FM) (r : Ty) :
    SR_arm sigs reg η .kPop s r := by
  intro _ _ _ hpre
  cases s with
  | fdone v fs heap nl n => exact ⟨η, hpre⟩
  | fell fs heap nl n => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases eval with
          | nil =>
              have h1 : frameTyped sigs η (sigRetTy sigs ret)
                  ⟨.kPop :: stmts, env, [], ret⟩ := hpre.2.2.2.1.1
              rw [frameTyped_kPop_reject_nil] at h1
              exact h1.elim
          | cons w eval' =>
              refine ⟨η, hpre.1, heapOk_drop_eval hpre.2.1,
                framesWf_cons_intro (f := ⟨stmts, env, eval', ret⟩)
                  hpre.2.2.1.1.2 hpre.2.2.1.2,
                ⟨frameTyped_kPop hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2.2.2.2

/-- The kSet arm. -/
theorem SR_kSet (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kSet x) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone v fs heap nl n => exact ⟨η, hpre⟩
  | fell fs heap nl n => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases eval with
          | nil =>
              have h1 : frameTyped sigs η (sigRetTy sigs ret)
                  ⟨.kSet x :: stmts, env, [], ret⟩ := hpre.2.2.2.1.1
              rw [frameTyped_kSet_reject_nil] at h1
              exact h1.elim
          | cons w eval' =>
              refine ⟨η, hpre.1, heapOk_push_env hpre.2.1,
                framesWf_cons_intro (f := ⟨stmts, (x, w) :: env, eval', ret⟩)
                  hpre.2.2.1.1.2 hpre.2.2.1.2,
                ⟨frameTyped_kSet hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2.2.2.2

/-- The kEval-const arm (a pushing arm; all value shapes). -/
theorem SR_kEval_const (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (v : JSValue) (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kEval (.const v)) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone v' fs heap nl n => exact ⟨η, hpre⟩
  | fell fs heap nl n => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          refine ⟨η, hpre.1, ?_,
            framesWf_cons_intro (f := ⟨stmts, env, v :: eval, ret⟩)
              hpre.2.2.1.1.2 hpre.2.2.1.2,
            ⟨frameTyped_kEval_const hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
          · exact heapOk_push_eval (i := .kEval (.const v))
              (fun l hl => hpre.2.2.1.1.1 l (by
                simp only [instrLocs, exprLocs]
                exact hl)) hpre.2.1
          · rw [machineRet_head_swap]
            exact hpre.2.2.2.2

theorem findAO_mem : ∀ {reg : AOReg} {n : «String»} {e : List «String» × Prog},
    findAO reg n = some e → (n, e) ∈ reg
  | [], _, _, h => by simp [findAO] at h
  | ⟨m, e'⟩ :: tl, n, e, h => by
      simp only [findAO] at h
      split at h
      · next hmn =>
          obtain rfl := Option.some.inj h
          rw [beq_iff_eq.mp hmn]
          exact List.mem_cons_self ..
      · next hmn =>
          exact List.mem_cons_of_mem _ (findAO_mem h)

theorem findAO_isSome {reg : AOReg} {n : «String»}
    (h : (findAO reg n).isSome = Bool.true) :
    ∃ e, findAO reg n = some e := by
  cases hf : findAO reg n with
  | none => rw [hf] at h; simp at h
  | some e => exact ⟨e, rfl⟩

theorem popArgs_elim {ps : List Ty} {σ : List Ty}
    (h : popArgs ps σ = Bool.true) :
    σ.length ≥ ps.length ∧ leTy (σ.take ps.length).reverse ps = Bool.true := by
  simp only [popArgs, Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, h.2⟩

theorem sigParams_of_sigFind {sigs : SigTable} {f : «String»} {ps : List Ty}
    {retj : List Pending} (h : sigFind sigs f = some (ps, retj)) :
    sigParams sigs f = ps := by
  simp only [sigParams, h]

theorem sigCompls_of_sigFind {sigs : SigTable} {f : «String»} {ps : List Ty}
    {retj : List Pending} (h : sigFind sigs f = some (ps, retj)) :
    sigCompls sigs f = retj := by
  simp only [sigCompls, h]

/-- kCall: one successor world, the completion union pushed on the
    caller's stack. -/
theorem checkSeq_kCall {sigs : SigTable} {r : Ty} {W : World}
    {f : «String»} {n : Nat} {ps : List Ty} {retj : List Pending}
    {rest : List Instr}
    (hsig : sigFind sigs f = some (ps, retj))
    (har : ((ps.length == n) || (ps.length == n + 1)) = Bool.true)
    (hpop : popArgs (if ps.length == n then ps else ps.take n) W.σ
      = Bool.true) :
    checkSeq sigs r W (.kCall f n :: rest)
      = checkSeq sigs r { W with σ := complTy retj :: W.σ.drop n } rest := by
  simp only [checkSeq, step1, hsig, har, hpop, forkTC_cons]

/-- kCall inversion: an accepted call yields the signature, the arity
    hit, the argument check, and the post-call world's check. -/
theorem checkSeq_kCall_elim {sigs : SigTable} {r : Ty} {W : World}
    {f : «String»} {n : Nat} {rest : List Instr} {fb : Flows}
    (h : checkSeq sigs r W (.kCall f n :: rest) = TCResult.flows fb) :
    ∃ (ps : List Ty) (retj : List Pending),
      sigFind sigs f = some (ps, retj)
      ∧ ((ps.length == n) || (ps.length == n + 1)) = Bool.true
      ∧ popArgs (if ps.length == n then ps else ps.take n) W.σ = Bool.true
      ∧ checkSeq sigs r { W with σ := complTy retj :: W.σ.drop n } rest
          = TCResult.flows fb := by
  have hex : ∃ (ps : List Ty) (retj : List Pending),
      sigFind sigs f = some (ps, retj)
      ∧ ((ps.length == n) || (ps.length == n + 1)) = Bool.true
      ∧ popArgs (if ps.length == n then ps else ps.take n) W.σ = Bool.true := by
    cases hsig : sigFind sigs f with
    | none =>
        simp only [checkSeq, step1, hsig] at h
        exact absurd h (by simp)
    | some pr =>
        obtain ⟨ps, retj⟩ := pr
        cases har : ((ps.length == n) || (ps.length == n + 1)) with
        | false =>
            simp only [checkSeq, step1, hsig, har] at h
            exact absurd h (by simp)
        | true =>
            cases hpop : popArgs (if ps.length == n then ps else ps.take n) W.σ with
            | false =>
                simp only [checkSeq, step1, hsig, har, hpop] at h
                exact absurd h (by simp)
            | true => exact ⟨ps, retj, rfl, har, hpop⟩
  obtain ⟨ps, retj, hsig, har, hpop⟩ := hex
  refine ⟨ps, retj, hsig, har, hpop, ?_⟩
  simp only [checkSeq, step1, hsig, har, hpop, forkTC_cons] at h
  exact h

/-- popArgs bounds the argument-stack length (under the arity hit). -/
theorem popArgs_n_le {ps : List Ty} {σ : List Ty} {n : Nat}
    (har : ((ps.length == n) || (ps.length == n + 1)) = Bool.true)
    (hpop : popArgs (if ps.length == n then ps else ps.take n) σ = Bool.true) :
    n ≤ σ.length := by
  obtain ⟨hge, -⟩ := popArgs_elim hpop
  cases hn : (ps.length == n) with
  | true =>
      have hpn : ps.length = n := beq_iff_eq.mp hn
      have hif : (if (ps.length == n) = true then ps else ps.take n) = ps := by
        simp [hn]
      rw [hif] at hge
      omega
  | false =>
      have har2 : (ps.length == n + 1) = Bool.true := by
        rw [hn, Bool.false_or] at har
        exact har
      have hpn : ps.length = n + 1 := beq_iff_eq.mp har2
      have hif : (if (ps.length == n) = true then ps else ps.take n) = ps.take n := by
        simp [hn]
      rw [hif] at hge
      have hlen : (ps.take n).length = n := by
        rw [List.length_take, Nat.min_eq_left (by omega)]
      omega

/-- popArgs types the n popped arguments against the parameter prefix. -/
theorem popArgs_le_take {ps : List Ty} {σ : List Ty} {n : Nat}
    (har : ((ps.length == n) || (ps.length == n + 1)) = Bool.true)
    (hpop : popArgs (if ps.length == n then ps else ps.take n) σ = Bool.true) :
    leTy ((σ.take n).reverse) (ps.take n) = Bool.true := by
  obtain ⟨-, hle⟩ := popArgs_elim hpop
  cases hn : (ps.length == n) with
  | true =>
      have hpn : ps.length = n := beq_iff_eq.mp hn
      have hif : (if (ps.length == n) = true then ps else ps.take n) = ps := by
        simp [hn]
      rw [hif] at hle
      rw [show n = ps.length from hpn.symm, List.take_length]
      exact hle
  | false =>
      have har2 : (ps.length == n + 1) = Bool.true := by
        rw [hn, Bool.false_or] at har
        exact har
      have hpn : ps.length = n + 1 := beq_iff_eq.mp har2
      have hif : (if (ps.length == n) = true then ps else ps.take n) = ps.take n := by
        simp [hn]
      rw [hif] at hle
      have hlen : (ps.take n).length = n := by
        rw [List.length_take, Nat.min_eq_left (by omega)]
      rw [hlen] at hle
      exact hle

/-- The runtime argument typings meet the declared parameter prefix:
    from the checker's popArgs over the singleton abstraction. -/
theorem runtime_args_le {sigs : SigTable} {η : HeapCallableTy} {f : «String»}
    {n : Nat}
    {ps : List Ty} {retj : List Pending} {eval : List JSValue}
    (hsig : sigFind sigs f = some (ps, retj))
    (har : ((ps.length == n) || (ps.length == n + 1)) = Bool.true)
    (hpop : popArgs (if ps.length == n then ps else ps.take n)
      (eval.map (fun v => [normalizeAtom η (typeOfV v)])) = Bool.true) :
    ((eval.take n).reverse.map (fun v => [normalizeAtom η (typeOfV v)])).length
        ≤ (sigParams sigs f).length
      ∧ leTy ((eval.take n).reverse.map (fun v => [normalizeAtom η (typeOfV v)]))
          ((sigParams sigs f).take
            ((eval.take n).reverse.map (fun v => [normalizeAtom η (typeOfV v)])).length)
          = Bool.true := by
  have hnl : n ≤ eval.length := by
    simpa [List.length_map] using popArgs_n_le har hpop
  have htake_len : (eval.take n).length = n := by
    rw [List.length_take, Nat.min_eq_left hnl]
  have hts : (eval.take n).reverse.map (fun v => [normalizeAtom η (typeOfV v)])
      = ((eval.map (fun v => [normalizeAtom η (typeOfV v)])).take n).reverse := by
    rw [List.map_reverse, List.map_take]
  have hlen_eq : ((eval.take n).reverse.map (fun v => [normalizeAtom η (typeOfV v)])).length = n := by
    rw [List.length_map, List.length_reverse, htake_len]
  have hpn : n ≤ ps.length := by
    cases h : (ps.length == n) with
    | true =>
        rw [beq_iff_eq.mp h]
        exact Nat.le_refl n
    | false =>
        rw [h, Bool.false_or] at har
        rw [beq_iff_eq.mp har]
        omega
  rw [sigParams_of_sigFind hsig]
  refine ⟨?_, ?_⟩
  · rw [hlen_eq]; exact hpn
  · rw [hlen_eq, hts]
    exact popArgs_le_take har hpop

/-- The certificate at the runtime argument typings: the callee frame
    checks. -/
theorem callee_frameChecks {sigs : SigTable} {reg : AOReg}
    {η : HeapCallableTy} {fname : «String»}
    {ps : List «String»} {body : Prog} {args : List JSValue}
    (hcert : registryCertified sigs reg)
    (hmem : (fname, (ps, body)) ∈ reg)
    (hlen : (args.reverse.map (fun v => [normalizeAtom η (typeOfV v)])).length
      ≤ (sigParams sigs fname).length)
    (hle : leTy (args.reverse.map (fun v => [normalizeAtom η (typeOfV v)]))
      ((sigParams sigs fname).take
        (args.reverse.map (fun v => [normalizeAtom η (typeOfV v)])).length) = Bool.true) :
    frameChecks sigs η ⟨compileSteps body, ps.zip args.reverse, [], fname⟩ := by
  obtain ⟨-, hc⟩ := hcert fname ps body hmem
  obtain ⟨fb, hchk, hterm, -⟩ :=
    certifies_flows_elim (hc η (args.reverse.map (fun v => [normalizeAtom η (typeOfV v)])) hlen hle)
  simp only [frameChecks, frameWorld, envTyOf_zipTy η, hchk, hterm, List.map_nil]

/-- The machine's registry-hit kCall step, spelled out. -/
theorem fstep_kCall_found {reg : AOReg} {fname : «String»}
    {ps : List «String»} {body : Prog} {n : Nat} {rest : List Instr}
    {env : Env} {eval : List JSValue} {heap : Heap} {nl : Nat} {fs : List Fr}
    {ret : «String»}
    (hfao : findAO reg fname = some (ps, body))
    (hlen : n ≤ eval.length) :
    fstep reg (.frames (⟨.kCall fname n :: rest, env, eval, ret⟩ :: fs) heap nl)
      = .frames (⟨compileSteps body, ps.zip (eval.take n).reverse, [], fname⟩
          :: ⟨rest, env, eval.drop n, ret⟩ :: fs) heap nl := by
  simp only [fstep]
  split
  · exfalso; omega
  · simp only [hfao]

theorem machineRet_cons_congr {sigs : SigTable} {f g : Fr} {fs : List Fr}
    (h : f.ret = g.ret) : machineRet sigs (f :: fs) = machineRet sigs (g :: fs) := by
  cases fs with
  | nil => simp [machineRet, h]
  | cons x xs => simp [machineRet, List.getLast?_cons_cons]

/-- frameChecks unpacked. -/
theorem frameChecks_elim {sigs : SigTable} {η : HeapCallableTy} {f : Fr}
    (h : frameChecks sigs η f) :
    ∃ fb, checkSeq sigs (sigRetTy sigs f.ret) (frameWorld η f) f.stmts
        = TCResult.flows fb ∧ terminal fb = Bool.true := by
  cases hc : checkSeq sigs (sigRetTy sigs f.ret) (frameWorld η f) f.stmts with
  | flows fb =>
      exact ⟨fb, rfl, by rw [frameChecks, hc] at h; exact h⟩
  | reject s w =>
      rw [frameChecks, hc] at h
      exact h.elim

theorem frameOkUnder_elim {sigs : SigTable} {η : HeapCallableTy} {n : «String»}
    {f : Fr}
    (h : frameOkUnder sigs η n f) :
    ∃ fb, checkSeq sigs (sigRetTy sigs f.ret)
      { η := η, Γ := envTyOf η f.env,
        σ := complTy (sigCompls sigs n)
            :: f.eval.map (fun v => [normalizeAtom η (typeOfV v)]) }
      f.stmts = TCResult.flows fb ∧ terminal fb = Bool.true := by
  cases hch : checkSeq sigs (sigRetTy sigs f.ret)
      { η := η, Γ := envTyOf η f.env,
        σ := complTy (sigCompls sigs n)
            :: f.eval.map (fun v => [normalizeAtom η (typeOfV v)]) }
      f.stmts with
  | flows fb => exact ⟨fb, rfl, by rw [frameOkUnder, hch] at h; exact h⟩
  | reject s w => rw [frameOkUnder, hch] at h; exact h.elim

/-- THE kCall ARM (registry-hit; the native branch is the
    specialization capstone's business). -/
theorem SR_kCall (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (fname : «String») (n : Nat) (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kCall fname n) s r := by
  intro hcert hcover _ hpre
  have hclosed : ∀ (m : «String») (ps : List Ty) (retj : List Pending),
      sigFind sigs m = some (ps, retj) → (findAO reg m).isSome = Bool.true :=
    hcover.1
  cases s with
  | fdone v fs heap nl n' => exact ⟨η, hpre⟩
  | fell fs heap nl n' => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          obtain ⟨fb, hchk, hterm⟩ := frameChecks_elim hpre.2.2.2.1.1
          simp only [frameWorld] at hchk
          obtain ⟨ps, retj, hsig, har, hpop, hpost⟩ := checkSeq_kCall_elim hchk
          dsimp only at hpost
          have hlen : n ≤ eval.length := by
            simpa [List.length_map] using popArgs_n_le har hpop
          obtain ⟨⟨psr, body⟩, hfao⟩ :=
            findAO_isSome (hclosed fname ps retj hsig)
          have hregmem : (fname, (psr, body)) ∈ reg := findAO_mem hfao
          obtain ⟨hlen', hle'⟩ := runtime_args_le hsig har hpop
          have hcl := callee_frameChecks hcert hregmem hlen' hle'
          have hcaller : frameOkUnder sigs η fname ⟨stmts, env, eval.drop n, ret⟩ := by
            simp only [frameOkUnder, sigCompls_of_sigFind hsig]
            rw [List.map_drop, hpost]
            exact hterm
          rw [fstep_kCall_found hfao hlen]
          refine ⟨η, hpre.1, ⟨?_, ?_, hpre.2.1.2⟩, ⟨?_, ?_, hpre.2.2.1.2⟩,
            ⟨hcl, hcaller, hpre.2.2.2.1.2⟩, ?_⟩
          · intro l hl
            simp only [List.flatMap_nil, List.append_nil] at hl
            obtain ⟨v, hv, hpl⟩ := List.mem_flatMap.mp hl
            obtain ⟨pair, hpmem, rfl⟩ := List.mem_map.mp hv
            have hvm : (Prod.snd pair) ∈ (eval.take n).reverse :=
              zip_snd_mem _ _ hpmem
            exact hpre.2.1.1 l (List.mem_append.mpr (Or.inl
              (List.mem_flatMap.mpr
                ⟨_, List.mem_of_mem_take (List.mem_reverse.mp hvm), hpl⟩)))
          · intro l hl
            have h1 : l ∈ ((eval.drop n).flatMap locsOf
                ++ List.flatMap locsOf (List.map Prod.snd env)) := hl
            rcases List.mem_append.mp h1 with h1 | h1
            · exact hpre.2.1.1 l (List.mem_append.mpr
                (Or.inl (mem_flatMap_of_mem_drop h1)))
            · exact hpre.2.1.1 l (List.mem_append.mpr (Or.inr h1))
          · show instrsWf heap nl (compileSteps body)
            exact (hcert fname psr body hregmem).1 heap nl
          · exact hpre.2.2.1.1.2
          · rw [machineRet_cons_cons,
              machineRet_cons_congr (f := ⟨stmts, env, eval.drop n, ret⟩)
                (g := ⟨.kCall fname n :: stmts, env, eval, ret⟩) rfl]
            exact hpre.2.2.2.2

/- ## The kCall arm (registry hit)

    Post = callee :: callerPost :: fs' and the obligations map onto
    the machinery just before:
    1. callee frameChecks = certifies sigs fname ps' ts body at
       ts := (eval.take n).reverse.map singleton — leTy ts params
       from the checker's popArgs (popArgs_le_take + map_take /
       map_reverse); Γ = envTyOf (ps'.zip …) = zipTy ps' ts
       (envTyOf_zipTy). The certificate premise is the PREFIX form —
       kCall accepts an (n+1)-parameter callee at n arguments, so the
       typing only reaches a prefix of the declared params.
    2. callerPost frameOkUnder fname — verbatim the checker's kCall
       arm (checkSeq_kCall_elim): the post world
       complTy (sigCompls fname) :: σ.drop n matches under
       List.map_drop.
    3. machineRet — machineRet_cons_cons + machineRet_cons_congr.
    4. Vacuous arms: underflow is impossible (popArgs_n_le), unknown
       callee rejects (sigFind none), and reg-miss names are excluded
       by the hclosed premise below. hclosed is EXACTLY the native
       dispatch gap: the machine answers Get/Call/… natively while
       the registry does not, pushing a singleton completion that
       must be refined into the checker's union — the specialization
       capstone. -/

/- ## Proof layer XX: the specialization capstone — helper layer

    Refinement direction: w' ≤ w (w' is the RUNTIME world, w the
    CERTIFICATE world). A coarse successful check must stay
    successful at the refined world, and its falling worlds must
    cover the refined falling worlds (loop joins need the coverage
    to re-establish neutrality on the refined falls). This layer
    proves the split covariances and the loop join; the full
    56-arm induction (checkSeq_specialize) is the remaining step. -/

/-- Result specialization: coarse `flows` forces refined `flows` and
    refined falls refine coarse falls; a coarse reject is vacuous. -/
def specLe (res' res : TCResult) : Prop :=
  match res with
  | .flows fb =>
      match res' with
      | .flows fb' => ∀ v ∈ fb'.falls, ∃ u ∈ fb.falls, worldLe v u
      | .reject _ _ => False
  | .reject _ _ => True

theorem specLe_flows_elim {res' : TCResult} {fb : Flows}
    (h : specLe res' (TCResult.flows fb)) :
    ∃ fb', res' = TCResult.flows fb' ∧
      ∀ v ∈ fb'.falls, ∃ u ∈ fb.falls, worldLe v u := by
  cases res' with
  | flows fb' => exact ⟨fb', rfl, h⟩
  | reject s w => exact h.elim

theorem specLe_flows_intro {fb' fb : Flows}
    (h : ∀ v ∈ fb'.falls, ∃ u ∈ fb.falls, worldLe v u) :
    specLe (TCResult.flows fb') (TCResult.flows fb) := h

theorem specLe_reject (res' : TCResult) {s : Instr} {why : «String»} :
    specLe res' (TCResult.reject s why) := trivial

theorem specLe_merge {a' a b' b : TCResult}
    (ha : specLe a' a) (hb : specLe b' b) :
    specLe (mergeTC a' b') (mergeTC a b) := by
  cases a with
  | reject s w => exact trivial
  | flows fa =>
      cases b with
      | reject s w => exact trivial
      | flows fb =>
          obtain ⟨fa', rfl, hca⟩ := specLe_flows_elim ha
          obtain ⟨fb', rfl, hcb⟩ := specLe_flows_elim hb
          simp only [mergeTC, specLe]
          intro v hv
          rcases List.mem_append.mp hv with hv | hv
          · obtain ⟨u, hu, hle⟩ := hca v hv
            exact ⟨u, List.mem_append_left _ hu, hle⟩
          · obtain ⟨u, hu, hle⟩ := hcb v hv
            exact ⟨u, List.mem_append_right _ hu, hle⟩

theorem specLe_merge_left {x y z : TCResult} (h : specLe x z) :
    specLe x (mergeTC y z) := by
  cases y with
  | reject s w => exact trivial
  | flows fy =>
      cases z with
      | reject s w => exact trivial
      | flows fz =>
          obtain ⟨fx, rfl, hc⟩ := specLe_flows_elim h
          simp only [mergeTC, specLe]
          intro v hv
          obtain ⟨u, hu, hle⟩ := hc v hv
          exact ⟨u, List.mem_append_right _ hu, hle⟩

theorem specLe_merge_right {x y z : TCResult} (h : specLe x y) :
    specLe x (mergeTC y z) := by
  cases y with
  | reject s w => exact trivial
  | flows fy =>
      cases z with
      | reject s w => exact trivial
      | flows fz =>
          obtain ⟨fx, rfl, hc⟩ := specLe_flows_elim h
          simp only [mergeTC, specLe]
          intro v hv
          obtain ⟨u, hu, hle⟩ := hc v hv
          exact ⟨u, List.mem_append_left _ hu, hle⟩

/-- Fold of flows components is flows. -/
theorem fold_flows_exists {α : Type} {J : α → TCResult} :
    ∀ (ts : List α) (acc : TCResult), (∃ fa, acc = TCResult.flows fa) →
      (∀ a ∈ ts, ∃ f, J a = TCResult.flows f) →
      ∃ fr, ts.foldl (fun x a => mergeTC x (J a)) acc = TCResult.flows fr := by
  intro ts
  induction ts with
  | nil =>
      intro acc hacc _
      exact ⟨_, by rw [List.foldl_nil]; exact hacc.choose_spec⟩
  | cons a as ih =>
      intro acc hacc hall
      obtain ⟨fa, hfa⟩ := hall a (List.mem_cons_self ..)
      obtain ⟨fa0, hfa0⟩ := hacc
      have hm : ∃ f, mergeTC acc (J a) = TCResult.flows f := by
        refine ⟨⟨fa0.exits || fa.exits, fa0.throws || fa.throws,
          fa0.falls ++ fa.falls, fa0.assumes ++ fa.assumes⟩, ?_⟩
        rw [hfa0, hfa]
        rfl
      obtain ⟨fr, hfr⟩ := ih (mergeTC acc (J a)) hm
        (fun b hb => hall b (List.mem_cons_of_mem _ hb))
      exact ⟨fr, by rw [List.foldl_cons]; exact hfr⟩

/-- Fold over noFlows: components are flows and the falls concat. -/
theorem fold_noFlows_falls {α : Type} {J : α → TCResult} :
    ∀ (ts : List α) (fb : Flows),
      ts.foldl (fun x a => mergeTC x (J a)) noFlows = TCResult.flows fb →
      (∀ a ∈ ts, ∃ f, J a = TCResult.flows f)
      ∧ fb.falls = ts.flatMap (fun a => fallsT (J a)) := by
  intro ts fb h
  have hnr : ∀ s w, ts.foldl (fun x a => mergeTC x (J a)) noFlows
      ≠ TCResult.reject s w := ne_reject_of_flows h
  obtain ⟨hcomp, heq⟩ := fold_merge_flows J ts noFlows hnr
  refine ⟨hcomp, ?_⟩
  have hfall : fb.falls = fallsT noFlows ++ ts.flatMap (fun a => fallsT (J a)) := by
    have hres : TCResult.flows fb = TCResult.flows ({ exits := exitsT noFlows || ts.any (fun a => exitsT (J a)), throws := throwsT noFlows || ts.any (fun a => throwsT (J a)), falls := fallsT noFlows ++ ts.flatMap (fun a => fallsT (J a)), assumes := assumesT noFlows ++ ts.flatMap (fun a => assumesT (J a)) }) :=
      h.symm.trans heq
    exact congrArg Flows.falls (TCResult.flows.inj hres)
  rw [hfall]
  rfl

/-- Fold specialization: mate-covering index lists + pointwise specLe. -/
theorem fold_specLe {α β : Type} {J : α → TCResult} {J' : β → TCResult}
    {R : β → α → Prop} :
    ∀ (ws : List α) (ws' : List β) (fr : Flows),
      (∀ b ∈ ws', ∃ a ∈ ws, R b a) →
      (∀ b a, R b a → specLe (J' b) (J a)) →
      ws.foldl (fun x a => mergeTC x (J a)) noFlows = TCResult.flows fr →
      ∃ fr', ws'.foldl (fun x b => mergeTC x (J' b)) noFlows = TCResult.flows fr'
        ∧ ∀ v ∈ fr'.falls, ∃ u ∈ fr.falls, worldLe v u := by
  intro ws ws' fr hmate hpoint hcoarse
  obtain ⟨hccomp, hcfalls⟩ := fold_noFlows_falls ws fr hcoarse
  have hcomp' : ∀ b ∈ ws', ∃ f, J' b = TCResult.flows f := by
    intro b hb
    obtain ⟨a, ha, hR⟩ := hmate b hb
    obtain ⟨fa, hfa⟩ := hccomp a ha
    have hpb := hpoint b a hR
    rw [hfa] at hpb
    obtain ⟨fb', hfb', -⟩ := specLe_flows_elim hpb
    exact ⟨fb', hfb'⟩
  obtain ⟨fr', hfr'⟩ := fold_flows_exists ws' noFlows ⟨_, rfl⟩ hcomp'
  have hcfalls' := (fold_noFlows_falls ws' fr' hfr').2
  refine ⟨fr', hfr', ?_⟩
  intro v hv
  rw [hcfalls'] at hv
  obtain ⟨b, hb, hvb⟩ := List.mem_flatMap.mp hv
  obtain ⟨a, ha, hR⟩ := hmate b hb
  obtain ⟨fa, hfa⟩ := hccomp a ha
  have hpb := hpoint b a hR
  rw [hfa] at hpb
  obtain ⟨fb', hfb', hcov⟩ := specLe_flows_elim hpb
  have hvb' : v ∈ fb'.falls := by
    rw [hfb'] at hvb
    exact hvb
  obtain ⟨u, hu, hle⟩ := hcov v hvb'
  refine ⟨u, ?_, hle⟩
  rw [hcfalls]
  exact List.mem_flatMap.mpr ⟨a, ha, by rw [hfa]; exact hu⟩

/-- Refinement gives the length and tmoves of zip with any fixed list. -/
theorem zip_tmoves_cov : ∀ {s' s : List Ty} {T : List Ty}, stackLe s' s →
    (List.zip s T).all (fun p => tmoves p.1 p.2) = Bool.true →
    (List.zip s' T).all (fun p => tmoves p.1 p.2) = Bool.true
  | [], [], T, _, h => h
  | [], _ :: _, T, h, _ => by cases h
  | _ :: _, [], T, h, _ => by cases h
  | a' :: s', a :: s, T, h, hz => by
      obtain ⟨hslot, hrest⟩ := stackLe_cons h
      cases T with
      | nil => rfl
      | cons u T' =>
          simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hz ⊢
          exact ⟨tmoves_trans hslot.1 hz.1, zip_tmoves_cov hrest hz.2⟩

theorem neutral_transfer {σ₀ : List Ty} {u v : World} (hle : worldLe v u)
    (h : (u.σ.length == σ₀.length)
      && (List.zip u.σ σ₀).all (fun p => tmoves p.1 p.2) = Bool.true) :
    (v.σ.length == σ₀.length)
      && (List.zip v.σ σ₀).all (fun p => tmoves p.1 p.2) = Bool.true := by
  simp only [Bool.and_eq_true] at h ⊢
  have hlen : v.σ.length = u.σ.length := stackLe_length hle.2.2.1
  exact ⟨by rw [hlen]; exact h.1, zip_tmoves_cov hle.2.2.1 h.2⟩

/-- Refined split1 outputs are covered by coarse split1 outputs. -/
theorem split1_cov {x : «String»} {T : Ty} {w' w : World} {v' : World}
    (h : worldLe w' w) (hv' : v' ∈ split1 x T w') :
    ∃ v ∈ split1 x T w, worldLe v' v := by
  obtain ⟨hη, hΓ, hσ, hcovΓ, hcovσ⟩ := h
  cases hl' : tyLookup w'.Γ x with
  | none => rw [split1, hl'] at hv'; cases hv'
  | some S' =>
      cases hl : tyLookup w.Γ x with
      | none =>
          have hsome := hΓ.1 x
          rw [hl', hl] at hsome
          exact absurd hsome (by simp)
      | some S =>
          have hcovA : ∀ a' ∈ S', ∃ a ∈ S, atomCov w'.η a' a := by
            intro a' ha'
            obtain ⟨t, ht, htc⟩ := hcovΓ x S' (by rw [hl'])
            rw [hl] at ht
            have hSe : t = S := by simpa using ht.symm
            rw [hSe] at htc
            exact htc a' ha'
          have hcov : ∀ a' ∈ S', ∃ a ∈ S, tmovesV a' a = Bool.true := by
            intro a' ha'
            obtain ⟨a, ha, hac⟩ := hcovA a' ha'
            exact ⟨a, ha, atomCov_tmoves hac⟩
          have hmeetle : tyLe (meetTy S' T) (meetTy S T) :=
            tyLe_of_atom_cov (fun a' ha' => meetTy_cov hcov a' ha')
          have hremle : tyLe (removeTy S' T) (removeTy S T) :=
            tyLe_of_atom_cov (fun a' ha' => removeTy_cov hcov a' ha')
          have hmeetcov : tyCov w'.η (meetTy S' T) (meetTy S T) :=
            meetTy_tyCov hcovA
          have hremcov : tyCov w'.η (removeTy S' T) (removeTy S T) :=
            removeTy_tyCov hcovA
          rw [split1, hl'] at hv'
          rw [split1, hl]
          simp only [List.mem_append] at hv' ⊢
          rcases hv' with hv' | hv'
          · cases hm' : meetTy S' T with
            | nil => rw [hm'] at hv'; cases hv'
            | cons m' ms' =>
                rw [hm'] at hv'
                simp only [List.mem_singleton] at hv'
                subst hv'
                have hm'mem : m' ∈ meetTy S' T := by rw [hm']; exact List.mem_cons_self ..
                obtain ⟨m, hm_mem, -⟩ := meetTy_cov hcov m' hm'mem
                have hne : meetTy S T ≠ [] := by
                  intro hnil; rw [hnil] at hm_mem; cases hm_mem
                refine ⟨{ w with Γ := (x, meetTy S T) :: w.Γ, σ := [.isValue (.boolean Bool.true)] :: w.σ }, ?_, ?_⟩
                · left
                  cases hm : meetTy S T with
                  | nil => exact absurd hm hne
                  | cons m ms => simp
                · exact ⟨hη, envLe_cons hΓ ⟨hm' ▸ hmeetle,
                    fun _ => List.cons_ne_nil _ _⟩,
                    ⟨⟨tmoves_refl _, fun h => h⟩, hσ⟩,
                    envCov_cons hcovΓ (by rw [← hm']; exact hmeetcov),
                    stackCov_cons_intro (tyCov_refl _ _) hcovσ⟩
          · cases hm' : removeTy S' T with
            | nil => rw [hm'] at hv'; cases hv'
            | cons m' ms' =>
                rw [hm'] at hv'
                simp only [List.mem_singleton] at hv'
                subst hv'
                have hm'mem : m' ∈ removeTy S' T := by rw [hm']; exact List.mem_cons_self ..
                obtain ⟨m, hm_mem, -⟩ := removeTy_cov hcov m' hm'mem
                have hne : removeTy S T ≠ [] := by
                  intro hnil; rw [hnil] at hm_mem; cases hm_mem
                refine ⟨{ w with Γ := (x, removeTy S T) :: w.Γ, σ := [.isValue (.boolean Bool.false)] :: w.σ }, ?_, ?_⟩
                · right
                  cases hm : removeTy S T with
                  | nil => exact absurd hm hne
                  | cons m ms => simp
                · exact ⟨hη, envLe_cons hΓ ⟨hm' ▸ hremle,
                    fun _ => List.cons_ne_nil _ _⟩,
                    ⟨⟨tmoves_refl _, fun h => h⟩, hσ⟩,
                    envCov_cons hcovΓ (by rw [← hm']; exact hremcov),
                    stackCov_cons_intro (tyCov_refl _ _) hcovσ⟩
/-- Agreement for a total Bool split decider: covered atoms must
    receive the same verdict. -/
def DecAgree (η : HeapCallableTy) (dec : VTy → Bool) : Prop :=
  ∀ {a' a : VTy}, atomCov η a' a → dec a' = dec a

theorem splitP1_cov {x : «String»} {dec : VTy → Bool} {w' w : World}
    {v' : World} (hdec : DecAgree w.η dec) (h : worldLe w' w)
    (hv' : v' ∈ splitP1 x dec w') :
    ∃ v ∈ splitP1 x dec w, worldLe v' v := by
  obtain ⟨hη, hΓ, hσ, hcovΓ, hcovσ⟩ := h
  rw [← hη] at hdec
  cases hl' : tyLookup w'.Γ x with
  | none => rw [splitP1, hl'] at hv'; cases hv'
  | some S' =>
      cases hl : tyLookup w.Γ x with
      | none =>
          have hsome := hΓ.1 x
          rw [hl', hl] at hsome
          exact absurd hsome (by simp)
      | some S =>
          have hcovA : ∀ a' ∈ S', ∃ a ∈ S, atomCov w'.η a' a := by
            intro a' ha'
            obtain ⟨t, ht, htc⟩ := hcovΓ x S' (by rw [hl'])
            rw [hl] at ht
            have hSe : t = S := by simpa using ht.symm
            rw [hSe] at htc
            exact htc a' ha'
          have mk_le : ∀ {a' a : VTy} (hac : atomCov w'.η a' a)
              (hdd : dec a' = dec a),
              worldLe
                { w' with Γ := (x, [a']) :: w'.Γ,
                            σ := [.isValue (.boolean (dec a'))] :: w'.σ }
                { w with Γ := (x, [a]) :: w.Γ,
                           σ := [.isValue (.boolean (dec a))] :: w.σ } := by
            intro a' a hac hdd
            rw [hdd]
            exact ⟨hη, envLe_cons hΓ
              ⟨by simp [tyLe, tmoves, atomCov_tmoves hac],
                fun _ => List.cons_ne_nil _ _⟩,
              ⟨⟨tmoves_refl _, fun h => h⟩, hσ⟩,
              envCov_cons hcovΓ (atomCov_single hac),
              stackCov_cons_intro (tyCov_refl _ _) hcovσ⟩
          simp only [splitP1, hl', List.mem_flatMap] at hv'
          obtain ⟨a', ha', hv'a'⟩ := hv'
          obtain ⟨a, ha, hac⟩ := hcovA a' ha'
          have hdd : dec a' = dec a := hdec hac
          simp only [splitP1, hl, List.mem_flatMap, splitP1At,
            List.mem_singleton] at hv'a' ⊢
          subst hv'a'
          refine ⟨{ w with Γ := (x, [a]) :: w.Γ,
                                 σ := [.isValue (.boolean (dec a))] :: w.σ },
            ⟨a, ha, rfl⟩, ?_⟩
          exact mk_le hac hdd

theorem DecAgree_predDecide {η : HeapCallableTy} {f : «String»}
    {dec : VTy → Bool} (hd : predDecide η f = some dec) :
    DecAgree η dec :=
  fun hac => atomCov_dec hac f dec hd

/-- Verdict adjustment (b-adapted splits) preserves agreement. -/
theorem DecAgree_beq {dec : VTy → Bool} {η : HeapCallableTy} {b : Bool}
    (h : DecAgree η dec) : DecAgree η (fun a => dec a == b) :=
  fun hac => by dsimp only; rw [h hac]

/-- The completion-kind deciders are total and cover-stable. -/
theorem DecAgree_primDecide {η : HeapCallableTy} {p : Prim} {dec : VTy → Bool}
    (hd : primDecide p = some dec) : DecAgree η dec := by
  intro a' a hac
  have hle := atomCov_tmoves hac
  cases p <;> simp only [primDecide] at hd
  all_goals first
    | (injection hd with hdec
       subst hdec
       cases a' <;> cases a <;> simp_all [tmovesV])
    | cases hd

theorem specLe_loop_join {fb' fb : Flows} {k' k : TCResult}
    (h : specLe k' k) :
    specLe
      (match k' with
       | .flows fr' => .flows { exits := fb'.exits || fr'.exits, throws := fb'.throws || fr'.throws, falls := fr'.falls, assumes := fb'.assumes ++ fr'.assumes }
       | res => res)
      (match k with
       | .flows fr => .flows { exits := fb.exits || fr.exits, throws := fb.throws || fr.throws, falls := fr.falls, assumes := fb.assumes ++ fr.assumes }
       | res => res) := by
  cases k with
  | reject s w => trivial
  | flows fr =>
      obtain ⟨fr', rfl, hcov⟩ := specLe_flows_elim h
      exact hcov

theorem checkLoopBody_spec (site : Instr) (σ₀ : List Ty) (k : Worlds → TCResult)
    {rbody' rbody : TCResult}
    (hspec : specLe rbody' rbody)
    (hk : ∀ fs' fs, (∀ v ∈ fs', ∃ u ∈ fs, worldLe v u) → specLe (k fs') (k fs)) :
    specLe (checkLoopBody rbody' site σ₀ k) (checkLoopBody rbody site σ₀ k) := by
  cases rbody with
  | reject s w => exact trivial
  | flows fb =>
      obtain ⟨fb', rfl, hcov⟩ := specLe_flows_elim hspec
      simp only [checkLoopBody]
      by_cases hneu : fb.falls.all (fun w =>
        w.σ.length == σ₀.length
          && (List.zip w.σ σ₀).all (fun (t, u) => tmoves t u)) = true
      · have hneu' : fb'.falls.all (fun w =>
            w.σ.length == σ₀.length
              && (List.zip w.σ σ₀).all (fun (t, u) => tmoves t u)) = true := by
          rw [List.all_eq_true] at hneu ⊢
          intro v hv
          obtain ⟨u, hu, hle⟩ := hcov v hv
          exact neutral_transfer hle (hneu u hu)
        cases hkr : k fb.falls with
        | reject s w =>
            simp only [hneu]
            exact trivial
        | flows fr =>
            have hspec' : specLe (k fb'.falls) (TCResult.flows fr) := by
              rw [← hkr]; exact hk _ _ hcov
            obtain ⟨fr', hfr', hcov'⟩ := specLe_flows_elim hspec'
            simp only [hneu, hneu', hfr']
            exact hcov' 
      · simp only [hneu]
        exact trivial

/- ## Proof layer XXI: fork nonempty-preservation and the fork lift -/

/-- A bare atom that a refined atom reaches MEETS it (the only
    move-without-meet pairs are complN/complT, which are not bare). -/
theorem meetAtom_some_of_tmovesV_bare {a' a : VTy}
    (h : tmovesV a' a = Bool.true) (hb : isBareVTy a = Bool.true) :
    ∃ m, meetAtom a' a = some m := by
  cases a with
  | complN p => simp [isBareVTy] at hb
  | complT => simp [isBareVTy] at hb
  | anyValue c =>
      cases c <;> cases a' <;>
        simp_all [tmovesV, meetAtom, decide_eq_true_eq, beq_iff_eq]
  | isValue v =>
      cases a' <;> simp_all [tmovesV, meetAtom, beq_iff_eq]
  | desc fs =>
      cases a' <;> simp_all [tmovesV, meetAtom, decide_eq_true_eq]
  | notPresent =>
      cases a' <;> simp_all [tmovesV, meetAtom]

/-- Every atom either meets a BARE T or survives the difference. -/
theorem atom_split_nonempty {a' : VTy} {T : Ty}
    (hbare : ∀ b ∈ T, isBareVTy b = Bool.true) :
    (∃ b ∈ T, ∃ m, meetAtom a' b = some m) ∨ removeAtom a' T ≠ [] := by
  by_cases hmeet : ∃ b ∈ T, ∃ m, meetAtom a' b = some m
  · exact Or.inl hmeet
  · right
    have hmoves : T.any (fun b => tmovesV a' b) = Bool.false := by
      cases h : T.any (fun b => tmovesV a' b) with
      | false => rfl
      | true =>
          exfalso
          obtain ⟨b, hb, hvb⟩ := List.any_eq_true.mp h
          obtain ⟨m, hmm⟩ := meetAtom_some_of_tmovesV_bare hvb (hbare b hb)
          exact hmeet ⟨b, hb, m, hmm⟩
    rw [removeAtom, hmoves]
    cases hbc : isBoolClass a' with
    | false => simp [hbc]
    | true =>
        have ha' : a' = .anyValue .bool := isBoolClass_inv hbc
        subst ha'
        have hnoT : ∀ (b : Bool), T.any (isBoolSing b) = Bool.true → False := by
          intro b hb
          exfalso
          obtain ⟨c, hc, hbc2⟩ := List.any_eq_true.mp hb
          have hcv : c = .isValue (.boolean b) := isBoolSing_inv hbc2
          exact hmeet ⟨c, hc, .isValue (.boolean b), by
            rw [hcv]; cases b <;> simp [meetAtom, tagOf]⟩
        cases h1 : T.any (isBoolSing Bool.true) with
        | true => exact absurd h1 (hnoT Bool.true)
        | false =>
            cases h2 : T.any (isBoolSing Bool.false) with
            | true => exact absurd h2 (hnoT Bool.false)
            | false => simp [hbc, h1, h2]

/-- For BARE T, a nonempty refined slot splits nonempty. -/
theorem split1_ne_of_bare {x : «String»} {T : Ty} {w : World} {S' : Ty}
    (hbare : ∀ b ∈ T, isBareVTy b = Bool.true)
    (hl : tyLookup w.Γ x = some S') (hne : S' ≠ []) :
    split1 x T w ≠ [] := by
  obtain ⟨a', ha'⟩ := List.exists_mem_of_ne_nil S' hne
  have hcase := atom_split_nonempty (a' := a') (T := T) hbare
  rw [split1, hl]
  cases hm : meetTy S' T with
  | cons m ms => simp [hm]
  | nil =>
      rcases hcase with ⟨b, hb, m, hmm⟩ | hrem
      · exfalso
        have hmem : m ∈ meetTy S' T := by
          simp only [meetTy]
          exact List.mem_flatMap.mpr ⟨a', ha',
            List.mem_flatMap.mpr ⟨b, hb, by simp [hmm]⟩⟩
        rw [hm] at hmem
        cases hmem
      · have hremTy : removeTy S' T ≠ [] := by
          obtain ⟨m0, hm0⟩ := List.exists_mem_of_ne_nil _ hrem
          intro hnil
          have hmem : m0 ∈ removeTy S' T :=
            List.mem_flatMap.mpr ⟨a', ha', hm0⟩
          rw [hnil] at hmem
          cases hmem
        cases hr : removeTy S' T with
        | nil => exact absurd hr hremTy
        | cons m ms => simp [hm, hr]

/-- Coarse nonempty split1 (BARE test type) stays nonempty refined. -/
theorem split1_ne_of_worldLe {x : «String»} {T : Ty} {w' w : World}
    (hbare : ∀ b ∈ T, isBareVTy b = Bool.true) (h : worldLe w' w)
    (hne : split1 x T w ≠ []) : split1 x T w' ≠ [] := by
  obtain ⟨-, hΓ, -, -, -⟩ := h
  cases hl : tyLookup w.Γ x with
  | none => rw [split1, hl] at hne; exact absurd rfl hne
  | some S =>
      have hSne : S ≠ [] := by
        intro hS
        subst hS
        apply hne
        simp [split1, hl, meetTy, removeTy]
      obtain ⟨S', ht', hS'ne, -⟩ := hΓ.2.2 x S (by rw [hl]; simp) hSne
      have hl' : tyLookup w'.Γ x = some S' := by
        cases hlook : tyLookup w'.Γ x with
        | none => rw [hlook] at ht'; cases ht'
        | some U => rw [hlook] at ht'; simp_all
      exact split1_ne_of_bare hbare hl' hS'ne

/-- Coarse nonempty splitP1 stays nonempty refined. -/
theorem splitP1_ne_of_worldLe {x : «String»} {dec : VTy → Bool}
    {w' w : World} (h : worldLe w' w)
    (hne : splitP1 x dec w ≠ []) : splitP1 x dec w' ≠ [] := by
  obtain ⟨-, hΓ, -, -, -⟩ := h
  cases hl : tyLookup w.Γ x with
  | none => rw [splitP1, hl] at hne; exact absurd rfl hne
  | some S =>
      have hSne : S ≠ [] := by
        intro hS
        subst hS
        apply hne
        simp [splitP1, hl]
      obtain ⟨S', ht', hS'ne, -⟩ := hΓ.2.2 x S (by rw [hl]; simp) hSne
      have hl' : tyLookup w'.Γ x = some S' := by
        cases hlook : tyLookup w'.Γ x with
        | none => rw [hlook] at ht'; cases ht'
        | some U => rw [hlook] at ht'; simp_all
      intro hnil
      simp only [splitP1, hl'] at hnil
      obtain ⟨a', ha'⟩ := List.exists_mem_of_ne_nil S' hS'ne
      have hatom : splitP1At x dec w' a' ≠ [] := by
        simp only [splitP1At]
        cases hd : dec a' <;> simp [hd]
      obtain ⟨v', hv'⟩ := List.exists_mem_of_ne_nil _ hatom
      have hmem : v' ∈ S'.flatMap (splitP1At x dec w') :=
        List.mem_flatMap.mpr ⟨a', ha', hv'⟩
      rw [hnil] at hmem
      cases hmem

/-- Every `step1` success is a nonempty successor list. -/
theorem step1_some_ne (sigs : SigTable) (i : Instr) (w : World) :
    ∀ ws, step1 sigs i w = some ws → ws ≠ [] := by
  intro ws h
  cases i <;> simp only [step1] at h
  all_goals
    repeat' first
      | split at h
      | (obtain ⟨a, hb, hws⟩ := h; rw [← hws]; simp)
      | (rw [← h]; simp)
      | (injection h with hws; rw [← hws]; simp)
      | simp_all

/-- Fork lift: covered successor lists and covered continuations. -/
theorem fork_specLe {site : Instr} {ws' ws : Worlds} {k : World → TCResult}
    (hmate : ∀ u' ∈ ws', ∃ u ∈ ws, worldLe u' u)
    (hne : ws ≠ [] → ws' ≠ [])
    (hk : ∀ u' u, worldLe u' u → specLe (k u') (k u)) :
    specLe (forkTC site ws' k) (forkTC site ws k) := by
  cases ws with
  | nil => exact trivial
  | cons u0 us =>
      have hws' : ws' ≠ [] := hne (by simp)
      cases ws' with
      | nil => exact absurd rfl hws'
      | cons u0' us' =>
          cases hc : forkTC site (u0 :: us) k with
          | reject s w => exact trivial
          | flows fr =>
              have hfold : (u0 :: us).foldl
                  (fun acc u => mergeTC acc (k u)) noFlows = TCResult.flows fr := by
                simpa [forkTC] using hc
              obtain ⟨fr', hfr', hcov⟩ :=
                fold_specLe (J := k) (J' := k) (R := worldLe)
                  (u0 :: us) (u0' :: us') fr hmate hk hfold
              have hfork : forkTC site (u0' :: us') k = TCResult.flows fr' := by
                simpa [forkTC] using hfr'
              rw [hfork]
              exact hcov

/- ## LAYER XIVb: TERMINALITY TRANSFER (complementary to fork_specLe:
    fork_specLe carries falls-covariance; this layer carries EXIT
    preservation, needed wherever the capstone must conclude a
    refined fork TERMINATES because the coarse one did). -/

def worldsLe (ws' ws : Worlds) : Prop :=
  ∀ u' ∈ ws', ∃ u ∈ ws, worldLe u' u

/-- Merge of two terminal flows is terminal. -/
theorem mergeTC_terminal {f₁ f₂ : Flows}
    (h₁ : terminal f₁ = Bool.true) (h₂ : terminal f₂ = Bool.true) :
    terminal { exits := f₁.exits || f₂.exits, throws := f₁.throws || f₂.throws,
               falls := f₁.falls ++ f₂.falls, assumes := f₁.assumes ++ f₂.assumes }
      = Bool.true := by
  obtain ⟨e1, th1, fa1, as1⟩ := f₁
  obtain ⟨e2, th2, fa2, as2⟩ := f₂
  unfold terminal at h₁ h₂ ⊢
  simp only [Bool.and_eq_true] at h₁ h₂ ⊢
  obtain ⟨he₁, hf₁⟩ := h₁
  obtain ⟨he₂, hf₂⟩ := h₂
  refine ⟨?_, ?_⟩
  · rw [he₁, he₂]; rfl
  · cases fa1 with
    | nil =>
        rw [List.nil_append]
        exact hf₂
    | cons x xs =>
        exact absurd hf₁ (fun hc => Bool.noConfusion hc)

/-- Extraction from a noFlows-seeded fold that is flows: every
    component is flows. (By fold_merge_flows with acc = noFlows.) -/
theorem fold_all_flows {J : World → TCResult} :
    ∀ (ws : Worlds) (fb : Flows),
      ws.foldl (fun acc u => mergeTC acc (J u)) noFlows = TCResult.flows fb →
      ∀ u ∈ ws, ∃ fbu, J u = TCResult.flows fbu := by
  intro ws fb heq u hu
  have hnr : ∀ s w, ws.foldl (fun acc u => mergeTC acc (J u)) noFlows
      ≠ TCResult.reject s w := by
    intro s w hsw
    rw [hsw] at heq
    exact TCResult.noConfusion heq
  obtain ⟨hmem, -⟩ := fold_merge_flows J ws noFlows hnr
  exact hmem u hu

/-- Extraction: the fold's total exits is the disjunction of the
    component exits (any coarse component exiting is enough, and a
    covered refined world inherits its cover's exit). -/
theorem fold_exits_true_of {J : World → TCResult} :
    ∀ (ws : Worlds) (fb : Flows),
      ws.foldl (fun acc u => mergeTC acc (J u)) noFlows = TCResult.flows fb
        → terminal fb = Bool.true → ws ≠ []
        → ∃ u ∈ ws, exitsT (J u) = Bool.true := by
  -- the fold's record has exits := false || any exits; terminality
  -- forces the disjunction true, i.e. SOME component exits
  intro ws fb heq hterm hne
  have hnr : ∀ s w, ws.foldl (fun acc u => mergeTC acc (J u)) noFlows
      ≠ TCResult.reject s w := by
    intro s w hsw
    rw [hsw] at heq
    exact TCResult.noConfusion heq
  obtain ⟨-, heqf⟩ := fold_merge_flows J ws noFlows hnr
  rw [heqf] at heq
  have hinj := TCResult.flows.inj heq
  obtain ⟨fb2⟩ := hinj
  -- terminal of the merged record: exits disjunction true
  unfold terminal at hterm
  simp only [Bool.and_eq_true] at hterm
  obtain ⟨hexs, -⟩ := hterm
  simp only [exitsT, noFlows, Bool.or_eq_true, Bool.false_or] at hexs
  by_cases hany : ws.any (fun u => exitsT (J u)) = Bool.true
  · obtain ⟨u, hu, hex⟩ := List.any_eq_true.mp hany
    exact ⟨u, hu, hex⟩
  · exfalso
    have hf : ws.any (fun u => exitsT (J u)) = Bool.false := by
      cases hc : ws.any (fun u => exitsT (J u)) with
      | true => exact absurd hc hany
      | false => rfl
    have : (List.any ws fun a =>
        match J a with
        | TCResult.flows f => f.exits
        | TCResult.reject _ _ => Bool.false) = Bool.false := hf
    rw [this] at hexs
    exact Bool.noConfusion hexs

theorem fold_terminal_falls_nil {J : World → TCResult} :
    ∀ (ws : Worlds) (fb : Flows),
      ws.foldl (fun acc u => mergeTC acc (J u)) noFlows = TCResult.flows fb
        → terminal fb = Bool.true
        → ∀ u ∈ ws, ∀ fbu, J u = TCResult.flows fbu → fbu.falls = [] := by
  intro ws fb heq hterm u hu fbu hJu
  have hnr : ∀ s w, ws.foldl (fun acc u => mergeTC acc (J u)) noFlows
      ≠ TCResult.reject s w := by
    intro s w hsw
    rw [hsw] at heq
    exact TCResult.noConfusion heq
  obtain ⟨-, heqf⟩ := fold_merge_flows J ws noFlows hnr
  -- fb IS the merged record (flows-inj on the two fold equations)
  have hinj2 : TCResult.flows fb = TCResult.flows
      { exits := exitsT noFlows || ws.any (fun a => exitsT (J a)),
        throws := throwsT noFlows || ws.any (fun a => throwsT (J a)),
        falls := fallsT noFlows ++ ws.flatMap (fun a => fallsT (J a)),
        assumes := assumesT noFlows ++ ws.flatMap (fun a => assumesT (J a)) } :=
    heq.symm.trans heqf
  have hfb2 := TCResult.flows.inj hinj2
  rw [hfb2] at hterm
  unfold terminal at hterm
  simp only [Bool.and_eq_true] at hterm
  obtain ⟨-, hfl0⟩ := hterm
  cases hfb : fbu.falls with
  | nil => rfl
  | cons x xs =>
      exfalso
      -- the component's fall world x appears in the total falls
      -- (via fold_merge_flows's record), contradicting terminality
      obtain ⟨-, heqf2⟩ := fold_merge_flows J ws noFlows hnr
      -- total falls include the component's falls (x :: xs)
      have hmem' : x ∈ fallsT (J u) := by
        have h1 : fallsT (J u) = fbu.falls := by
          show (match J u with
            | TCResult.flows f => f.falls
            | TCResult.reject _ _ => []) = fbu.falls
          rw [hJu]
        rw [h1, hfb]
        exact List.mem_cons.mpr (Or.inl rfl)
      have hx : x ∈ ws.flatMap (fun a => fallsT (J a)) :=
        List.mem_flatMap.mpr ⟨u, hu, hmem'⟩
      -- hfl0: the record's total falls are empty
      obtain hnil := List.isEmpty_iff.mp hfl0
      rw [show fallsT noFlows = ([] : Worlds) from rfl, List.nil_append] at hnil
      rw [hnil] at hx
      cases hx

/-- flatMap of falls is empty when every world's falls are. -/
theorem flatMap_falls_nil {J : World → TCResult} :
    ∀ ws, (∀ u ∈ ws, fallsT (J u) = [])
      → List.flatMap (fun a => fallsT (J a)) ws = [] := by
  intro ws
  induction ws with
  | nil => intro _; rfl
  | cons u us ih =>
      intro hall
      have h1 : fallsT (J u) = [] := hall u (List.mem_cons.mpr (Or.inl rfl))
      have h2 : ∀ x ∈ us, fallsT (J x) = [] := by
        intro x hx; exact hall x (List.mem_cons.mpr (Or.inr hx))
      show fallsT (J u) ++ List.flatMap (fun a => fallsT (J a)) us = []
      rw [h1, ih h2]
      rfl

/-- THE FORK-LIFT: if the coarse fork-fold over ws is terminal, and
    the per-world transfers hold (falls: without needing exit;
    terminal: exit preserved), then the refined fold over a
    surjectively-covered ws' is terminal. -/
theorem fork_lift {J' J : World → TCResult}
    (hPf : ∀ (u' u : World), worldLe u' u →
      ∀ fbu, J u = TCResult.flows fbu → fbu.falls = []
        → ∃ fbu', J' u' = TCResult.flows fbu' ∧ fbu'.falls = [])
    (hPe : ∀ (u' u : World), worldLe u' u →
      ∀ fbu, J u = TCResult.flows fbu → terminal fbu = Bool.true
        → ∃ fbu', J' u' = TCResult.flows fbu' ∧ terminal fbu' = Bool.true) :
    ∀ (ws' ws : Worlds),
      (∀ u' ∈ ws', ∃ u ∈ ws, worldLe u' u)
      → (∀ u ∈ ws, ∃ u' ∈ ws', worldLe u' u)
      → ∀ fb, ws.foldl (fun acc u => mergeTC acc (J u)) noFlows
          = TCResult.flows fb → terminal fb = Bool.true
        → ∀ fb', ws'.foldl (fun acc u => mergeTC acc (J' u)) noFlows
            = TCResult.flows fb' → terminal fb' = Bool.true := by
  intro ws' ws hcov hsurj fb heq hterm fb' heq'
  -- ws is nonempty: an empty coarse fold is not terminal
  have hne : ws ≠ [] := by
    intro h
    subst ws
    have hfb : fb =
        { exits := Bool.false, throws := Bool.false,
          falls := [], assumes := [] } :=
      TCResult.flows.inj (show TCResult.flows fb = noFlows from heq.symm)
    rw [hfb] at hterm
    exact Bool.noConfusion hterm
  -- the refined fold never rejects (it equals flows fb')
  have hnr' : ∀ s w, ws'.foldl (fun acc u => mergeTC acc (J' u)) noFlows
      ≠ TCResult.reject s w := by
    intro s w hsw
    rw [hsw] at heq'
    exact TCResult.noConfusion heq'
  -- SOME coarse world exits
  obtain ⟨u₀, hu₀, hex₀⟩ := fold_exits_true_of (J := J) ws fb heq hterm hne
  obtain ⟨fbu, hJu⟩ := fold_all_flows (J := J) ws fb heq u₀ hu₀
  rw [hJu] at hex₀
  have hext : fbu.exits = Bool.true := hex₀
  have hfni : fbu.falls = [] :=
    fold_terminal_falls_nil (J := J) ws fb heq hterm u₀ hu₀ fbu hJu
  have htermu : terminal fbu = Bool.true := by
    show (fbu.exits && List.isEmpty fbu.falls) = Bool.true
    rw [hext, hfni]
    rfl
  -- its refined counterpart exits too
  obtain ⟨u₀', hu₀', hle₀⟩ := hsurj u₀ hu₀
  obtain ⟨fbu', hJu', htermu'⟩ := hPe u₀' u₀ hle₀ fbu hJu htermu
  have hexu' : exitsT (J' u₀') = Bool.true := by
    show (match J' u₀' with
      | TCResult.flows f => f.exits
      | TCResult.reject _ _ => Bool.false) = Bool.true
    rw [hJu']
    exact ((Bool.and_eq_true _ _).mp htermu').1
  -- EVERY refined world has empty falls (coarse covers never fall)
  have hfallall : ∀ u' ∈ ws', fallsT (J' u') = [] := by
    intro u' hu'
    obtain ⟨u, hu, hle⟩ := hcov u' hu'
    obtain ⟨fbu2, hJu2⟩ := fold_all_flows (J := J) ws fb heq u hu
    have hf2 : fbu2.falls = [] :=
      fold_terminal_falls_nil (J := J) ws fb heq hterm u hu fbu2 hJu2
    obtain ⟨fbu'2, hJu'2, hfall'2⟩ := hPf u' u hle fbu2 hJu2 hf2
    have h1 : fallsT (J' u') = fbu'2.falls := by
      show (match J' u' with
        | TCResult.flows f => f.falls
        | TCResult.reject _ _ => []) = fbu'2.falls
      rw [hJu'2]
    rw [h1]
    exact hfall'2
  -- assemble the refined record's terminality
  obtain ⟨-, heqf'⟩ := fold_merge_flows J' ws' noFlows hnr'
  have hfb' := TCResult.flows.inj (heq'.symm.trans heqf')
  rw [hfb']
  show (exitsT noFlows || List.any ws' (fun a => exitsT (J' a)))
      && List.isEmpty (fallsT noFlows
          ++ List.flatMap (fun a => fallsT (J' a)) ws') = Bool.true
  have hany : List.any ws' (fun a => exitsT (J' a)) = Bool.true :=
    List.any_eq_true.mpr ⟨u₀', hu₀', hexu'⟩
  have hfm : List.flatMap (fun a => fallsT (J' a)) ws' = [] :=
    flatMap_falls_nil (J := J') ws' hfallall
  rw [show exitsT noFlows = Bool.false from rfl, hany, Bool.false_or,
      show fallsT noFlows = ([] : Worlds) from rfl, List.nil_append, hfm]
  rfl

/- ## Proof layer XXII: the vacOk-seeded verdict fork lift (kIte) -/

theorem fold_vac_falls {α : Type} {J : α → TCResult} :
    ∀ (ts : List α) (fb : Flows),
      ts.foldl (fun x a => mergeTC x (J a)) vacOk = TCResult.flows fb →
      (∀ a ∈ ts, ∃ f, J a = TCResult.flows f)
      ∧ fb.falls = ts.flatMap (fun a => fallsT (J a)) := by
  intro ts fb h
  have hnr : ∀ s w, ts.foldl (fun x a => mergeTC x (J a)) vacOk
      ≠ TCResult.reject s w := ne_reject_of_flows h
  obtain ⟨hcomp, heq⟩ := fold_merge_flows J ts vacOk hnr
  refine ⟨hcomp, ?_⟩
  have hfall : fb.falls = fallsT vacOk ++ ts.flatMap (fun a => fallsT (J a)) := by
    have hres : TCResult.flows fb = TCResult.flows
        { exits := exitsT vacOk || ts.any (fun a => exitsT (J a)),
          throws := throwsT vacOk || ts.any (fun a => throwsT (J a)),
          falls := fallsT vacOk ++ ts.flatMap (fun a => fallsT (J a)),
          assumes := assumesT vacOk ++ ts.flatMap (fun a => assumesT (J a)) } :=
      h.symm.trans heq
    exact congrArg Flows.falls (TCResult.flows.inj hres)
  rw [hfall]
  simp [fallsT, vacOk]

theorem fold_specLe_vac {α β : Type} {J : α → TCResult} {J' : β → TCResult}
    {R : β → α → Prop} :
    ∀ (ws : List α) (ws' : List β) (fr : Flows),
      (∀ b ∈ ws', ∃ a ∈ ws, R b a) →
      (∀ b a, R b a → specLe (J' b) (J a)) →
      ws.foldl (fun x a => mergeTC x (J a)) vacOk = TCResult.flows fr →
      ∃ fr', ws'.foldl (fun x b => mergeTC x (J' b)) vacOk = TCResult.flows fr'
        ∧ ∀ v ∈ fr'.falls, ∃ u ∈ fr.falls, worldLe v u := by
  intro ws ws' fr hmate hpoint hcoarse
  obtain ⟨hccomp, hcfalls⟩ := fold_vac_falls ws fr hcoarse
  have hcomp' : ∀ b ∈ ws', ∃ f, J' b = TCResult.flows f := by
    intro b hb
    obtain ⟨a, ha, hR⟩ := hmate b hb
    obtain ⟨fa, hfa⟩ := hccomp a ha
    have hpb := hpoint b a hR
    rw [hfa] at hpb
    obtain ⟨fb', hfb', -⟩ := specLe_flows_elim hpb
    exact ⟨fb', hfb'⟩
  obtain ⟨fr', hfr'⟩ := fold_flows_exists ws' vacOk ⟨_, rfl⟩ hcomp'
  have hcfalls' := (fold_vac_falls ws' fr' hfr').2
  refine ⟨fr', hfr', ?_⟩
  intro v hv
  rw [hcfalls'] at hv
  obtain ⟨b, hb, hvb⟩ := List.mem_flatMap.mp hv
  obtain ⟨a, ha, hR⟩ := hmate b hb
  obtain ⟨fa, hfa⟩ := hccomp a ha
  have hpb := hpoint b a hR
  rw [hfa] at hpb
  obtain ⟨fb', hfb', hcov⟩ := specLe_flows_elim hpb
  have hvb' : v ∈ fb'.falls := by
    rw [hfb'] at hvb
    exact hvb
  obtain ⟨u, hu, hle⟩ := hcov v hvb'
  refine ⟨u, ?_, hle⟩
  rw [hcfalls]
  exact List.mem_flatMap.mpr ⟨a, ha, by rw [hfa]; exact hu⟩

/-- The per-atom `kIte` verdict body (a named `match` so that
    dependent elimination never has to reduce a match in the goal). -/
def iteVerdict (sigs : SigTable) (r : Ty) (t e rest : List Instr)
    (σ' : List Ty) (w : World) : VTy → TCResult
  | .isValue (.boolean Bool.true) =>
      checkSeq sigs r { w with σ := σ' } (t ++ rest)
  | .isValue (.boolean Bool.false) =>
      checkSeq sigs r { w with σ := σ' } (e ++ rest)
  | .anyValue .bool =>
      mergeTC (checkSeq sigs r { w with σ := σ' } (t ++ rest))
        (checkSeq sigs r { w with σ := σ' } (e ++ rest))
  | _ => .reject (.kIte t e) "kIte: verdict is not boolean"

/-- Verdict-atom refinement for `kIte`-style folds.  A refined
    verdict atom that moves to a coarse one is either the same
    singleton verdict (IH) or the boolean union (both IH branches). -/
theorem iteVerdict_spec {sigs : SigTable} {r : Ty} {rest t e : List Instr}
    {w' w : World} {σr σc : List Ty}
    (ht : specLe (checkSeq sigs r { w' with σ := σr } (t ++ rest))
                 (checkSeq sigs r { w with σ := σc } (t ++ rest)))
    (he : specLe (checkSeq sigs r { w' with σ := σr } (e ++ rest))
                 (checkSeq sigs r { w with σ := σc } (e ++ rest)))
    {a' a : VTy} (hmv : tmovesV a' a = Bool.true) :
    specLe (iteVerdict sigs r t e rest σr w' a')
      (iteVerdict sigs r t e rest σc w a) := by
  revert hmv
  cases a with
  | complN p => intro hmv; exact trivial
  | complT => intro hmv; exact trivial
  | desc fs => intro hmv; exact trivial
  | notPresent => intro hmv; exact trivial
  | anyValue c =>
      cases c with
      | bool =>
          cases a' with
          | anyValue c' =>
              intro hmv
              simp_all [iteVerdict, tmovesV, decide_eq_true_eq]
              exact specLe_merge ht he
          | isValue v' =>
              cases v' with
              | boolean b' =>
                  cases b'
                  · intro hmv
                    simp_all [iteVerdict, tmovesV, decide_eq_true_eq, beq_iff_eq]
                    exact specLe_merge_left he
                  · intro hmv
                    simp_all [iteVerdict, tmovesV, decide_eq_true_eq]
                    exact specLe_merge_right ht
              | _ => intro hmv; simp_all [iteVerdict, tmovesV, tagOf]
          | _ => intro hmv; simp_all [iteVerdict, tmovesV, tagOf]
      | _ => intro hmv; exact trivial
  | isValue v =>
      cases v with
      | boolean b =>
          cases b
          · cases a' with
            | isValue w =>
                cases w with
                | boolean b' =>
                    cases b'
                    · intro hmv
                      simp_all [iteVerdict, tmovesV, beq_iff_eq]
                    · intro hmv
                      simp_all [iteVerdict, tmovesV, beq_iff_eq]
                | _ => intro hmv; simp_all [iteVerdict, tmovesV, tagOf]
            | _ => intro hmv; simp_all [iteVerdict, tmovesV, tagOf]
          · cases a' with
            | isValue w =>
                cases w with
                | boolean b' =>
                    cases b'
                    · intro hmv
                      simp_all [iteVerdict, tmovesV, beq_iff_eq]
                    · intro hmv
                      simp_all [iteVerdict, tmovesV, beq_iff_eq]
                | _ => intro hmv; simp_all [iteVerdict, tmovesV, tagOf]
            | _ => intro hmv; simp_all [iteVerdict, tmovesV, tagOf]
      | _ => intro hmv; exact trivial
theorem markDebt_specLe (why : «String») {r' r : TCResult}
    (h : specLe r' r) : specLe (markDebt why r') (markDebt why r) := by
  cases r with
  | reject s w => exact trivial
  | flows f =>
      obtain ⟨f', rfl, hcov⟩ := specLe_flows_elim h
      simpa [markDebt, specLe] using hcov

theorem anyOf_bare (cs : List Ctor) :
    ∀ b ∈ anyOf cs, isBareVTy b = Bool.true := by
  intro b hb
  simp only [anyOf, List.mem_map] at hb
  obtain ⟨c, hc, rfl⟩ := hb
  simp [isBareVTy]

theorem typeMask_bare (s : «String») :
    ∀ b ∈ typeMask s, isBareVTy b = Bool.true := by
  intro b hb
  unfold typeMask at hb
  split at hb <;> simp_all [isBareVTy]

theorem markDebt_specLe_left (why : «String») {r' r : TCResult}
    (h : specLe r' r) : specLe (markDebt why r') r := by
  cases r with
  | reject s w => exact trivial
  | flows f =>
      obtain ⟨f', rfl, hcov⟩ := specLe_flows_elim h
      simpa [markDebt, specLe] using hcov

theorem markDebt_specLe_right (why : «String») {r' r : TCResult}
    (h : specLe r' r) : specLe r' (markDebt why r) := by
  cases r with
  | reject s w => exact trivial
  | flows f =>
      obtain ⟨f', rfl, hcov⟩ := specLe_flows_elim h
      simpa [markDebt, specLe] using hcov

def assertVerdict (sigs : SigTable) (r : Ty) (rest : List Instr)
    (σ' : List Ty) (w : World) (a : VTy) : TCResult :=
  match a with
  | .isValue (.boolean Bool.true) => checkSeq sigs r { w with σ := σ' } rest
  | .isValue (.boolean Bool.false) | .anyValue .bool =>
      markDebt "assert obligation not discharged"
        (checkSeq sigs r { w with σ := σ' } rest)
  | _ => .reject .kAssert "assert: verdict is not boolean"

theorem assertVerdict_spec (sigs : SigTable) (r : Ty) (rest : List Instr)
    {w' w : World} {σr σc : List Ty}
    (h : specLe (checkSeq sigs r { w' with σ := σr } rest)
                (checkSeq sigs r { w with σ := σc } rest))
    {a' a : VTy} (hmv : tmovesV a' a = Bool.true) :
    specLe (assertVerdict sigs r rest σr w' a')
      (assertVerdict sigs r rest σc w a) := by
  cases a with
  | isValue v =>
      cases v with
      | boolean b => cases b <;> cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | number n => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | str st => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | listV l => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | compl ab vv => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | obj loc => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | descV d => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | undefined => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | null => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
  | anyValue c =>
      cases c with
      | bool =>
          cases a' with
          | isValue v => cases v <;> (first | (rename_i b; cases b) | skip) <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
          | _ => simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | undef => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | null => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | num => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | str => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | list => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | obj => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | desc => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
  | complN pp => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
  | complT => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
  | desc fs => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
  | notPresent => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)

theorem testTypeP_bare (p : Prim) {T : Ty} (h : testTypeP p = some T) :
    ∀ b ∈ T, isBareVTy b = Bool.true := by
  cases p <;> simp only [testTypeP] at h
  all_goals
    cases h
    all_goals
      intro b hb
      first
      | exact anyOf_bare _ b hb
      | exact typeMask_bare _ b hb
      | (cases b <;> simp_all [isBareVTy, objT])

theorem markThrow_specLe (sigs : SigTable) (ex : Expr) {r' r : TCResult}
    (h : specLe r' r) : specLe (markThrow sigs ex r') (markThrow sigs ex r) := by
  cases r with
  | reject s w => exact trivial
  | flows f =>
      obtain ⟨f', rfl, hcov⟩ := specLe_flows_elim h
      simpa [markThrow, specLe] using hcov

theorem mem_dropLast_subset {α : Type} : ∀ (l : List α) {a : α}, a ∈ l.dropLast → a ∈ l
  | [], a, h => by simp at h
  | [_], a, h => by simp at h
  | x :: y :: ys, a, h => by
      simp only [List.dropLast_cons_cons] at h
      simp only [List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by simpa [List.mem_cons] using mem_dropLast_subset (y :: ys) h)

theorem popTy_some_nil_cov {T t' t : Ty} {σ' σ : List Ty}
    (hslot : slotLe t' t) (hrest : stackLe σ' σ)
    (hp : popTy T (t :: σ) = some []) :
    ∃ hnil : σ' = [], popTy T (t' :: σ') = some [] := by
  have hp0 := popTy_cov hslot hrest hp
  have hσnil : σ = [] := by
    simp only [popTy] at hp
    by_cases htm : tmoves t T = Bool.true
    · rw [if_pos htm] at hp
      injection hp with h
    · rw [if_neg htm] at hp
      cases hp
  subst σ
  have hσ'nil : σ' = [] := by
    cases σ' with
    | nil => rfl
    | cons u us => simp [stackLe] at hrest
  exact ⟨hσ'nil, by simpa [hσ'nil] using hp0⟩

theorem tmoves_class_down {t' t : Ty} {c : Ctor} (hslot : slotLe t' t)
    (hm : tmoves t [.anyValue c] = Bool.true) :
    tmoves t' [.anyValue c] = Bool.true := by
  unfold slotLe at hslot
  unfold tmoves at hm ⊢
  have hcov : tmoves t' t = Bool.true := hslot.1
  unfold tmoves at hcov
  simp only [List.all_eq_true] at hm ⊢ hcov
  intro a' ha'
  obtain ⟨a, ha, ha'a⟩ := List.any_eq_true.mp (hcov a' ha')
  obtain ⟨b, hb, hab⟩ := List.any_eq_true.mp (hm a ha)
  simp only [List.mem_singleton] at hb
  subst b
  exact List.any_eq_true.mpr ⟨VTy.anyValue c, by simp, tmovesV_trans ha'a hab⟩

theorem fold_worlds_specLe (sigs : SigTable) (r : Ty) (rest : List Instr)
    (hstep : ∀ u v : World, worldLe u v →
      specLe (checkSeq sigs r u rest) (checkSeq sigs r v rest)) :
    ∀ fs' fs : List World,
      (∀ u ∈ fs', ∃ v ∈ fs, worldLe u v) →
      specLe
        (fs'.foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows)
        (fs.foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows) := by
  intro fs' fs hcov
  cases hf : fs.foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows with
  | reject s why => exact trivial
  | flows fr =>
      obtain ⟨fr', hfr', hfrcov⟩ := fold_specLe fs fs' fr hcov hstep hf
      cases hf' : fs'.foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows with
      | reject s why =>
          rw [hf'] at hfr'
          cases hfr'
      | flows fr0 =>
          have hfr0 : fr0 = fr' := by
            injection (hf'.symm.trans hfr') with heq
          cases hfr0
          exact hfrcov

theorem checkSeq_specialize (sigs : SigTable) (r : Ty) (w : World) (seq : List Instr)
    (hsc : sigParamsClosed sigs) :
    ∀ (w' : World), worldLe w' w →
      specLe (checkSeq sigs r w' seq) (checkSeq sigs r w seq) := by
  induction sigs, r, w, seq using checkSeq.induct
  case case1 =>
    rename_i sigs r w
    intro w' h
    simp only [checkSeq]
    intro v hv
    simp only [List.mem_singleton] at hv
    subst hv
    exact ⟨w, List.mem_singleton.mpr rfl, h⟩
  case case2 =>
    rename_i sigs r w tail ts σ' hσ hle
    intro w' h
    obtain ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩ := h
    have hworld : worldLe w' w := ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩
    rw [hσ] at hσle
    cases hσ' : w'.σ with
    | nil => rw [hσ'] at hσle; cases hσle
    | cons t' σ'' =>
        rw [hσ'] at hσle
        obtain ⟨hslot, -⟩ := hσle
        have hle' : tmoves t' r = Bool.true := tmoves_trans hslot.1 hle
        simp [checkSeq, hσ, hσ', hle, hle', specLe]
  case case6 =>
    rename_i sigs r w t e rest ts σ' hσ ih2 ih1
    intro w' h
    obtain ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩ := h
    have hworld : worldLe w' w := ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩
    rw [hσ] at hσle
    rw [hσ] at hcovσ
    cases hσ' : w'.σ with
    | nil => rw [hσ'] at hσle; cases hσle
    | cons t' σ'' =>
        rw [hσ'] at hσle
        rw [hσ'] at hcovσ
        obtain ⟨hslot, hσ''le⟩ := hσle
        obtain ⟨-, hcovσ''⟩ := hcovσ
        have hbr : worldLe { w' with σ := σ'' } { w with σ := σ' } :=
          ⟨hη, hΓ, hσ''le, hcovΓ, hcovσ''⟩
        have ht : specLe (checkSeq sigs r { w' with σ := σ'' } (t ++ rest))
            (checkSeq sigs r { w with σ := σ' } (t ++ rest)) := ih2 hsc _ hbr
        have he : specLe (checkSeq sigs r { w' with σ := σ'' } (e ++ rest))
            (checkSeq sigs r { w with σ := σ' } (e ++ rest)) := ih1 hsc _ hbr
        have hmate : ∀ b ∈ t', ∃ a ∈ ts, tmovesV b a = Bool.true :=
          tyLe_cov_atoms hslot.1
        cases hc : ts.foldl
            (fun acc a => mergeTC acc (iteVerdict sigs r t e rest σ' w a)) vacOk with
        | reject s why =>
            simp only [checkSeq, hσ, hσ']
            change specLe
              (t'.foldl (fun acc a =>
                mergeTC acc (iteVerdict sigs r t e rest σ'' w' a)) vacOk)
              (ts.foldl (fun acc a =>
                mergeTC acc (iteVerdict sigs r t e rest σ' w a)) vacOk)
            rw [hc]
            exact trivial
        | flows fr =>
            obtain ⟨fr', hfr', hcov⟩ :=
              fold_specLe_vac (J := fun a => iteVerdict sigs r t e rest σ' w a)
                (J' := fun a => iteVerdict sigs r t e rest σ'' w' a)
                (R := fun b a => tmovesV b a = Bool.true)
                ts t' fr hmate
                (fun b a hba => iteVerdict_spec ht he hba) hc
            simp only [checkSeq, hσ, hσ']
            change specLe
              (t'.foldl (fun acc a =>
                mergeTC acc (iteVerdict sigs r t e rest σ'' w' a)) vacOk)
              (ts.foldl (fun acc a =>
                mergeTC acc (iteVerdict sigs r t e rest σ' w a)) vacOk)
            rw [hfr', hc]
            exact hcov
  case case3 =>
    rename_i sigs r w tail ts σ' hσ hnt
    intro w' h
    simp only [checkSeq, hσ]
    rw [if_neg hnt]
    exact trivial
  case case4 =>
    rename_i sigs r w tail hσ
    intro w' h
    obtain ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩ := h
    have hworld : worldLe w' w := ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩
    rw [hσ] at hσle
    cases hσ' : w'.σ with
    | nil => simp only [checkSeq, hσ, hσ']; exact trivial
    | cons t' σ'' => rw [hσ'] at hσle; cases hσle
  case case5 =>
    rename_i sigs r w t e rest hσ
    intro w' h
    obtain ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩ := h
    have hworld : worldLe w' w := ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩
    rw [hσ] at hσle
    cases hσ' : w'.σ with
    | nil => simp only [checkSeq, hσ, hσ']; exact trivial
    | cons t' σ'' => rw [hσ'] at hσle; cases hσle
  case case7 =>
    rename_i sigs r w x rest hlook ih1
    intro w' h
    obtain ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩ := h
    have hlook' : tyLookup w'.Γ x = none := by
      have hex := hΓ.1 x
      rw [hlook] at hex
      cases hl : tyLookup w'.Γ x with
      | none => rfl
      | some S => rw [hl] at hex; simp at hex
    have hpush : worldLe { w' with σ := [.isValue (.boolean Bool.true)] :: w'.σ }
        { w with σ := [.isValue (.boolean Bool.true)] :: w.σ } :=
      ⟨hη, hΓ, stackLe_cons_intro (slotLe_refl _) hσle, hcovΓ,
        stackCov_cons_intro (tyCov_refl _ _) hcovσ⟩
    simp only [checkSeq, hlook, hlook']
    exact ih1 hsc _ hpush
  case case8 =>
    rename_i sigs r w x rest S hlook ih1
    intro w' h
    have hΓ := h.2.1
    have hσle := h.2.2.1
    obtain ⟨S', hlook', -⟩ := envLe_lookup_cov_full hΓ hlook
    simp only [checkSeq, hlook, hlook']
    exact fork_specLe (fun v' hv' => split1_cov h hv')
      (fun hne => split1_ne_of_worldLe (T := [.notPresent])
        (by intro b hb; simp only [List.mem_singleton] at hb; subst hb; rfl) h hne)
      (fun u' u hu => ih1 u hsc u' hu)
  case case9 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_5]
    exact ih1 hsc w' h
  case case10 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_6]
    exact ih1 hsc w' h
  case case11 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_7]
    exact ih1 hsc w' h
  case case12 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_8]
    exact ih1 hsc w' h
  case case13 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_9]
    exact ih1 hsc w' h
  case case14 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_10]
    exact ih1 hsc w' h
  case case15 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_11]
    exact ih1 hsc w' h
  case case16 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_12]
    exact ih1 hsc w' h
  case case17 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_13]
    exact ih1 hsc w' h
  case case18 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_14]
    exact ih1 hsc w' h
  case case19 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_15]
    exact ih1 hsc w' h
  case case20 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_16]
    exact ih1 hsc w' h
  case case21 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_17]
    exact ih1 hsc w' h
  case case22 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_18]
    exact ih1 hsc w' h
  case case23 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_19]
    exact ih1 hsc w' h
  case case24 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_20]
    exact ih1 hsc w' h
  case case25 =>
    rename_i sigs r w b f x rest hfused ih1
    intro w' h
    simp only [checkSeq.eq_21]
    simp only [ite_eq_left hfused]
    exact ih1 hsc w' h
  case case26 =>
    rename_i sigs r w b f x rest hf hnone
    intro w' h
    obtain ⟨-, hΓ, -, -, -⟩ := h
    cases hreff : typeOfE sigs w'.Γ
        (.isBoolVal b (.call f [.nv x])) with
    | none =>
        simp only [checkSeq.eq_21, ite_eq_right hf, hnone, hreff]
        exact trivial
    | some t' =>
        exfalso
        cases hcall' : typeOfE sigs w'.Γ (.call f [.nv x]) with
        | none => simp [typeOfE, hcall'] at hreff
        | some tc' =>
            cases hl' : tyLookup w'.Γ x with
            | none =>
                have hn : typeOfE sigs w'.Γ (.call f [.nv x]) = none := by
                  cases hsf : sigFind sigs f <;> simp [typeOfE, typesOf, hl', hsf]
                rw [hn] at hcall'
                cases hcall'
            | some tl' =>
                have hpres := hΓ.1 x
                rw [hl'] at hpres
                cases hl : tyLookup w.Γ x with
                | none => simp [hl] at hpres
                | some tl =>
                    have hslot : slotLe tl' tl := by
                      refine ⟨?_, ?_⟩
                      · obtain ⟨u, hu, hule⟩ := hΓ.2.1 x tl' (by simp [hl'])
                        rw [hl] at hu
                        have htu : tl = u := by simpa using hu
                        subst u
                        exact hule
                      · intro hne hnil
                        obtain ⟨u, hu, hune, _⟩ := hΓ.2.2 x tl (by simp [hl]) hne
                        have hutl : u = tl' := by
                          rw [hl'] at hu
                          simpa using hu.symm
                        exact hune (by rw [hutl, hnil])
                    have hslots : slotsLe [tl'] [tl] := ⟨hslot, True.intro⟩
                    cases hsig : sigFind sigs f with
                    | none => simp [typeOfE, hsig] at hcall'
                    | some pair =>
                        obtain ⟨ps, retj⟩ := pair
                        simp only [typeOfE, hsig, typesOf, hl'] at hcall'
                        have hg' : (leTy [tl'] ps ||
                            [Expr.nv x].length == ps.length - 1 &&
                              leTy [tl'] ps.dropLast) = Bool.true := by
                          cases hg : (leTy [tl'] ps ||
                            [Expr.nv x].length == ps.length - 1 &&
                              leTy [tl'] ps.dropLast) with
                          | false =>
                              have hng : ¬(leTy [tl'] ps ||
                                  [Expr.nv x].length == ps.length - 1 &&
                                    leTy [tl'] ps.dropLast) = Bool.true := by
                                intro htrue
                                rw [hg] at htrue
                                cases htrue
                              rw [ite_eq_right hng] at hcall'
                              cases hcall'
                          | true => rfl
                        have hgc : (leTy [tl] ps ||
                            ([Expr.nv x].length == ps.length - 1 &&
                              leTy [tl] ps.dropLast)) = Bool.true := by
                          rw [Bool.or_eq_true] at hg'
                          cases hg' with
                          | inl hA =>
                              have hA' : leTy [tl] ps = Bool.true :=
                                leTy_up_closed hslots
                                  (fun p hp => (hsc f ps retj hsig).1 p hp) hA
                              simp [hA']
                          | inr hB =>
                              obtain ⟨hlen, hdl⟩ := (Bool.and_eq_true _ _) |>.mp hB
                              have hdl' : leTy [tl] ps.dropLast = Bool.true :=
                                leTy_up_closed hslots
                                  (fun p hp => (hsc f ps retj hsig).1 p
                                    (mem_dropLast_subset ps hp)) hdl
                              rw [Bool.or_eq_true]
                              exact Or.inr (by
                                rw [Bool.and_eq_true]
                                exact ⟨hlen, hdl'⟩)
                        have hcoarse : typeOfE sigs w.Γ (.call f [.nv x]) =
                            some (complPayload retj) := by
                          simp only [typeOfE, hsig, typesOf, hl]
                          rw [ite_eq_left hgc]
                        have hcoarseTop : typeOfE sigs w.Γ
                            (.isBoolVal b (.call f [.nv x])) =
                            some [.anyValue .bool] := by
                          simp [typeOfE, hcoarse]
                        rw [hcoarseTop] at hnone
                        cases hnone
  case case27 =>
    rename_i sigs r w b f x rest hf S hsome ih1
    intro w' h
    obtain ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩ := h
    obtain ⟨S', hsome', hslot, hscov⟩ := typeOfE_cov sigs w'.Γ w.Γ
      (.isBoolVal b (.call f [.nv x])) hΓ hcovΓ S hsome
    have hpush : worldLe { w' with σ := normalizeTy w'.η S' :: w'.σ }
        { w with σ := normalizeTy w.η S :: w.σ } := by
      have hnorm : normalizeTy w'.η S = normalizeTy w.η S :=
        congrArg (fun ξ => normalizeTy ξ S) hη
      rw [← hnorm]
      exact ⟨hη, hΓ,
        stackLe_cons_intro (normalizeTy_slotLe hslot hscov) hσle, hcovΓ,
        stackCov_cons_intro (normalizeTy_cov hscov) hcovσ⟩
    have hpt : specLe (checkSeq sigs r { w' with σ := normalizeTy w'.η S' :: w'.σ } rest)
        (checkSeq sigs r { w with σ := normalizeTy w.η S :: w.σ } rest) :=
      ih1 hsc _ hpush
    simp only [checkSeq.eq_21]
    simp only [ite_eq_right hf]
    simp only [hsome, hsome']
    exact markThrow_specLe sigs _ hpt
  case case34 =>
    rename_i sigs r w x rest f b dec hdec ih1
    intro w' h
    have hη := h.1
    have hdec' : predDecide w'.η f = some dec := by
      rw [hη]; exact hdec
    simp only [checkSeq.eq_24, hdec, hdec']
    exact fork_specLe
      (fun v' hv' => splitP1_cov
        (DecAgree_beq (DecAgree_predDecide hdec)) h hv')
      (fun hne => splitP1_ne_of_worldLe h hne) (fun u' u hu => ih1 u hsc u' hu)
  case case35 =>
    rename_i sigs r w x rest f b hdec hlook
    intro w' h
    obtain ⟨-, hΓ, -, -, -⟩ := h
    have hlook' : tyLookup w'.Γ x = none := by
      have hex := hΓ.1 x
      rw [hlook] at hex
      cases hl : tyLookup w'.Γ x with
      | none => rfl
      | some S => rw [hl] at hex; simp at hex
    simp only [checkSeq.eq_24, hdec, hlook, hlook']
    exact trivial
  case case36 =>
    rename_i sigs r w x rest f b hdec S hlook ih1
    intro w' h
    obtain ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩ := h
    have hdec2 : predDecide w'.η f = predDecide w.η f := by rw [hη]
    obtain ⟨S', hlook', -⟩ := envLe_lookup_cov_full hΓ hlook
    have hpush : worldLe { w' with σ := [.anyValue .bool] :: w'.σ }
        { w with σ := [.anyValue .bool] :: w.σ } :=
      ⟨hη, hΓ, stackLe_cons_intro (slotLe_refl _) hσle, hcovΓ,
        stackCov_cons_intro (tyCov_refl _ _) hcovσ⟩
    simp only [checkSeq.eq_24, hdec, hdec2, hlook, hlook']
    exact ih1 hsc _ hpush
  case case37 =>
    rename_i sigs r w x rest dec hdec ih1
    intro w' h
    simp only [checkSeq.eq_25, hdec]
    exact fork_specLe (fun v' hv' => splitP1_cov (DecAgree_primDecide hdec) h hv')
      (fun hne => splitP1_ne_of_worldLe h hne) (fun u' u hu => ih1 u hsc u' hu)
  case case38 =>
    rename_i sigs r w x rest hdec hlook
    intro w' h
    exact absurd hlook (by simp [primDecide])
  case case39 =>
    rename_i sigs r w x rest hdec S hlook ih1
    intro w' h
    exact absurd hlook (by simp [primDecide])
  case case40 =>
    rename_i sigs r w x rest dec hdec ih1
    intro w' h
    simp only [checkSeq.eq_26, hdec]
    exact fork_specLe (fun v' hv' => splitP1_cov (DecAgree_primDecide hdec) h hv')
      (fun hne => splitP1_ne_of_worldLe h hne) (fun u' u hu => ih1 u hsc u' hu)
  case case41 =>
    rename_i sigs r w x rest hdec hlook
    intro w' h
    exact absurd hlook (by simp [primDecide])
  case case42 =>
    rename_i sigs r w x rest hdec S hlook ih1
    intro w' h
    exact absurd hlook (by simp [primDecide])
  case case43 =>
    rename_i sigs r w x p rest ps hT hpred hn hc ih1
    intro w' h
    have hbare := testTypeP_bare p hT
    simp only [checkSeq, hT]
    exact fork_specLe (fun v' hv' => split1_cov h hv')
      (fun hne => split1_ne_of_worldLe hbare h hne)
      (fun u' u hu => ih1 u hsc u' hu)
  case case44 =>
    rename_i sigs r w x p rest hT hlook hpred hn hc
    intro w' h
    obtain ⟨-, hΓ, -, -, -⟩ := h
    have hlook' : tyLookup w'.Γ x = none := by
      have hex := hΓ.1 x
      rw [hlook] at hex
      cases hl : tyLookup w'.Γ x with
      | none => rfl
      | some S => rw [hl] at hex; simp at hex
    simp only [checkSeq, hT, hlook, hlook']
    exact trivial
  case case45 =>
    rename_i sigs r w x p rest hT S hlook hpred hn hc ih1
    intro w' h
    obtain ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩ := h
    obtain ⟨S', hlook', -⟩ := envLe_lookup_cov_full hΓ hlook
    have hpush : worldLe { w' with σ := [.anyValue .bool] :: w'.σ }
        { w with σ := [.anyValue .bool] :: w.σ } :=
      ⟨hη, hΓ, stackLe_cons_intro (slotLe_refl _) hσle, hcovΓ,
        stackCov_cons_intro (tyCov_refl _ _) hcovσ⟩
    simp only [checkSeq, hT, hlook, hlook']
    exact ih1 hsc _ hpush
  case case54 =>
    rename_i sigs r w rest hσ
    intro w' h
    obtain ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩ := h
    have hworld : worldLe w' w := ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩
    rw [hσ] at hσle
    cases hσ' : w'.σ with
    | nil => simp only [checkSeq, hσ, hσ']; exact trivial
    | cons t' σ'' => rw [hσ'] at hσle; cases hσle
  case case55 =>
    rename_i sigs r w rest ts σ' hσ ih1
    intro w' h
    obtain ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩ := h
    have hworld : worldLe w' w := ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩
    rw [hσ] at hσle
    rw [hσ] at hcovσ
    cases hσ' : w'.σ with
    | nil => rw [hσ'] at hσle; cases hσle
    | cons t' σ'' =>
        rw [hσ'] at hσle
        rw [hσ'] at hcovσ
        obtain ⟨hslot, hσ''le⟩ := hσle
        obtain ⟨-, hcovσ''⟩ := hcovσ
        have hbr : worldLe { w' with σ := σ'' } { w with σ := σ' } :=
          ⟨hη, hΓ, hσ''le, hcovΓ, hcovσ''⟩
        have hpt : specLe (checkSeq sigs r { w' with σ := σ'' } rest)
            (checkSeq sigs r { w with σ := σ' } rest) := ih1 hsc _ hbr
        have hmate : ∀ b ∈ t', ∃ a ∈ ts, tmovesV b a = Bool.true :=
          tyLe_cov_atoms hslot.1
        cases hc : ts.foldl
            (fun acc a => mergeTC acc (assertVerdict sigs r rest σ' w a)) vacOk with
        | reject s why =>
            simp only [checkSeq, hσ, hσ']
            change specLe
              (t'.foldl (fun acc a =>
                mergeTC acc (assertVerdict sigs r rest σ'' w' a)) vacOk)
              (ts.foldl (fun acc a =>
                mergeTC acc (assertVerdict sigs r rest σ' w a)) vacOk)
            rw [hc]
            exact trivial
        | flows fr =>
            obtain ⟨fr', hfr', hcov⟩ :=
              fold_specLe_vac (J := fun a => assertVerdict sigs r rest σ' w a)
                (J' := fun a => assertVerdict sigs r rest σ'' w' a)
                (R := fun b a => tmovesV b a = Bool.true)
                ts t' fr hmate
                (fun b a hba => assertVerdict_spec sigs r rest hpt hba) hc
            simp only [checkSeq, hσ, hσ']
            change specLe
              (t'.foldl (fun acc a =>
                mergeTC acc (assertVerdict sigs r rest σ'' w' a)) vacOk)
              (ts.foldl (fun acc a =>
                mergeTC acc (assertVerdict sigs r rest σ' w a)) vacOk)
            rw [hfr', hc]
            exact hcov
  case case28 =>
    rename_i sigs r w c body rest hσ ps hsome hbool ih2 ih1
    intro w' h
    obtain ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩ := h
    have hworld : worldLe w' w := ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩
    rw [hσ] at hσle
    cases hσ' : w'.σ with
    | nil =>
        obtain ⟨ps', hsome', hslot, -⟩ :=
          typeOfE_cov sigs w'.Γ w.Γ c hΓ hcovΓ ps hsome
        have hbool' : tmoves ps' [.anyValue .bool] = Bool.true :=
          tmoves_class_down hslot hbool
        have hbody : specLe (checkSeq sigs r w' body) (checkSeq sigs r w body) :=
          ih2 hsc w' hworld
        have hk := fold_worlds_specLe sigs r rest
          (fun u v huv => ih1 v hsc u huv)
        simp only [checkSeq, hσ, hσ', hsome, hsome', ite_eq_left hbool, ite_eq_left hbool']
        exact checkLoopBody_spec (.kRepeatWhile c body) []
          (fun fs => fs.foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows)
          hbody hk
    | cons t σ'' =>
        rw [hσ'] at hσle
        cases hσle
  case case29 =>
    intro w' h
    simp [checkSeq, specLe, *]
  case case30 =>
    intro w' h
    simp [checkSeq, specLe, *]
  case case31 =>
    rename_i sigs r w c body rest hσne
    intro w' h
    obtain ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩ := h
    cases hσ' : w'.σ with
    | nil =>
        cases hstack : w.σ with
        | nil => exact absurd hstack hσne
        | cons t σ =>
            exfalso
            simp [hσ', hstack, stackLe] at hσle
    | cons t' σ'' =>
        cases hstack : w.σ with
        | nil =>
            exfalso
            simp [hσ', hstack, stackLe] at hσle
        | cons t σ =>
            simp only [checkSeq, hσ', hstack]
            exact trivial
  case case32 =>
    intro w' h
    simp [checkSeq, specLe, *]
  case case33 =>
    rename_i sigs r w ex rest n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 S hsome ih1
    intro w' h
    obtain ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩ := h
    obtain ⟨S', hsome', hslot, hscov⟩ :=
      typeOfE_cov sigs w'.Γ w.Γ ex hΓ hcovΓ S hsome
    have hpush : worldLe { w' with σ := normalizeTy w'.η S' :: w'.σ }
        { w with σ := normalizeTy w.η S :: w.σ } := by
      have hnorm : normalizeTy w'.η S = normalizeTy w.η S :=
        congrArg (fun ξ => normalizeTy ξ S) hη
      rw [← hnorm]
      exact ⟨hη, hΓ,
        stackLe_cons_intro (normalizeTy_slotLe hslot hscov) hσle, hcovΓ,
        stackCov_cons_intro (normalizeTy_cov hscov) hcovσ⟩
    simp only [checkSeq, hsome, hsome']
    exact markThrow_specLe sigs ex (ih1 hsc _ hpush)
  case case46 =>
    intro w' h
    simp [checkSeq, specLe, *]
  case case47 =>
    rename_i sigs r w c body rest hpop ih2 ih1
    intro w' h
    obtain ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩ := h
    cases hσ : w.σ with
    | nil => simp [hσ, popTy] at hpop
    | cons t σ =>
        cases hσ' : w'.σ with
        | nil =>
            exfalso
            simp [hσ, hσ', stackLe] at hσle
        | cons t' σ' =>
            rw [hσ] at hpop
            rw [hσ, hσ'] at hσle
            rw [hσ, hσ'] at hcovσ
            obtain ⟨hslot, hrest⟩ := hσle
            obtain ⟨-, hcovσ'⟩ := hcovσ
            obtain ⟨hnil, hpop'⟩ := popTy_some_nil_cov hslot hrest hpop
            subst σ'
            have hw0 : worldLe { w' with σ := [] } { w with σ := [] } :=
              ⟨hη, hΓ, by simp [stackLe], hcovΓ, by simp [stackCov]⟩
            have hbody := ih2 hsc ({ w' with σ := [] }) hw0
            have hk := fold_worlds_specLe sigs r rest
              (fun u v huv => ih1 v hsc u huv)
            simp only [checkSeq, hσ, hσ', hpop, hpop']
            exact checkLoopBody_spec (.kRepeatTest c body) []
              (fun fs => fs.foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows)
              hbody hk
  case case48 =>
    intro w' h
    simp [checkSeq, specLe, *]
  case case49 =>
    intro w' h
    simp [checkSeq, specLe, *]
  case case50 =>
    rename_i sigs r w x body rest hpop ih2 ih1
    intro w' h
    obtain ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩ := h
    cases hσ : w.σ with
    | nil => simp [hσ, popA, popTy] at hpop
    | cons t σ =>
        cases hσ' : w'.σ with
        | nil =>
            exfalso
            simp [hσ, hσ', stackLe] at hσle
        | cons t' σ' =>
            rw [hσ] at hpop
            rw [hσ, hσ'] at hσle
            obtain ⟨hslot, hrest⟩ := hσle
            have hp : popTy [.anyValue .list] (t :: σ) = some [] := by
              simpa [popA] using hpop
            obtain ⟨hnil, hpop'⟩ := popTy_some_nil_cov hslot hrest hp
            have hpopA' : popA (.anyValue .list) (t' :: σ') = some [] := by
              simpa [popA] using hpop'
            subst σ'
            have hw0 : worldLe
                { w' with Γ := (x, langT) :: w'.Γ, σ := [] }
                { w with Γ := (x, langT) :: w.Γ, σ := [] } :=
              ⟨hη, envLe_cons hΓ (slotLe_refl _), by simp [stackLe],
                envCov_cons hcovΓ (tyCov_refl _ _), by simp [stackCov]⟩
            have hbody := ih2 hsc _ hw0
            have hk := fold_worlds_specLe sigs r rest
              (fun u v huv => ih1 v hsc u huv)
            simp only [checkSeq, hσ, hσ', hpop, hpopA']
            exact checkLoopBody_spec (.kForStart x body) []
              (fun fs => fs.foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows)
              hbody hk
  case case51 =>
    intro w' h
    simp [checkSeq, specLe, *]
  case case52 =>
    rename_i sigs r w x elems body rest hσ ih2 ih1
    intro w' h
    obtain ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩ := h
    cases hσ' : w'.σ with
    | nil =>
        have hw0 : worldLe
            { w' with Γ := (x, langT) :: w'.Γ, σ := w'.σ }
            { w with Γ := (x, langT) :: w.Γ, σ := w.σ } :=
          ⟨hη, envLe_cons hΓ (slotLe_refl _), hσle,
            envCov_cons hcovΓ (tyCov_refl _ _), hcovσ⟩
        have hbody := ih2 hsc _ hw0
        have hbody' : specLe
            (checkSeq sigs r { w' with Γ := (x, langT) :: w'.Γ, σ := [] } body)
            (checkSeq sigs r { w with Γ := (x, langT) :: w.Γ, σ := [] } body) := by
          rw [hσ', hσ] at hbody
          exact hbody
        have hk := fold_worlds_specLe sigs r rest
          (fun u v huv => ih1 v hsc u huv)
        simp only [checkSeq, hσ, hσ']
        exact checkLoopBody_spec (.kForBody x [] body) []
          (fun fs => fs.foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows)
          hbody' hk
    | cons t' σ'' =>
        exfalso
        simp [hσ, hσ', stackLe] at hσle
  case case53 =>
    rename_i sigs r w x elems body rest hσne
    intro w' h
    obtain ⟨hη, hΓ, hσle, hcovΓ, hcovσ⟩ := h
    cases hσ' : w'.σ with
    | nil =>
        cases hstack : w.σ with
        | nil => exact absurd hstack hσne
        | cons t σ =>
            exfalso
            simp [hσ', hstack, stackLe] at hσle
    | cons t' σ'' =>
        cases hstack : w.σ with
        | nil =>
            exfalso
            simp [hσ', hstack, stackLe] at hσle
        | cons t σ =>
            simp only [checkSeq, hσ', hstack]
            exact trivial
  case case56 =>
    intro w' h
    simp [checkSeq, specLe, *]
  case case57 =>
    rename_i sigs r w i rest n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 n23 n24 n25 n26 n27 ws hstep ih1
    intro w' h
    obtain ⟨ws', hstep', hcov⟩ := step1_cov sigs i w' w h ws hstep
    have hne : ws ≠ [] → ws' ≠ [] := by
      intro _ 
      exact step1_some_ne sigs i w' ws' hstep'
    have hpoint : ∀ u' u, worldLe u' u →
        specLe (checkSeq sigs r u' rest) (checkSeq sigs r u rest) :=
      fun u' u hu => ih1 u hsc u' hu
    simp only [checkSeq, hstep, hstep']
    exact fork_specLe hcov hne hpoint

/-- THE TERMINALITY COROLLARY: specialization preserves
    terminality. specLe carries the falls; checkSeq_exits turns
    empty falls into the exit bit. No separate induction needed. -/
theorem checkSeq_specialize_terminal (sigs : SigTable) (r : Ty)
    (w w' : World) (seq : List Instr) (hsc : sigParamsClosed sigs)
    (hle : worldLe w' w) {fb : Flows}
    (h : checkSeq sigs r w seq = TCResult.flows fb)
    (ht : terminal fb = Bool.true) :
    ∃ fb', checkSeq sigs r w' seq = TCResult.flows fb'
      ∧ terminal fb' = Bool.true := by
  have hspec := checkSeq_specialize sigs r w seq hsc w' hle
  rw [h] at hspec
  obtain ⟨fb', h', hcov⟩ := specLe_flows_elim hspec
  refine ⟨fb', h', ?_⟩
  have hf : fb.falls = [] :=
    List.isEmpty_iff.mp ((Bool.and_eq_true _ _).mp ht).2
  have hf' : fb'.falls = [] := by
    match hfl : fb'.falls with
    | [] => rfl
    | v :: vs =>
        have hvm : v ∈ fb'.falls := by
          rw [hfl]
          exact List.mem_cons.mpr (Or.inl rfl)
        obtain ⟨u, hu, -⟩ := hcov v hvm
        rw [hf] at hu
        cases hu
  have he := checkSeq_exits sigs r w' seq fb' h' hf'
  exact (Bool.and_eq_true _ _).mpr ⟨he, List.isEmpty_iff.mpr hf'⟩

theorem fork_single_terminal {sigs : SigTable} {r : Ty} {site : Instr}
    {ws : Worlds} {w : World} {seq : List Instr} {fb : Flows}
    (hsc : sigParamsClosed sigs)
    (hne : ws ≠ [])
    (hcov : ∀ u ∈ ws, worldLe u w)
    (hcoarse : checkSeq sigs r w seq = TCResult.flows fb)
    (hterm : terminal fb = Bool.true) :
    ∃ fb', forkTC site ws (fun u => checkSeq sigs r u seq)
      = TCResult.flows fb' ∧ terminal fb' = Bool.true := by
  have hbranch : ∀ u ∈ ws, ∃ fbu,
      checkSeq sigs r u seq = TCResult.flows fbu ∧ terminal fbu = Bool.true := by
    intro u hu
    obtain ⟨fbu, hflu, htermu⟩ :=
      checkSeq_specialize_terminal sigs r w u seq hsc (hcov u hu) hcoarse hterm
    exact ⟨fbu, hflu, htermu⟩
  obtain ⟨ffold, hfold⟩ := fold_flows_exists ws noFlows
    ⟨{ exits := Bool.false, throws := Bool.false, falls := [], assumes := [] }, rfl⟩
    (fun u hu => ⟨(hbranch u hu).choose, (hbranch u hu).choose_spec.1⟩)
  cases ws with
  | nil => exact absurd rfl hne
  | cons u us =>
      have hfork : forkTC site (u :: us)
          (fun v => checkSeq sigs r v seq) = TCResult.flows ffold := by
        simp only [forkTC, hfold]
      refine ⟨ffold, hfork, ?_⟩
      have hsingle : [w].foldl
          (fun acc v => mergeTC acc (checkSeq sigs r v seq)) noFlows
          = TCResult.flows fb := by
        simp [List.foldl_cons, List.foldl_nil, mergeTC, noFlows, hcoarse]
      refine fork_lift
        (J' := fun v => checkSeq sigs r v seq)
        (J := fun v => checkSeq sigs r v seq) ?_ ?_ (u :: us) [w] ?_ ?_ fb
        hsingle hterm ffold hfold
      · intro u' v hle fbu hflu hcfalls
        have hs := checkSeq_specialize sigs r v seq hsc u' hle
        rw [hflu] at hs
        obtain ⟨fbu', hflu', hcov⟩ := specLe_flows_elim hs
        refine ⟨fbu', hflu', ?_⟩
        cases hfl : fbu'.falls with
        | nil => rfl
        | cons x xs =>
            have hx : x ∈ fbu'.falls := by
              rw [hfl]
              exact List.mem_cons.mpr (Or.inl rfl)
            obtain ⟨y, hy, -⟩ := hcov x hx
            rw [hcfalls] at hy
            cases hy
      · intro u' v hle fbu hflu hcterm
        exact checkSeq_specialize_terminal sigs r v u' seq hsc hle hflu hcterm
      · intro u' hu'
        exact ⟨w, List.mem_cons.mpr (Or.inl rfl), hcov u' hu'⟩
      · intro v hv
        have hvw : v = w := by simpa using hv
        subst hvw
        exact ⟨u, List.mem_cons.mpr (Or.inl rfl), hcov u (List.mem_cons.mpr (Or.inl rfl))⟩

/- ## THE kRet ARM: the anticipated union becomes the delivered
    singleton. The callee's own kRet acceptance (inverted from its
    CURRENT frameChecks) gives [normalizeAtom η (typeOfV v)] ⊑ complTy retj; the
    caller's union-anticipated judgement then refines to the
    ordinary frameChecks via the terminality corollary. -/

theorem complTy_atomStable {cs : List Pending}
    (hstable : ∀ c ∈ cs, pendingStable c) :
    ∀ a ∈ complTy cs, atomStable a := by
  intro a ha
  simp only [complTy, List.mem_append] at ha
  rcases ha with ha | ha
  · obtain ⟨u, hu, hau⟩ := List.mem_flatten.mp ha
    obtain ⟨c, hc, hcu⟩ := List.mem_filterMap.mp hu
    cases c with
    | normal t =>
        have hts : tyStable t := hstable (.normal t) hc
        obtain rfl := Option.some.inj hcu
        obtain ⟨p, hp, hap⟩ := List.mem_map.mp hau
        obtain rfl := hap
        exact hts p hp
    | throw => simp at hcu
  · by_cases hct : complCanThrow cs = Bool.true
    · rw [if_pos hct] at ha
      rcases List.mem_cons.mp ha with ha | ha
      · obtain rfl := ha
        trivial
      · cases ha
    · rw [if_neg hct] at ha
      cases ha

theorem complTy_atomStable_sigCompls {sigs : SigTable} {n : «String»}
    (hsc : sigParamsClosed sigs) :
    ∀ a ∈ complTy (sigCompls sigs n), atomStable a := by
  cases hf : sigFind sigs n with
  | some pr =>
      obtain ⟨ps, retj⟩ := pr
      have hcompls : sigCompls sigs n = retj := sigCompls_of_sigFind hf
      rw [hcompls]
      exact complTy_atomStable ((hsc n ps retj hf).2)
  | none =>
      have hc : sigCompls sigs n = [Pending.throw] := by
        simp only [sigCompls, hf]
      rw [hc]
      intro a ha
      have hct : complCanThrow [Pending.throw] = Bool.true := rfl
      simp only [complTy, List.filterMap, List.flatten_nil,
        List.nil_append, hct, if_true, List.mem_cons, not_false_iff] at ha
      rcases ha with ha | ha
      · obtain rfl := ha
        trivial
      · cases ha

theorem tmoves_singleton_elim {a : VTy} {t : Ty}
    (h : tmoves [a] t = Bool.true) : ∃ b ∈ t, tmovesV a b = Bool.true := by
  have h1 : t.any (fun b => tmovesV a b) = Bool.true := by
    simpa [tmoves] using h
  obtain ⟨b, hb, hmv⟩ := List.any_eq_true.mp h1
  exact ⟨b, hb, hmv⟩

theorem tyCov_singleton_stable {η : HeapCallableTy} {a' : VTy} {t : Ty}
    (hnorm : normalizeAtom η a' = a')
    (hmove : tmoves [a'] t = Bool.true)
    (hstable : ∀ a ∈ t, atomStable a) : tyCov η [a'] t := by
  intro a ha
  simp only [List.mem_singleton] at ha
  obtain rfl := ha
  obtain ⟨b, hb, hmv⟩ := tmoves_singleton_elim hmove
  exact ⟨b, hb, atomCov_of_stable hnorm hmv (hstable b hb)⟩

theorem SR_kRet (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy) (s : FM) (r : Ty) :
    SR_arm sigs reg η .kRet s r := by
  intro _ _ hsc hpre
  cases s with
  | fdone => exact ⟨η, hpre⟩
  | fell => exact ⟨η, hpre⟩
  | frames fs heap nl =>
    cases fs with
    | nil => exact ⟨η, hpre⟩
    | cons f fs0 =>
        obtain ⟨stmts, env, eval, ret⟩ := f
        simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
        cases eval with
        | nil =>
            -- kRet with an EMPTY eval: the callee's own judgement
            -- read kRet at an empty top slot and rejected, so hpre
            -- is contradictory (the machine's no-push case never
            -- arises in typed states)
            exfalso
            obtain ⟨fb, hchk, -⟩ :=
              frameChecks_elim (f := { stmts := .kRet :: stmts, env := env,
                                       eval := [], ret := ret }) hpre.2.2.2.1.1
            rw [checkSeq] at hchk
            cases hchk
        | cons v eval' =>
            have hval : tmoves [normalizeAtom η (typeOfV v)] (complTy (sigCompls sigs ret))
                = Bool.true := by
              obtain ⟨fb2, hchk2, -⟩ := frameChecks_elim
                (f := { stmts := .kRet :: stmts, env := env,
                        eval := v :: eval', ret := ret }) hpre.2.2.2.1.1
              obtain ⟨t, σ2, hcons, htm⟩ := checkSeq_kRet_elim hchk2
              have hm : [normalizeAtom η (typeOfV v)] :: eval'.map (fun x => [normalizeAtom η (typeOfV x)])
                  = t :: σ2 := hcons
              obtain ⟨rfl, -⟩ := List.cons.inj hm
              simp only [sigRetTy] at htm
              exact htm
            cases fs0 with
            | nil =>
                have hr : complTy (sigCompls sigs ret) = r := hpre.2.2.2.2
                refine ⟨η, ?_⟩
                show tmoves [normalizeAtom η (typeOfV v)] r = Bool.true
                rw [← hr]
                exact hval
            | cons caller fs1 =>
                obtain ⟨cstmts, cenv, ceval, cret⟩ := caller
                refine ⟨η, hpre.1, ⟨?_, hpre.2.1.2.2⟩, ⟨?_, hpre.2.2.1.2.2⟩, ⟨?_, hpre.2.2.2.1.2.2⟩, ?_⟩
                · intro l hl
                  have h1 : l ∈ (locsOf v ++ ceval.flatMap locsOf)
                      ++ List.flatMap locsOf (List.map Prod.snd cenv) := hl
                  rcases List.mem_append.mp h1 with h1 | h1
                  · rcases List.mem_append.mp h1 with h1 | h1
                    · exact hpre.2.1.1 l (List.mem_append.mpr
                        (Or.inl (List.mem_append.mpr (Or.inl h1))))
                    · exact hpre.2.1.2.1 l (List.mem_append.mpr (Or.inl h1))
                  · exact hpre.2.1.2.1 l (List.mem_append.mpr (Or.inr h1))
                · exact hpre.2.2.1.2.1
                · obtain ⟨fb, hchk, hterm⟩ :=
                    frameOkUnder_elim (n := ret)
                      (f := ⟨cstmts, cenv, ceval, cret⟩) hpre.2.2.2.1.2.1
                  have hcov : tyCov η [normalizeAtom η (typeOfV v)]
                      (complTy (sigCompls sigs ret)) :=
                    tyCov_singleton_stable
                      (normalizeAtom_idem η (typeOfV v)) hval
                      (complTy_atomStable_sigCompls hsc)
                  have hslot : slotLe [normalizeAtom η (typeOfV v)]
                      (complTy (sigCompls sigs ret)) :=
                    ⟨tyLe_of_atom_cov (fun a' ha' => by
                        obtain ⟨b, hb, hac⟩ := hcov a' ha'
                        exact ⟨b, hb, atomCov_tmoves hac⟩),
                      fun _ => by simp⟩
                  have hw : worldLe
                      { η := η, Γ := envTyOf η cenv,
                        σ := [normalizeAtom η (typeOfV v)] :: ceval.map (fun x => [normalizeAtom η (typeOfV x)]) }
                      { η := η, Γ := envTyOf η cenv,
                        σ := complTy (sigCompls sigs ret)
                          :: ceval.map (fun x => [normalizeAtom η (typeOfV x)]) } :=
                    ⟨rfl, envLe_refl _,
                      stackLe_cons_intro hslot (stackLe_refl _),
                      envCov_refl _ _,
                      stackCov_cons_intro hcov (stackCov_refl _ _)⟩
                  obtain ⟨fb', h', ht'⟩ :=
                    checkSeq_specialize_terminal sigs (sigRetTy sigs cret)
                      _ _ cstmts hsc hw hchk hterm
                  have hgoal : (match checkSeq sigs (sigRetTy sigs cret)
                      { η := η, Γ := envTyOf η cenv,
                        σ := [normalizeAtom η (typeOfV v)] :: ceval.map (fun x => [normalizeAtom η (typeOfV x)]) }
                      cstmts with
                    | TCResult.flows fb => terminal fb = Bool.true
                    | x => False) := by
                    rw [h']
                    exact ht'
                  exact hgoal
                · have h1 : machineRet sigs
                      (⟨.kRet :: stmts, env, v :: eval', ret⟩
                        :: ⟨cstmts, cenv, ceval, cret⟩ :: fs1)
                      = machineRet sigs (⟨cstmts, cenv, ceval, cret⟩ :: fs1) :=
                    machineRet_cons_cons
                  have h2 : machineRet sigs (⟨cstmts, cenv, v :: ceval, cret⟩ :: fs1)
                      = machineRet sigs (⟨cstmts, cenv, ceval, cret⟩ :: fs1) :=
                    machineRet_cons_congr rfl
                  exact h2.trans (h1.symm.trans hpre.2.2.2.2)


theorem frameTyped_kEval_nat {sigs : SigTable} {r : Ty} {n : Nat} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameTyped sigs η r ⟨.kEval (.nat n) :: rest, env, eval, ret⟩) :
    frameTyped sigs η r ⟨rest, env, .number (↑n : Int) :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  rw [checkSeq_kEval_nat] at h
  exact h

theorem SR_kEval_nat (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy) (n : Nat) (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kEval (.nat n)) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone v fs heap nl n' => exact ⟨η, hpre⟩
  | fell fs heap nl n' => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          obtain ⟨hhk, hwf⟩ := heapOk_framesWf_push_nolocs
            (i := .kEval (.nat n)) (v := .number (↑n : Int))
            (by simp [locsOf]) hpre.2.1 hpre.2.2.1
          refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kEval_nat hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2.2.2.2

theorem frameTyped_kEval_nv {sigs : SigTable} {r : Ty} {x : «String»} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    (hΓ : tyLookup (envTyOf η env) x = some [normalizeAtom η (typeOfV v)])
    (h : frameTyped sigs η r ⟨.kEval (.nv x) :: rest, env, eval, ret⟩) :
    frameTyped sigs η r ⟨rest, env, v :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  rw [checkSeq_kEval_nv hΓ] at h
  exact h

theorem meetTy_typeOfV_notPresent (η : HeapCallableTy) (v : JSValue) :
    meetTy [normalizeAtom η (typeOfV v)] [.notPresent] = [] := by
  cases v with
  | compl b w =>
      cases b <;> simp [typeOfV, normalizeAtom, meetTy, meetAtom]
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _ | descV _ =>
      simp [typeOfV, normalizeAtom, meetTy, meetAtom]

theorem removeTy_typeOfV_notPresent (η : HeapCallableTy) (v : JSValue) :
    removeTy [normalizeAtom η (typeOfV v)] [.notPresent] = [normalizeAtom η (typeOfV v)] := by
  cases v with
  | compl b w =>
      cases b <;> simp [typeOfV, normalizeAtom, removeTy, removeAtom, tmovesV,
        isBoolClass, isBoolSing]
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _ | descV _ =>
      simp [typeOfV, normalizeAtom, removeTy, removeAtom, tmovesV, isBoolClass, isBoolSing]

theorem envLe_shadow_same {Γ : TyEnv} {x : «String»} {t : Ty}
    (h : tyLookup Γ x = some t) : envLe Γ ((x, t) :: Γ) := by
  refine ⟨fun y => ?_, fun y s' hs' => ?_, fun y s hs hne => ?_⟩
  all_goals
    by_cases hxy : x = y <;> simp_all [tyLookup, tyLe] <;>
      first
        | exact tmoves_refl _
        | (intro a ha; exact ⟨a, ha, tmovesV_refl a⟩)

theorem envCov_shadow_same {η : HeapCallableTy} {Γ : TyEnv} {x : «String»} {t : Ty}
    (h : tyLookup Γ x = some t) : envCov η Γ ((x, t) :: Γ) := by
  intro y s' hs'
  by_cases hxy : x = y
  · subst hxy
    have hs'e : s' = t := Option.some.inj (hs'.symm.trans h)
    subst hs'e
    exact ⟨s', by simp [tyLookup], tyCov_refl η s'⟩
  · exact ⟨s', by
      simp only [tyLookup, if_neg (fun he => hxy (beq_iff_eq.mp he))]
      exact hs', tyCov_refl η s'⟩

theorem frameTyped_kEval_varNotPresent_absent {sigs : SigTable} {r : Ty}
    {x : «String»} {rest : List Instr} {env : Env} {eval : List JSValue}
    {ret : «String»}
    (hΓ : tyLookup (envTyOf η env) x = none)
    (h : frameTyped sigs η r ⟨.kEval (.varNotPresent x) :: rest, env, eval, ret⟩) :
    frameTyped sigs η r ⟨rest, env, .boolean Bool.true :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  simp only [checkSeq, hΓ] at h
  exact h

theorem frameTyped_kEval_varNotPresent_present {sigs : SigTable} {r : Ty}
    {x : «String»} {v : JSValue} {rest : List Instr} {env : Env}
    {eval : List JSValue} {ret : «String»} {hsc : sigParamsClosed sigs}
    (hΓ : tyLookup (envTyOf η env) x = some [normalizeAtom η (typeOfV v)])
    (h : frameTyped sigs η r ⟨.kEval (.varNotPresent x) :: rest, env, eval, ret⟩) :
    frameTyped sigs η r ⟨rest, env, .boolean Bool.false :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  have hstep : checkSeq sigs r
      { η := η, Γ := envTyOf η env, σ := eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
      (.kEval (.varNotPresent x) :: rest)
      = checkSeq sigs r
        { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: envTyOf η env,
          σ := [.isValue (.boolean Bool.false)] :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
        rest := by
    simp [checkSeq, hΓ, split1, meetTy_typeOfV_notPresent,
      removeTy_typeOfV_notPresent, forkTC, mergeTC_noFlows, normalizeAtom]
  rw [hstep] at h
  have hres : ∃ fb, checkSeq sigs r
      { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: envTyOf η env,
        σ := [.isValue (.boolean Bool.false)] :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
      rest = TCResult.flows fb ∧ terminal fb = Bool.true := by
    cases hres : checkSeq sigs r
        { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: envTyOf η env,
          σ := [.isValue (.boolean Bool.false)] :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
        rest with
    | flows fb => exact ⟨fb, rfl, by rw [hres] at h; exact h⟩
    | reject s why => rw [hres] at h; exact h.elim
  obtain ⟨fb, hchk, hterm⟩ := hres
  have hle : worldLe
      { η := η, Γ := envTyOf η env,
        σ := [.isValue (.boolean Bool.false)] :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
      { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: envTyOf η env,
        σ := [.isValue (.boolean Bool.false)] :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) } :=
    ⟨rfl, envLe_shadow_same hΓ,
      stackLe_cons_intro (slotLe_refl _) (stackLe_refl _),
      envCov_shadow_same hΓ,
      stackCov_cons_intro (tyCov_refl _ _) (stackCov_refl _ _)⟩
  obtain ⟨fb', hchk', hterm'⟩ :=
    checkSeq_specialize_terminal sigs r _ _ rest hsc hle hchk hterm
  simp only [typeOfV, normalizeAtom] at hchk' ⊢
  rw [hchk']
  exact hterm'

theorem SR_kEval_varNotPresent (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kEval (.varNotPresent x)) s r := by
  intro _ _ hsc hpre
  cases s with
  | fdone v fs heap nl n => exact ⟨η, hpre⟩
  | fell fs heap nl n => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases hl : lookup env x with
          | none =>
              have hΓ : tyLookup (envTyOf η env) x = none := by
                have hbridge := envTyOf_lookup η env x
                simp only [hl, Option.map_none] at hbridge
                exact hbridge.symm
              simp only [fstep, hl]
              obtain ⟨hhk, hwf⟩ := heapOk_framesWf_push_nolocs
                (i := .kEval (.varNotPresent x)) (v := .boolean Bool.true)
                (by simp [locsOf]) hpre.2.1 hpre.2.2.1
              refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kEval_varNotPresent_absent hΓ
                hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2.2.2.2
          | some v =>
              have hΓ : tyLookup (envTyOf η env) x = some [normalizeAtom η (typeOfV v)] := by
                have hbridge := envTyOf_lookup η env x
                simp only [hl, Option.map_some] at hbridge
                exact hbridge.symm
              simp only [fstep, hl]
              obtain ⟨hhk, hwf⟩ := heapOk_framesWf_push_nolocs
                (i := .kEval (.varNotPresent x)) (v := .boolean Bool.false)
                (by simp [locsOf]) hpre.2.1 hpre.2.2.1
              refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kEval_varNotPresent_present (hsc := hsc) hΓ
                  hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2.2.2.2

theorem frameTyped_kEval_nv_reject_unbound {sigs : SigTable} {r : Ty} {x : «String»}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    (hx : lookup env x = none) :
    frameTyped sigs η r ⟨.kEval (.nv x) :: rest, env, eval, ret⟩ = False := by
  have hΓ : tyLookup (envTyOf η env) x = none := by
    have hbridge := envTyOf_lookup η env x
    simp only [hx, Option.map_none] at hbridge
    exact hbridge.symm
  simp only [frameTyped, frameWorld]
  simp only [checkSeq, typeOfE, hΓ]

theorem SR_kEval_nv (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy) (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kEval (.nv x)) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone v fs heap nl n => exact ⟨η, hpre⟩
  | fell fs heap nl n => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases hl : lookup env x with
          | none =>
              have h1 : frameTyped sigs η (sigRetTy sigs ret)
                  ⟨.kEval (.nv x) :: stmts, env, eval, ret⟩ := hpre.2.2.2.1.1
              rw [frameTyped_kEval_nv_reject_unbound hl] at h1
              exact h1.elim
          | some v =>
              simp only [fstep, hl]
              have hΓ : tyLookup (envTyOf η env) x = some [normalizeAtom η (typeOfV v)] := by
                have hbridge := envTyOf_lookup η env x
                simp only [hl, Option.map_some] at hbridge
                exact hbridge.symm
              obtain ⟨hhk, hwf⟩ := heapOk_framesWf_push
                (i := .kEval (.nv x)) (v := v)
                (fun l hlv => hpre.2.1.1 l (List.mem_append.mpr
                  (Or.inr (List.mem_flatMap.mpr ⟨v, lookup_mem_snd hl, hlv⟩))))
                hpre.2.1 hpre.2.2.1
              refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kEval_nv hΓ hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2.2.2.2

theorem frameTyped_kTest_normal {sigs : SigTable} {r : Ty} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameTyped sigs η r ⟨.kTest :: rest, env, .compl Bool.false v :: eval, ret⟩) :
    frameTyped sigs η r ⟨rest, env, .boolean Bool.false :: .compl Bool.false v :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  have hn : normalizeAtom η (typeOfV (JSValue.compl Bool.false v))
      = VTy.complN (normalizeAtom η (typeOfV v)) := rfl
  rw [hn] at h ⊢
  rw [checkSeq_kTest_normal (p := normalizeAtom η (typeOfV v)) rfl] at h
  exact h

theorem frameTyped_kTest_throw {sigs : SigTable} {r : Ty} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameTyped sigs η r ⟨.kTest :: rest, env, .compl Bool.true v :: eval, ret⟩) :
    frameTyped sigs η r ⟨rest, env, .boolean Bool.true :: .compl Bool.true v :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  rw [checkSeq_kTest_throw rfl] at h
  exact h

theorem frameTyped_kTest_reject_nil {sigs : SigTable} {r : Ty}
    {rest : List Instr} {env : Env} {ret : «String»} :
    frameTyped sigs η r ⟨.kTest :: rest, env, [], ret⟩ = False := by
  simp [frameTyped, frameWorld, checkSeq, step1]

theorem frameTyped_kTest_reject {sigs : SigTable} {r : Ty} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    (hv : ∀ b w, v ≠ JSValue.compl b w) :
    frameTyped sigs η r ⟨.kTest :: rest, env, v :: eval, ret⟩ = False := by
  cases v with
  | compl b w => exact absurd rfl (hv b w)
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _ | descV _ =>
      simp [frameTyped, frameWorld, checkSeq, step1, complOnly, typeOfV, normalizeAtom]

theorem SR_kTest (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy) (s : FM) (r : Ty) :
    SR_arm sigs reg η .kTest s r := by
  intro _ _ _ hpre
  cases s with
  | fdone v fs heap nl n => exact ⟨η, hpre⟩
  | fell fs heap nl n => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases eval with
          | nil =>
              have h1 : frameTyped sigs η (sigRetTy sigs ret)
                  ⟨.kTest :: stmts, env, [], ret⟩ := hpre.2.2.2.1.1
              rw [frameTyped_kTest_reject_nil] at h1
              exact h1.elim
          | cons v eval' =>
              by_cases hv : ∃ b w, v = JSValue.compl b w
              · rcases hv with ⟨b, w, rfl⟩
                cases b
                · obtain ⟨hhk, hwf⟩ := heapOk_framesWf_push_nolocs
                    (i := .kTest) (v := .boolean Bool.false)
                    (eval := .compl Bool.false w :: eval')
                    (by simp [locsOf]) hpre.2.1 hpre.2.2.1
                  refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kTest_normal (r := sigRetTy sigs ret) hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2.2.2.2
                · obtain ⟨hhk, hwf⟩ := heapOk_framesWf_push_nolocs
                    (i := .kTest) (v := .boolean Bool.true)
                    (eval := .compl Bool.true w :: eval')
                    (by simp [locsOf]) hpre.2.1 hpre.2.2.1
                  refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kTest_throw (r := sigRetTy sigs ret) hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2.2.2.2
              · exfalso
                have h1 : frameTyped sigs η (sigRetTy sigs ret)
                    ⟨.kTest :: stmts, env, v :: eval', ret⟩ := hpre.2.2.2.1.1
                rw [frameTyped_kTest_reject (v := v) (by
                  intro b w h
                  exact hv ⟨b, w, h⟩)] at h1
                exact h1.elim

theorem frameTyped_kUnwrap {sigs : SigTable} {r : Ty} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameTyped sigs η r ⟨.kUnwrap :: rest, env, .compl Bool.false v :: eval, ret⟩) :
    frameTyped sigs η r ⟨rest, env, v :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  have hn : normalizeAtom η (typeOfV (JSValue.compl Bool.false v))
      = VTy.complN (normalizeAtom η (typeOfV v)) := rfl
  rw [hn] at h
  rw [checkSeq_kUnwrap (p := normalizeAtom η (typeOfV v)) rfl] at h
  exact h

theorem frameTyped_kUnwrap_reject_nil {sigs : SigTable} {r : Ty}
    {rest : List Instr} {env : Env} {ret : «String»} :
    frameTyped sigs η r ⟨.kUnwrap :: rest, env, [], ret⟩ = False := by
  simp [frameTyped, frameWorld, checkSeq, step1]

theorem frameTyped_kUnwrap_reject {sigs : SigTable} {r : Ty} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    (hv : ∀ w, v ≠ JSValue.compl Bool.false w) :
    frameTyped sigs η r ⟨.kUnwrap :: rest, env, v :: eval, ret⟩ = False := by
  cases v with
  | compl b w =>
      cases b
      · exact absurd rfl (hv w)
      · simp [frameTyped, frameWorld, checkSeq, step1, unwrapSlot, typeOfV, normalizeAtom]
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _ | descV _ =>
      simp [frameTyped, frameWorld, checkSeq, step1, unwrapSlot, typeOfV, normalizeAtom]

theorem SR_kUnwrap (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy) (s : FM) (r : Ty) :
    SR_arm sigs reg η .kUnwrap s r := by
  intro _ _ _ hpre
  cases s with
  | fdone v fs heap nl n => exact ⟨η, hpre⟩
  | fell fs heap nl n => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases eval with
          | nil =>
              have h1 : frameTyped sigs η (sigRetTy sigs ret)
                  ⟨.kUnwrap :: stmts, env, [], ret⟩ := hpre.2.2.2.1.1
              rw [frameTyped_kUnwrap_reject_nil] at h1
              exact h1.elim
          | cons v eval' =>
              by_cases hv : ∃ w, v = JSValue.compl Bool.false w
              · rcases hv with ⟨w, rfl⟩
                obtain ⟨hhk, hwf⟩ := heapOk_framesWf_swap_head
                  (v := w) (w := .compl Bool.false w)
                  (locsOf_compl Bool.false w).symm hpre.2.1 hpre.2.2.1
                refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kUnwrap (r := sigRetTy sigs ret) hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
                rw [machineRet_head_swap]
                exact hpre.2.2.2.2
              · exfalso
                have h1 : frameTyped sigs η (sigRetTy sigs ret)
                    ⟨.kUnwrap :: stmts, env, v :: eval', ret⟩ := hpre.2.2.2.1.1
                rw [frameTyped_kUnwrap_reject (v := v) (by
                  intro w h
                  exact hv ⟨w, h⟩)] at h1
                exact h1.elim

theorem frameTyped_pThrowC {sigs : SigTable} {r : Ty} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameTyped sigs η r ⟨.kPrim1 .pThrowC :: rest, env, v :: eval, ret⟩) :
    frameTyped sigs η r ⟨rest, env, .compl Bool.true v :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  rw [checkSeq_pThrowC_slot rfl] at h
  exact h

theorem frameTyped_pThrowC_reject_nil {sigs : SigTable} {r : Ty}
    {rest : List Instr} {env : Env} {ret : «String»} :
    frameTyped sigs η r ⟨.kPrim1 .pThrowC :: rest, env, [], ret⟩ = False := by
  simp [frameTyped, frameWorld, checkSeq, step1]

theorem SR_kPrim1_pThrowC (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy) (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kPrim1 .pThrowC) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone v fs heap nl n => exact ⟨η, hpre⟩
  | fell fs heap nl n => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases eval with
          | nil =>
              have h1 : frameTyped sigs η (sigRetTy sigs ret)
                  ⟨.kPrim1 .pThrowC :: stmts, env, [], ret⟩ := hpre.2.2.2.1.1
              rw [frameTyped_pThrowC_reject_nil] at h1
              exact h1.elim
          | cons v eval' =>
              obtain ⟨hhk, hwf⟩ := heapOk_framesWf_swap_head
                (v := .compl Bool.true v) (w := v)
                (locsOf_compl Bool.true v) hpre.2.1 hpre.2.2.1
              refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_pThrowC hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2.2.2.2

theorem frameTyped_pWrapC_bare {sigs : SigTable} {r : Ty} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    (hbar : isBareVTy (typeOfV v) = Bool.true)
    (h : frameTyped sigs η r ⟨.kPrim1 .pWrapC :: rest, env, v :: eval, ret⟩) :
    frameTyped sigs η r ⟨rest, env, .compl Bool.false v :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  rw [checkSeq_pWrapC_slot rfl
    (by rw [isBareVTy_normalizeAtom]; exact hbar)] at h
  exact h

theorem frameTyped_pWrapC_compl {sigs : SigTable} {r : Ty} {b : Bool} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameTyped sigs η r ⟨.kPrim1 .pWrapC :: rest, env, .compl b v :: eval, ret⟩) :
    frameTyped sigs η r ⟨rest, env, .compl b v :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  cases b <;> simp [checkSeq, step1, complOnly, typeOfV, forkTC, mergeTC_noFlows, normalizeAtom] at h ⊢ <;> exact h

theorem frameTyped_pWrapC_reject_nil {sigs : SigTable} {r : Ty}
    {rest : List Instr} {env : Env} {ret : «String»} :
    frameTyped sigs η r ⟨.kPrim1 .pWrapC :: rest, env, [], ret⟩ = False := by
  simp [frameTyped, frameWorld, checkSeq, step1]

theorem SR_kPrim1_pWrapC (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy) (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kPrim1 .pWrapC) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone v fs heap nl n => exact ⟨η, hpre⟩
  | fell fs heap nl n => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases eval with
          | nil =>
              have h1 : frameTyped sigs η (sigRetTy sigs ret)
                  ⟨.kPrim1 .pWrapC :: stmts, env, [], ret⟩ := hpre.2.2.2.1.1
              rw [frameTyped_pWrapC_reject_nil] at h1
              exact h1.elim
          | cons v eval' =>
              cases v with
              | compl b w =>
                  obtain ⟨hhk, hwf⟩ := heapOk_framesWf_swap_head
                    (v := .compl b w) (w := .compl b w) rfl hpre.2.1 hpre.2.2.1
                  refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_pWrapC_compl (r := sigRetTy sigs ret) hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2.2.2.2
              | undefined =>
                  obtain ⟨hhk, hwf⟩ := heapOk_framesWf_swap_head
                    (v := .compl Bool.false JSValue.undefined) (w := JSValue.undefined)
                    (locsOf_compl Bool.false JSValue.undefined) hpre.2.1 hpre.2.2.1
                  refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_pWrapC_bare (v := JSValue.undefined) (by simp [isBareVTy, typeOfV, normalizeAtom]) hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2.2.2.2
              | null =>
                  obtain ⟨hhk, hwf⟩ := heapOk_framesWf_swap_head
                    (v := .compl Bool.false JSValue.null) (w := JSValue.null)
                    (locsOf_compl Bool.false JSValue.null) hpre.2.1 hpre.2.2.1
                  refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_pWrapC_bare (v := JSValue.null) (by simp [isBareVTy, typeOfV, normalizeAtom]) hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2.2.2.2
              | boolean b =>
                  obtain ⟨hhk, hwf⟩ := heapOk_framesWf_swap_head
                    (v := .compl Bool.false (JSValue.boolean b)) (w := JSValue.boolean b)
                    (locsOf_compl Bool.false (JSValue.boolean b)) hpre.2.1 hpre.2.2.1
                  refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_pWrapC_bare (v := JSValue.boolean b) (by simp [isBareVTy, typeOfV, normalizeAtom]) hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2.2.2.2
              | number n =>
                  obtain ⟨hhk, hwf⟩ := heapOk_framesWf_swap_head
                    (v := .compl Bool.false (JSValue.number n)) (w := JSValue.number n)
                    (locsOf_compl Bool.false (JSValue.number n)) hpre.2.1 hpre.2.2.1
                  refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_pWrapC_bare (v := JSValue.number n) (by simp [isBareVTy, typeOfV, normalizeAtom]) hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2.2.2.2
              | str s =>
                  obtain ⟨hhk, hwf⟩ := heapOk_framesWf_swap_head
                    (v := .compl Bool.false (JSValue.str s)) (w := JSValue.str s)
                    (locsOf_compl Bool.false (JSValue.str s)) hpre.2.1 hpre.2.2.1
                  refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_pWrapC_bare (v := JSValue.str s) (by simp [isBareVTy, typeOfV, normalizeAtom]) hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2.2.2.2
              | obj a =>
                  obtain ⟨hhk, hwf⟩ := heapOk_framesWf_swap_head
                    (v := .compl Bool.false (JSValue.obj a)) (w := JSValue.obj a)
                    (locsOf_compl Bool.false (JSValue.obj a)) hpre.2.1 hpre.2.2.1
                  refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_pWrapC_bare (v := JSValue.obj a) (by simp [isBareVTy, typeOfV, normalizeAtom]) hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2.2.2.2
              | listV xs =>
                  obtain ⟨hhk, hwf⟩ := heapOk_framesWf_swap_head
                    (v := .compl Bool.false (JSValue.listV xs)) (w := JSValue.listV xs)
                    (locsOf_compl Bool.false (JSValue.listV xs)) hpre.2.1 hpre.2.2.1
                  refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_pWrapC_bare (v := JSValue.listV xs) (by simp [isBareVTy, typeOfV, normalizeAtom]) hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2.2.2.2
              | descV d =>
                  obtain ⟨hhk, hwf⟩ := heapOk_framesWf_swap_head
                    (v := .compl Bool.false (JSValue.descV d)) (w := JSValue.descV d)
                    (locsOf_compl Bool.false (JSValue.descV d)) hpre.2.1 hpre.2.2.1
                  refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_pWrapC_bare (v := JSValue.descV d) (by simp [isBareVTy, typeOfV, normalizeAtom]) hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2.2.2.2
/-- ## kMkList / kNewSlot: value-pushing arms. The checker pushes
    the CLASS atom (anyValue list / obj) and typeOfV of the machine's
    pushed value IS that atom - the transfer is direct. -/

theorem popTyN_append_anyT : ∀ (l₁ l₂ : List Ty),
    popTyN l₁.length anyT (l₁ ++ l₂)
      = if l₁.all (fun t => tmoves t anyT) then some l₂ else none := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; simp [popTyN]
  | cons t ts ih =>
      intro l₂
      cases ht : tmoves t anyT with
      | false =>
          have hall : (t :: ts).all (fun t => tmoves t anyT) = Bool.false := by
            simp only [List.all_cons, ht, Bool.false_and]
          simp [popTyN, popTy, ht, hall]
      | true =>
          have hall : (t :: ts).all (fun t => tmoves t anyT)
              = ts.all (fun t => tmoves t anyT) := by
            simp only [List.all_cons, ht, Bool.true_and]
          simp only [popTyN, List.length_cons, popTy, List.cons_append, ht,
            if_true, hall]
          exact ih l₂

/-- The n-indexed form (safe as a simp argument: no length
    back-rewriting). -/
theorem popTyN_anyT_append {n : Nat} {l₁ l₂ : List Ty} (hlen : l₁.length = n) :
    popTyN n anyT (l₁ ++ l₂)
      = if l₁.all (fun t => tmoves t anyT) then some l₂ else none := by
  subst hlen
  exact popTyN_append_anyT l₁ l₂

theorem popTyN_anyT_short : ∀ (n : Nat) (l : List Ty),
    l.length < n → popTyN n anyT l = none := by
  intro n
  induction n with
  | zero => intro l h; omega
  | succ k ih =>
      intro l h
      cases l with
      | nil => simp [popTyN, popTy]
      | cons t l' =>
          cases ht : tmoves t anyT with
          | false => simp [popTyN, popTy, ht]
          | true =>
              simp only [popTyN, List.length_cons, popTy, ht, if_true,
                List.cons_append]
              exact ih l' (by simp only [List.length_cons] at h; omega)

theorem checkSeq_kMkList {sigs : SigTable} {r : Ty} {W : World}
    {ts σ' : List Ty} {rest : List Instr}
    (hσ : W.σ = ts ++ σ')
    (hall : ts.all (fun t => tmoves t anyT) = Bool.true) :
    checkSeq sigs r W (.kMkList ts.length :: rest)
      = checkSeq sigs r { W with σ := [.anyValue .list] :: σ' } rest := by
  simp only [checkSeq, step1, hσ, popTyN_append_anyT, hall, reduceIte,
    Option.bind, Option.some.injEq, forkTC, List.foldl, mergeTC_noFlows]

/-- The generic value-push refinement: the machine pushes the
    CONCRETE singleton [normalizeAtom η (typeOfV v)] below the CLASS atom the checker
    pushed; specialization carries terminality (the kRet pattern). -/
theorem frameTyped_pushRefine {sigs : SigTable} {r : Ty} {v : JSValue}
    {rest : List Instr} {env : Env} {eval' : List JSValue} {ret : «String»}
    {T : Ty} (hsc : sigParamsClosed sigs)
    (hslot : slotLe [normalizeAtom η (typeOfV v)] T)
    (hcov : tyCov η [normalizeAtom η (typeOfV v)] T)
    (h : (match checkSeq sigs r
        { η := η, Γ := envTyOf η env, σ := T :: eval'.map (fun x => [normalizeAtom η (typeOfV x)]) }
        rest with
      | .flows fb => terminal fb = Bool.true
      | x => False)) :
    (match checkSeq sigs r
        { η := η, Γ := envTyOf η env, σ := [normalizeAtom η (typeOfV v)] :: eval'.map (fun x => [normalizeAtom η (typeOfV x)]) }
        rest with
      | .flows fb => terminal fb = Bool.true
      | x => False) := by
  have hres : ∃ fb, checkSeq sigs r
      { η := η, Γ := envTyOf η env, σ := T :: eval'.map (fun x => [normalizeAtom η (typeOfV x)]) }
      rest = TCResult.flows fb ∧ terminal fb = Bool.true := by
    cases hres : checkSeq sigs r
        { η := η, Γ := envTyOf η env, σ := T :: eval'.map (fun x => [normalizeAtom η (typeOfV x)]) }
        rest with
    | flows fb => exact ⟨fb, rfl, by rw [hres] at h; exact h⟩
    | reject s w => rw [hres] at h; exact h.elim
  obtain ⟨fb, hchk, hterm⟩ := hres
  have hw : worldLe
      { η := η, Γ := envTyOf η env, σ := [normalizeAtom η (typeOfV v)] :: eval'.map (fun x => [normalizeAtom η (typeOfV x)]) }
      { η := η, Γ := envTyOf η env, σ := T :: eval'.map (fun x => [normalizeAtom η (typeOfV x)]) } :=
    ⟨rfl, envLe_refl _,
      stackLe_cons_intro hslot (stackLe_refl _),
      envCov_refl _ _,
      stackCov_cons_intro hcov (stackCov_refl _ _)⟩
  obtain ⟨fb', h', ht'⟩ :=
    checkSeq_specialize_terminal sigs r _ _ rest hsc hw hchk hterm
  rw [h']
  exact ht'

theorem frameTyped_kMkList {sigs : SigTable} {r : Ty} {n : Nat}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    {ts σ' : List Ty} (hsc : sigParamsClosed sigs) (hlen : ts.length = n)
    (hσ : eval.map (fun x => [normalizeAtom η (typeOfV x)]) = ts ++ σ')
    (hall : ts.all (fun t => tmoves t anyT) = Bool.true)
    (h : frameTyped sigs η r ⟨.kMkList n :: rest, env, eval, ret⟩) :
    frameTyped sigs η r
      ⟨rest, env, .listV (eval.take ts.length).reverse :: eval.drop ts.length, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  have hdrop : σ' = (eval.map (fun x => [normalizeAtom η (typeOfV x)])).drop ts.length := by
    rw [hσ, List.drop_append]
    simp
  have hσ' : ({ η := η, Γ := envTyOf η env, σ := eval.map (fun x => [normalizeAtom η (typeOfV x)]) } : World).σ
      = ts ++ σ' := hσ
  have hstep : checkSeq sigs r
      { η := η, Γ := envTyOf η env, σ := eval.map (fun v => [normalizeAtom η (typeOfV v)]) }
      (Instr.kMkList n :: rest)
      = checkSeq sigs r { η := η, Γ := envTyOf η env, σ := [.anyValue .list] :: σ' } rest := by
    have h0 := checkSeq_kMkList (sigs := sigs) (r := r) (rest := rest)
      (W := { η := η, Γ := envTyOf η env, σ := eval.map (fun v => [normalizeAtom η (typeOfV v)]) })
      hσ' hall
    rw [hlen] at h0
    exact h0
  have hcoarse : (match checkSeq sigs r
      { η := η, Γ := envTyOf η env, σ := [.anyValue .list] :: σ' } rest with
    | .flows fb => terminal fb = Bool.true
    | x => False) := by
    rw [hstep] at h
    exact h
  rw [hdrop, ← List.map_drop] at hcoarse
  exact frameTyped_pushRefine (v := .listV (eval.take ts.length).reverse)
    (ret := ret) hsc
    (T := [.anyValue .list])
    ⟨by simp [tyLe, tmoves, tmovesV, typeOfV, tagOf, normalizeAtom], by simp⟩
    (atomCov_single (atomCov_of_pure_cover η
      (by simp [tmovesV, typeOfV, tagOf, normalizeAtom]) pureAtomDeep_bool))
    hcoarse

theorem frameTyped_kMkList_reject {sigs : SigTable} {r : Ty} {n : Nat}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    (hshort : eval.length < n) :
    frameTyped sigs η r ⟨.kMkList n :: rest, env, eval, ret⟩ = False := by
  simp only [frameTyped, frameWorld, checkSeq, step1,
    popTyN_anyT_short n (eval.map (fun x => [normalizeAtom η (typeOfV x)])) (by
      simp only [List.length_map]
      exact hshort)]

theorem SR_kMkList (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy) (n : Nat) (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kMkList n) s r := by
  intro _ _ hsc hpre
  cases s with
  | fdone => exact ⟨η, hpre⟩
  | fell => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          by_cases hshort : eval.length < n
          · exfalso
            have h1 : frameTyped sigs η (sigRetTy sigs ret)
                ⟨.kMkList n :: stmts, env, eval, ret⟩ := hpre.2.2.2.1.1
            rw [frameTyped_kMkList_reject hshort] at h1
            exact h1.elim
          · -- split the stack at n and refine
            have hlen : n ≤ eval.length := by omega
            have hsplit : eval.map (fun v => [normalizeAtom η (typeOfV v)])
                = (eval.map (fun x => [normalizeAtom η (typeOfV x)])).take n
                  ++ (eval.map (fun x => [normalizeAtom η (typeOfV x)])).drop n :=
              (List.take_append_drop n _).symm
            have htake : ((eval.map (fun x => [normalizeAtom η (typeOfV x)])).take n).length = n :=
              List.length_take_of_le (by simp only [List.length_map]; omega)
            have hall : ((eval.map (fun x => [normalizeAtom η (typeOfV x)])).take n).all
                (fun t => tmoves t anyT) = Bool.true := by
              cases hall : ((eval.map (fun x => [normalizeAtom η (typeOfV x)])).take n).all
                  (fun t => tmoves t anyT) with
              | true => rfl
              | false =>
                  exfalso
                  have h1 : frameTyped sigs η (sigRetTy sigs ret)
                      ⟨.kMkList n :: stmts, env, eval, ret⟩ := hpre.2.2.2.1.1
                  simp only [frameTyped, frameWorld] at h1
                  rw [hsplit] at h1
                  simp only [checkSeq, step1, popTyN_anyT_append htake, hall,
                    reduceIte] at h1
                  exact h1.elim
            simp only [fstep] at ⊢
            rw [if_neg (by omega)]
            simp only [stateTyped, framesTypedFrom] at ⊢
            have hf : frameTyped sigs η (sigRetTy sigs ret)
                ⟨.kMkList n :: stmts, env, eval, ret⟩ := hpre.2.2.2.1.1
            have hft := frameTyped_kMkList (n := n)
              (ts := (eval.map (fun x => [normalizeAtom η (typeOfV x)])).take n)
              (σ' := (eval.map (fun x => [normalizeAtom η (typeOfV x)])).drop n)
              hsc htake hsplit hall hf
            rw [htake] at hft
            obtain ⟨hhk, hwf⟩ := heapOk_framesWf_mkList (n := n)
              hpre.2.1 hpre.2.2.1
            refine ⟨η, hpre.1, hhk, hwf, ⟨hft, hpre.2.2.2.1.2⟩, ?_⟩
            rw [machineRet_head_swap]
            exact hpre.2.2.2.2

theorem checkSeq_kNewSlot {sigs : SigTable} {r : Ty} {W : World}
    {sn : «String»} {ord : Nat} {t : Ty} {σ' : List Ty} {rest : List Instr}
    (hσ : W.σ = t :: σ') (hsn : slotOfName sn = some ord)
    (htm : tmoves t anyT = Bool.true) :
    checkSeq sigs r W (.kNewSlot sn :: rest)
      = checkSeq sigs r { W with σ := objT :: σ' } rest := by
  simp only [checkSeq, step1, hσ, hsn, popTy, htm, reduceIte,
    Option.bind, Option.some.injEq, forkTC, List.foldl, mergeTC_noFlows]

theorem frameTyped_kNewSlot {sigs : SigTable} {r : Ty} {sn : «String»}
    {ord nl : Nat} {rest : List Instr} {env : Env} {eval : List JSValue}
    {ret : «String»} {v : JSValue}
    (hsc : sigParamsClosed sigs) (hsn : slotOfName sn = some ord)
    (h : frameTyped sigs η r ⟨.kNewSlot sn :: rest, env, v :: eval, ret⟩) :
    frameTyped sigs η r ⟨rest, env, .obj nl :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  cases htm2 : tmoves [normalizeAtom η (typeOfV v)] anyT with
  | false =>
      simp only [checkSeq, step1, hsn, popTy, htm2, reduceIte] at h
      exact h.elim
  | true =>
      have hstep : checkSeq sigs r
          ⟨η, envTyOf η env, [normalizeAtom η (typeOfV v)] :: eval.map (fun v2 => [normalizeAtom η (typeOfV v2)])⟩
          (Instr.kNewSlot sn :: rest)
          = checkSeq sigs r
            ⟨η, envTyOf η env, objT :: eval.map (fun v2 => [normalizeAtom η (typeOfV v2)])⟩
            rest :=
        checkSeq_kNewSlot (W := ⟨η, envTyOf η env,
            [normalizeAtom η (typeOfV v)] :: eval.map (fun v2 => [normalizeAtom η (typeOfV v2)])⟩) rfl hsn htm2
      rw [hstep] at h
      have hnlcov : tyCov η [normalizeAtom η (typeOfV (JSValue.obj nl))] objT := by
        intro a ha
        simp only [List.mem_singleton] at ha
        subst ha
        rw [show normalizeAtom η (typeOfV (JSValue.obj nl))
          = VTy.anyValue (Ctor.obj (η nl)) from rfl]
        cases hnl : η nl with
        | true =>
          exact ⟨VTy.anyValue (Ctor.obj Bool.true), by simp [objT],
            atomCov_refl η _⟩
        | false =>
          exact ⟨VTy.anyValue (Ctor.obj Bool.false), by simp [objT],
            atomCov_refl η _⟩
      exact frameTyped_pushRefine (v := .obj nl) (eval' := eval) (ret := ret) hsc
        (T := objT)
        ⟨by simp [tyLe, tmoves, tmovesV, typeOfV, tagOf, normalizeAtom, objT], by simp⟩
        hnlcov h

theorem frameTyped_kNewSlot_reject {sigs : SigTable} {r : Ty} {sn : «String»}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    (hnone : slotOfName sn = none) :
    frameTyped sigs η r ⟨.kNewSlot sn :: rest, env, eval, ret⟩ = False := by
  simp [frameTyped, frameWorld, checkSeq, step1, hnone]

/- ## Fresh-location η transfer -/

def atomNoObj : VTy → Prop
  | .isValue (.obj _) => False
  | .complN p => atomNoObj p
  | _ => True

def tyNoObj (t : Ty) : Prop := ∀ a ∈ t, atomNoObj a

def atomLocsOf : VTy → List Nat
  | .isValue (.obj l) => [l]
  | .complN p => atomLocsOf p
  | _ => []

theorem atomNoObj_of_locsNil {a : VTy} (h : atomLocsOf a = []) : atomNoObj a := by
  cases a with
  | isValue v =>
      cases v with
      | obj l => simp [atomLocsOf] at h
      | undefined | null | boolean _ | number _ | str _ | listV _
        | descV _ | compl _ _ => trivial
  | complN p => simp only [atomNoObj, atomLocsOf] at h ⊢
                exact atomNoObj_of_locsNil h
  | complT | anyValue _ | desc _ | notPresent => trivial

theorem atomLocsOf_typeOfV (v : JSValue) :
    ∀ l ∈ atomLocsOf (typeOfV v), l ∈ locsOf v := by
  cases v with
  | obj l => intro l' hl'; simp only [typeOfV, atomLocsOf, List.mem_singleton] at hl'
             obtain rfl := hl'; simp [locsOf]
  | undefined | null | boolean _ | number _ | str _ | listV _ | descV _ =>
      intro l' hl'; simp [typeOfV, atomLocsOf] at hl'
  | compl b w =>
      cases b
      · intro l' hl'
        simp only [typeOfV, atomLocsOf] at hl'
        rw [locsOf_compl Bool.false w]
        exact atomLocsOf_typeOfV w l' hl'
      · intro l' hl'; simp [typeOfV, atomLocsOf] at hl'

theorem meetAtom_eq {a b : VTy} {m : VTy} (hm : meetAtom a b = some m) :
    m = a ∨ m = b := by
  cases a with
  | isValue v =>
      cases b with
      | isValue w =>
          simp only [meetAtom] at hm
          split at hm
          · cases hm; exact Or.inl rfl
          · cases hm
      | complN q =>
          cases hm
      | complT =>
          cases hm
      | anyValue c' =>
          simp only [meetAtom] at hm
          split at hm
          · cases hm; exact Or.inl rfl
          · cases hm
      | desc fs' =>
          cases hm
      | notPresent =>
          cases hm
  | complN p =>
      cases b with
      | isValue w =>
          cases hm
      | complN q =>
          cases hm
      | complT =>
          cases hm
      | anyValue c' =>
          cases hm
      | desc fs' =>
          cases hm
      | notPresent =>
          cases hm
  | complT =>
      cases b with
      | isValue w =>
          cases hm
      | complN q =>
          cases hm
      | complT =>
          cases hm
      | anyValue c' =>
          cases hm
      | desc fs' =>
          cases hm
      | notPresent =>
          cases hm
  | anyValue c =>
      cases b with
      | isValue w =>
          simp only [meetAtom] at hm
          split at hm
          · cases hm; exact Or.inr rfl
          · cases hm
      | complN q =>
          cases hm
      | complT =>
          cases hm
      | anyValue c' =>
          simp only [meetAtom] at hm
          split at hm
          · cases hm; exact Or.inl rfl
          · cases hm
      | desc fs' =>
          cases c with
          | desc => simp only [meetAtom] at hm; cases hm; exact Or.inr rfl
          | undef | null | bool | num | str | obj _ | list => cases hm
      | notPresent =>
          cases hm
  | desc fs =>
      cases b with
      | isValue w =>
          cases hm
      | complN q =>
          cases hm
      | complT =>
          cases hm
      | anyValue c' =>
          cases c' with
          | desc => simp only [meetAtom] at hm; cases hm; exact Or.inl rfl
          | undef | null | bool | num | str | obj callable | list => cases hm
      | desc fs' =>
          simp only [meetAtom] at hm
          split at hm
          · cases hm; exact Or.inl rfl
          · cases hm
      | notPresent =>
          cases hm
  | notPresent =>
      cases b with
      | isValue w =>
          cases hm
      | complN q =>
          cases hm
      | complT =>
          cases hm
      | anyValue c' =>
          cases hm
      | desc fs' =>
          cases hm
      | notPresent =>
          simp only [meetAtom] at hm
          cases hm; exact Or.inl rfl

theorem meetAtom_noObj {a b : VTy} (ha : atomNoObj a) (hb : atomNoObj b)
    {m : VTy} (hm : meetAtom a b = some m) : atomNoObj m := by
  rcases meetAtom_eq hm with rfl | rfl
  · exact ha
  · exact hb

theorem mem_meetTy {S T : Ty} {a : VTy} (h : a ∈ meetTy S T) :
    ∃ b ∈ S, ∃ c ∈ T, meetAtom b c = some a := by
  simp only [meetTy, List.mem_flatMap] at h
  obtain ⟨b, hb, hbu⟩ := h
  refine ⟨b, hb, ?_⟩
  obtain ⟨c, hc, hcu⟩ := hbu
  refine ⟨c, hc, ?_⟩
  revert hcu
  cases hme : meetAtom b c with
  | none => intro hcu; simp at hcu
  | some m =>
      intro hcu
      simp only at hcu
      rcases List.mem_cons.mp hcu with rfl | h'
      · rfl
      · cases h'

theorem meetTy_noObj {S T : Ty} (hS : tyNoObj S) (hT : tyNoObj T) :
    ∀ a ∈ meetTy S T, atomNoObj a := by
  intro a ha
  obtain ⟨b, hb, c, hc, hme⟩ := mem_meetTy ha
  exact meetAtom_noObj (hS b hb) (hT c hc) hme

theorem removeAtom_noObj {a : VTy} {T : Ty} (ha : atomNoObj a) :
    ∀ b ∈ removeAtom a T, atomNoObj b := by
  intro b hb
  simp only [removeAtom] at hb
  split at hb
  · cases hb
  · split at hb
    · split at hb
      · cases hb
      · split at hb
        · rcases List.mem_cons.mp hb with rfl | hb <;> trivial
        · split at hb
          · rcases List.mem_cons.mp hb with rfl | hb <;> trivial
          · rcases List.mem_cons.mp hb with rfl | hb
            · trivial
            · cases hb
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · cases hb

theorem removeTy_noObj {S T : Ty} (hS : tyNoObj S) :
    ∀ a ∈ removeTy S T, atomNoObj a := by
  intro a ha
  simp only [removeTy, List.mem_flatMap] at ha
  obtain ⟨b, hb, hba⟩ := ha
  exact removeAtom_noObj (hS b hb) a hba

theorem complNormals_noObj {t : Ty} (h : tyNoObj t) : tyNoObj (complNormals t) := by
  intro a ha
  simp only [complNormals, List.mem_filterMap] at ha
  obtain ⟨b, hb, hba⟩ := ha
  revert hba
  cases b with
  | complN p =>
      intro hba
      simp only at hba
      cases hba
      exact h _ hb
  | isValue _ | complT | anyValue _ | desc _ | notPresent =>
      intro hba
      simp only at hba
      cases hba

theorem mem_option_map {α β : Type} (f : α → β) (o : Option α) (y : β)
    (h : y ∈ o.map f) : ∃ x, o = some x ∧ y = f x := by
  cases o with
  | none => cases h
  | some x => cases h; exact ⟨x, rfl, rfl⟩

theorem mem_option_match {α β : Type} (o : Option α) (f : α → Option β) (y : β)
    (h : y ∈ match o with | some x => f x | none => none) :
    ∃ x, o = some x ∧ y ∈ f x := by
  cases o with
  | none => cases h
  | some x => exact ⟨x, rfl, h⟩

theorem opt_pres {α β : Type} (o : Option α) (f : α → β) (P : β → Prop)
    (h : ∀ x, o = some x → P (f x)) {y : β}
    (hy : y ∈ o.map f) : P y := by
  cases o with
  | none => cases hy
  | some x => cases hy; exact h x rfl

theorem opt_pres_match {α β : Type} (o : Option α) (f : α → Option β)
    (P : β → Prop)
    (h : ∀ x, o = some x → ∀ y, y ∈ f x → P y) {y : β}
    (hy : y ∈ match o with | some x => f x | none => none) : P y := by
  cases o with
  | none => cases hy
  | some x => exact h x rfl y hy

theorem payloadOf_cons_two (p q : VTy) (l : Ty) :
    payloadOf (p.complN :: q.complN :: l)
      = (payloadOf (q.complN :: l)).map (fun ps => p :: ps) := by
  cases h : payloadOf (q.complN :: l) with
  | none => simp only [h, payloadOf, Option.map]
  | some ps => simp only [h, payloadOf, Option.map]

theorem payloadOf_single (p : VTy) : payloadOf [p.complN] = some [p] := rfl

theorem unwrapSlot_noObj {t : Ty} (h : tyNoObj t) :
    ∀ x ∈ unwrapSlot t, tyNoObj x := by
  have hrec : ∀ (l : Ty), (∀ b ∈ l, atomNoObj b) →
      ∀ x ∈ unwrapSlot l, tyNoObj x := by
    intro l
    induction l with
    | nil => intro _ x hx; cases hx; trivial
    | cons c l' ih =>
        intro hall x hx
        cases c with
        | complN p =>
            simp only [unwrapSlot] at hx
            refine opt_pres _ _ _ ?_ hx
            intro ps hxr a hax
            rcases List.mem_cons.mp hax with heq | hax
            · rw [heq]
              exact hall (.complN p) (List.mem_cons.mpr (Or.inl rfl))
            · exact ih (fun b hb => hall b (by simp [hb])) ps
                (by rw [hxr]; simp) a hax
        | isValue _ | complT | anyValue _ | desc _ | notPresent =>
            simp only [unwrapSlot] at hx
            cases hx
  exact hrec t (fun b hb => h b hb)

theorem bareOf_noObj {t : Ty} (h : tyNoObj t) :
    ∀ x ∈ bareOf t, tyNoObj x := by
  have hrec : ∀ (l : Ty), (∀ b ∈ l, atomNoObj b) →
      ∀ x ∈ bareOf l, tyNoObj x := by
    intro l
    induction l with
    | nil => intro _ x hx; cases hx; trivial
    | cons c l' ih =>
        intro hall x hx
        simp only [bareOf] at hx
        cases hcb : isBareVTy c with
        | false => rw [hcb] at hx; cases hx
        | true =>
            rw [hcb] at hx
            refine opt_pres _ _ _ ?_ hx
            intro ps hxr a hax
            rcases List.mem_cons.mp hax with heq | hax
            · rw [heq]
              exact hall _ (by simp)
            · exact ih (fun b hb => hall b (by simp [hb])) ps
                (by rw [hxr]; simp) a hax
  exact hrec t (fun b hb => h b hb)

theorem bareSlot_noObj {t : Ty} (h : tyNoObj t) :
    ∀ x ∈ bareSlot t, tyNoObj x := by
  have hrec : ∀ (l : Ty), (∀ b ∈ l, atomNoObj b) →
      ∀ x ∈ bareSlot l, tyNoObj x := by
    intro l
    induction l with
    | nil => intro _ x hx; cases hx; trivial
    | cons c l' ih =>
        intro hall x hx
        simp only [bareSlot] at hx
        cases hcb : isBareVTy c with
        | false => rw [hcb] at hx; cases hx
        | true =>
            rw [hcb] at hx
            refine opt_pres _ _ _ ?_ hx
            intro ps hxr a hax
            rcases List.mem_cons.mp hax with heq | hax
            · rw [heq]
              exact hall _ (by simp)
            · exact ih (fun b hb => hall b (by simp [hb])) ps
                (by rw [hxr]; simp) a hax
  exact hrec t (fun b hb => h b hb)

theorem payloadOf_noObj {t : Ty} (h : tyNoObj t) :
    ∀ x ∈ payloadOf t, tyNoObj x := by
  have hrec : ∀ (l : Ty), (∀ b ∈ l, atomNoObj b) →
      ∀ x ∈ payloadOf l, tyNoObj x := by
    intro l
    induction l with
    | nil => intro _ x hx; cases hx
    | cons c l' ih =>
        intro hall x hx
        cases c with
        | complN p =>
            cases l' with
            | nil =>
                cases hx
                intro a hax
                rcases List.mem_cons.mp hax with heq | hax
                · rw [heq]
                  exact hall (.complN p) (List.mem_cons.mpr (Or.inl rfl))
                · cases hax
            | cons d l'' =>
                cases d with
                | complN q =>
                    rw [payloadOf_cons_two] at hx
                    refine opt_pres _ _ _ ?_ hx
                    intro ps hxr a hax
                    rcases List.mem_cons.mp hax with heq | hax
                    · rw [heq]
                      exact hall (.complN p) (List.mem_cons.mpr (Or.inl rfl))
                    · exact ih (fun b hb => hall b (by simp [hb])) ps
                        (by rw [hxr]; simp) a hax
                | isValue _ | complT | anyValue _ | desc _ | notPresent =>
                    simp only [payloadOf] at hx
                    cases hx
        | isValue _ | complT | anyValue _ | desc _ | notPresent =>
            simp only [payloadOf] at hx
            cases hx
  exact hrec t (fun b hb => h b hb)

theorem payloadsOf_noObj {t : Ty} (h : tyNoObj t) :
    ∀ a ∈ payloadsOf t, atomNoObj a := by
  intro a ha
  simp only [payloadsOf, List.mem_flatMap] at ha
  obtain ⟨b, hb, hba⟩ := ha
  have h1 : atomNoObj b := h b hb
  cases b with
  | complN p =>
      have h2 : atomNoObj p := h1
      simp only at hba
      rcases List.mem_cons.mp hba with rfl | h'
      · exact h2
      · cases h'
  | isValue _ | complT | anyValue _ | desc _ | notPresent => simp at hba

theorem anyOf_noObj (cs : List Ctor) : ∀ a ∈ anyOf cs, atomNoObj a := by
  intro a ha
  simp only [anyOf, List.mem_map] at ha
  obtain ⟨c, _, rfl⟩ := ha
  trivial

theorem langT_noObj : ∀ a ∈ langT, atomNoObj a := anyOf_noObj langTags
theorem objT_noObj : ∀ a ∈ objT, atomNoObj a := by
  intro a ha
  simp only [objT, List.mem_cons] at ha
  rcases ha with rfl | rfl | h'
  · trivial
  · trivial
  · cases h'
theorem anyT_noObj : ∀ a ∈ anyT, atomNoObj a := anyOf_noObj anyTags

theorem complTy_noObj {cs : List Pending}
    (h : ∀ a ∈ complPayload cs, atomNoObj a) :
    ∀ a ∈ complTy cs, atomNoObj a := by
  intro a ha
  simp only [complTy, List.mem_append] at ha
  rcases ha with ha | ha
  · obtain ⟨u, hu, hau⟩ := List.mem_flatten.mp ha
    obtain ⟨c, hc, hcu⟩ := List.mem_filterMap.mp hu
    cases c with
    | normal t =>
        obtain rfl := Option.some.inj hcu
        obtain ⟨p, hp, hap⟩ := List.mem_map.mp hau
        obtain rfl := hap
        refine h p (List.mem_flatten.mpr ⟨t, ?_, ?_⟩)
        · exact List.mem_filterMap.mpr ⟨_, hc, rfl⟩
        · exact hp
    | throw => simp at hcu
  · by_cases hct : complCanThrow cs = Bool.true
    · simp only [complTy, if_pos hct, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at ha
      cases ha
      trivial
    · simp only [complTy, hct, ite_false, List.append_nil] at ha
      cases ha

theorem noObj_mem3 {a : VTy}
    (h : a ∈ [.anyValue Ctor.null, .anyValue (Ctor.obj Bool.true),
      .anyValue (Ctor.obj Bool.false)]) : atomNoObj a := by
  rcases List.mem_cons.mp h with rfl | h
  · trivial
  · rcases List.mem_cons.mp h with rfl | h
    · trivial
    · rcases List.mem_cons.mp h with rfl | h
      · trivial
      · cases h

theorem noObj_mem_single {a : VTy} {x : VTy} (h : a ∈ [x])
    (hx : atomNoObj x) : atomNoObj a := by
  rcases List.mem_cons.mp h with rfl | h'
  · exact hx
  · cases h'

theorem mopResult_noObj_t (nm : «String») :
    ∀ c ∈ mopResult nm, ∀ a ∈ complPayload [c], atomNoObj a := by
  intro c hc a ha
  cases c with
  | normal t =>
      · by_cases h1 : nm = "Get"
        · subst h1
          simp only [mopResult, List.mem_cons, List.not_mem_nil, or_false,
            Pending.normal.injEq] at hc
          rcases hc with rfl | hc <;>
            first
              | (simp only [complPayload, List.filterMap_nil, List.filterMap_cons, List.flatten_nil, List.flatten_cons, List.nil_append, List.append_nil] at ha
                 exact langT_noObj a ha)
              | cases hc
        · by_cases h2 : nm = "Call"
          · subst h2
            simp only [mopResult, List.mem_cons, List.not_mem_nil, or_false,
              Pending.normal.injEq] at hc
            rcases hc with rfl | hc <;>
              first
                | (simp only [complPayload, List.filterMap_nil, List.filterMap_cons, List.flatten_nil, List.flatten_cons, List.nil_append, List.append_nil] at ha
                   exact langT_noObj a ha)
                | cases hc
          · by_cases h3 : nm = "Iterator"
            · subst h3
              simp only [mopResult, List.mem_cons, List.not_mem_nil, or_false,
                Pending.normal.injEq] at hc
              rcases hc with rfl | hc <;>
                first
                  | (simp only [complPayload, List.filterMap_nil, List.filterMap_cons, List.flatten_nil, List.flatten_cons, List.nil_append, List.append_nil] at ha
                     exact objT_noObj a ha)
                  | cases hc
            · by_cases h4 : nm = "NextMethod"
              · subst h4
                simp only [mopResult, List.mem_cons, List.not_mem_nil, or_false,
                  Pending.normal.injEq] at hc
                rcases hc with rfl | hc <;>
                  first
                    | (simp only [complPayload, List.filterMap_nil, List.filterMap_cons, List.flatten_nil, List.flatten_cons, List.nil_append, List.append_nil] at ha
                       exact langT_noObj a ha)
                    | cases hc
              · by_cases h5 : nm = "Done"
                · subst h5
                  simp only [mopResult, List.mem_cons, List.not_mem_nil, or_false,
                    Pending.normal.injEq] at hc
                  rcases hc with rfl | hc <;>
                    first
                      | (simp only [complPayload, List.filterMap_nil, List.filterMap_cons, List.flatten_nil, List.flatten_cons, List.nil_append, List.append_nil] at ha
                         exact langT_noObj a ha)
                      | cases hc
                · by_cases h6 : nm = "Value"
                  · subst h6
                    simp only [mopResult, List.mem_cons, List.not_mem_nil, or_false,
                      Pending.normal.injEq] at hc
                    rcases hc with rfl | hc <;>
                      first
                        | (simp only [complPayload, List.filterMap_nil, List.filterMap_cons, List.flatten_nil, List.flatten_cons, List.nil_append, List.append_nil] at ha
                           exact langT_noObj a ha)
                        | cases hc
                  · by_cases h7 : nm = "Getter"
                    · subst h7
                      simp only [mopResult, List.mem_cons, List.not_mem_nil, or_false,
                        Pending.normal.injEq] at hc
                      rcases hc with rfl | hc <;>
                        first
                          | (simp only [complPayload, List.filterMap_nil, List.filterMap_cons, List.flatten_nil, List.flatten_cons, List.nil_append, List.append_nil] at ha
                             exact langT_noObj a ha)
                          | cases hc
                    · by_cases h8 : nm = "Setter"
                      · subst h8
                        simp only [mopResult, List.mem_cons, List.not_mem_nil, or_false,
                          Pending.normal.injEq] at hc
                        rcases hc with rfl | hc <;>
                          first
                            | (simp only [complPayload, List.filterMap_nil, List.filterMap_cons, List.flatten_nil, List.flatten_cons, List.nil_append, List.append_nil] at ha
                               exact langT_noObj a ha)
                            | cases hc
                      · by_cases h9 : nm = "GetPrototypeOf"
                        · subst h9
                          simp only [mopResult, List.mem_cons, List.not_mem_nil, or_false,
                            Pending.normal.injEq] at hc
                          rcases hc with rfl | hc <;>
                            first
                              | (simp only [complPayload, List.filterMap_nil, List.filterMap_cons, List.flatten_nil, List.flatten_cons, List.nil_append, List.append_nil, List.cons_append, objT] at ha
                                 exact noObj_mem3 ha)
                              | cases hc
                        · by_cases h10 : nm = "Writable"
                          · subst h10
                            simp only [mopResult, List.mem_cons, List.not_mem_nil, or_false,
                              Pending.normal.injEq] at hc
                            rcases hc with rfl | hc <;>
                              first
                                | (simp only [complPayload, List.filterMap_nil, List.filterMap_cons, List.flatten_nil, List.flatten_cons, List.nil_append, List.append_nil] at ha
                                   exact noObj_mem_single ha trivial)
                                | cases hc
                          · by_cases h11 : nm = "Enumerable"
                            · subst h11
                              simp only [mopResult, List.mem_cons, List.not_mem_nil, or_false,
                                Pending.normal.injEq] at hc
                              rcases hc with rfl | hc <;>
                                first
                                  | (simp only [complPayload, List.filterMap_nil, List.filterMap_cons, List.flatten_nil, List.flatten_cons, List.nil_append, List.append_nil] at ha
                                     exact noObj_mem_single ha trivial)
                                  | cases hc
                            · by_cases h12 : nm = "Configurable"
                              · subst h12
                                simp only [mopResult, List.mem_cons, List.not_mem_nil, or_false,
                                  Pending.normal.injEq] at hc
                                rcases hc with rfl | hc <;>
                                  first
                                    | (simp only [complPayload, List.filterMap_nil, List.filterMap_cons, List.flatten_nil, List.flatten_cons, List.nil_append, List.append_nil] at ha
                                       exact noObj_mem_single ha trivial)
                                    | cases hc
                              · by_cases h13 : nm = "GetOwnProperty"
                                · subst h13
                                  simp only [mopResult, List.mem_cons, List.not_mem_nil, or_false,
                                    Pending.normal.injEq] at hc
                                  rcases hc with rfl | hc <;>
                                    first
                                      | (simp only [complPayload, List.filterMap_nil, List.filterMap_cons, List.flatten_nil, List.flatten_cons, List.nil_append, List.append_nil] at ha
                                         exact noObj_mem_single ha trivial)
                                      | (rcases hc with rfl | hc <;>
                                          first
                                            | (simp only [complPayload, List.filterMap_nil, List.filterMap_cons, List.flatten_nil, List.flatten_cons, List.nil_append, List.append_nil] at ha
                                               exact noObj_mem_single ha trivial)
                                            | (rcases hc with rfl | hc <;>
                                                first
                                                  | (simp only [complPayload, List.filterMap_nil, List.filterMap_cons, List.flatten_nil, List.flatten_cons, List.nil_append, List.append_nil] at ha
                                                     exact noObj_mem_single ha trivial)
                                                  | cases hc))
                                      | cases hc
                                · simp only [mopResult, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
                                    h13, List.mem_cons, List.not_mem_nil, or_false, Pending.normal.injEq] at hc
                                  rcases hc with rfl | hc <;>
                                    first
                                      | (simp only [complPayload, List.filterMap_nil, List.filterMap_cons, List.flatten_nil, List.flatten_cons, List.nil_append, List.append_nil] at ha
                                         exact anyT_noObj a ha)
                                      | cases hc
  | throw =>
      simp [complPayload] at ha

theorem mopPayload_noObj (nm : «String») : ∀ a ∈ mopPayload nm, atomNoObj a := by
  intro a ha
  simp only [mopPayload, complPayload, List.mem_flatten, List.mem_filterMap] at ha
  obtain ⟨u, hu, hau⟩ := ha
  obtain ⟨c, hc, hcu⟩ := hu
  cases c with
  | normal t =>
      obtain rfl := Option.some.inj hcu
      have hpleq : complPayload [Pending.normal t] = t := by
        simp [complPayload]
      exact mopResult_noObj_t nm (.normal t) hc a (by rw [hpleq]; exact hau)
  | throw => simp at hcu


def etaSwap (η' : HeapCallableTy) (w : World) : World := { w with η := η' }

def resEta (η' : HeapCallableTy) : TCResult → TCResult
  | .flows fb => .flows { fb with falls := fb.falls.map (etaSwap η') }
  | .reject st why => .reject st why

theorem resEta_merge (η' : HeapCallableTy) (a b : TCResult) :
    resEta η' (mergeTC a b) = mergeTC (resEta η' a) (resEta η' b) := by
  cases a with
  | reject s w => rfl
  | flows fa =>
      cases b with
      | reject s w => rfl
      | flows fb =>
          simp only [resEta, mergeTC]
          rw [List.map_append]

theorem resEta_noFlows (η' : HeapCallableTy) : resEta η' noFlows = noFlows := rfl

theorem resEta_terminal {η' : HeapCallableTy} {fb : Flows} :
    (terminal { fb with falls := fb.falls.map (etaSwap η') } : Bool)
      = terminal fb := by
  simp only [terminal, List.isEmpty_map]

theorem foldl_resEta (η' : HeapCallableTy) (k' k : World → TCResult) :
    ∀ (ws : Worlds) (acc acc' : TCResult),
      acc' = resEta η' acc → (∀ u ∈ ws, k' u = resEta η' (k u)) →
        ws.foldl (fun a u => mergeTC a (k' u)) acc'
          = resEta η' (ws.foldl (fun a u => mergeTC a (k u)) acc) := by
  intro ws
  induction ws with
  | nil => intro acc acc' hac _; simp only [List.foldl_nil]; rw [hac]
  | cons u ws ih =>
      intro acc acc' hac h
      simp only [List.foldl_cons]
      rw [h u (by simp)]
      refine ih (mergeTC acc (k u)) (mergeTC acc' (resEta η' (k u))) ?_
        (fun v hv => h v (by simp [hv]))
      rw [resEta_merge, hac]

theorem forkTC_resEta (η' : HeapCallableTy) (site : Instr) (ws : Worlds)
    (k' k : World → TCResult)
    (h : ∀ u ∈ ws, k' u = resEta η' (k u)) :
    forkTC site ws k' = resEta η' (forkTC site ws k) := by
  cases ws with
  | nil => rfl
  | cons u ws =>
      simp only [forkTC, List.foldl_cons, List.foldl_nil]
      rw [h u (by simp)]
      rw [foldl_resEta _ _ _ ws (mergeTC noFlows (k u))
        (mergeTC noFlows (resEta η' (k u)))
        (by rw [resEta_merge, resEta_noFlows]) (fun v hv => h v (by simp [hv]))]

theorem step1_eta (sigs : SigTable) (i : Instr) (η' : HeapCallableTy) (w : World) :
    step1 sigs i (etaSwap η' w) = (step1 sigs i w).map (List.map (etaSwap η')) := by
  obtain ⟨wη, wΓ, ws⟩ := w
  cases i with
  | kEval e => rfl
  | kPrim1 p =>
      cases p with
      | pWrapC =>
          cases ws with
          | nil => rfl
          | cons t σ' =>
              cases h : complOnly t with
              | false =>
                  cases h2 : bareSlot t with
                  | none => simp [step1, etaSwap, h, h2]
                  | some x => simp [step1, etaSwap, h, h2, Option.map]
              | true => simp [step1, etaSwap, h, Option.map]
      | pThrowC =>
          cases ws with
          | nil => rfl
          | cons t σ' => simp [step1, etaSwap, Option.map]
      | pUnwrapC | pIsNormalC | pIsThrowC | pIsCompletion | pPred f b => rfl
      | pIsObj =>
          cases hpt : primTys Prim.pIsObj with
          | none => simp [primTys] at hpt
          | some tt =>
              obtain ⟨tin, tout⟩ := tt
              cases h : popTy anyT ws with
              | none => simp [step1, etaSwap, primTys, hpt, h]
              | some σ'' => simp [step1, etaSwap, primTys, hpt, h, Option.map]
      | pIsNotObj =>
          cases hpt : primTys Prim.pIsNotObj with
          | none => simp [primTys] at hpt
          | some tt =>
              obtain ⟨tin, tout⟩ := tt
              cases h : popTy anyT ws with
              | none => simp [step1, etaSwap, primTys, hpt, h]
              | some σ'' => simp [step1, etaSwap, primTys, hpt, h, Option.map]
      | pIsNotU =>
          cases hpt : primTys Prim.pIsNotU with
          | none => simp [primTys] at hpt
          | some tt =>
              obtain ⟨tin, tout⟩ := tt
              cases h : popTy anyT ws with
              | none => simp [step1, etaSwap, primTys, hpt, h]
              | some σ'' => simp [step1, etaSwap, primTys, hpt, h, Option.map]
      | pHasCall =>
          cases hpt : primTys Prim.pHasCall with
          | none => simp [primTys] at hpt
          | some tt =>
              obtain ⟨tin, tout⟩ := tt
              cases h : popTy anyT ws with
              | none => simp [step1, etaSwap, primTys, hpt, h]
              | some σ'' => simp [step1, etaSwap, primTys, hpt, h, Option.map]
      | pHasCtor =>
          cases hpt : primTys Prim.pHasCtor with
          | none => simp [primTys] at hpt
          | some tt =>
              obtain ⟨tin, tout⟩ := tt
              cases h : popTy anyT ws with
              | none => simp [step1, etaSwap, primTys, hpt, h]
              | some σ'' => simp [step1, etaSwap, primTys, hpt, h, Option.map]
      | pIsU =>
          cases hpt : primTys Prim.pIsU with
          | none => simp [primTys] at hpt
          | some tt =>
              obtain ⟨tin, tout⟩ := tt
              cases h : popTy anyT ws with
              | none => simp [step1, etaSwap, primTys, hpt, h]
              | some σ'' => simp [step1, etaSwap, primTys, hpt, h, Option.map]
      | pIsTrue =>
          cases hpt : primTys Prim.pIsTrue with
          | none => simp [primTys] at hpt
          | some tt =>
              obtain ⟨tin, tout⟩ := tt
              cases h : popTy anyT ws with
              | none => simp [step1, etaSwap, primTys, hpt, h]
              | some σ'' => simp [step1, etaSwap, primTys, hpt, h, Option.map]
      | pIsFalse =>
          cases hpt : primTys Prim.pIsFalse with
          | none => simp [primTys] at hpt
          | some tt =>
              obtain ⟨tin, tout⟩ := tt
              cases h : popTy anyT ws with
              | none => simp [step1, etaSwap, primTys, hpt, h]
              | some σ'' => simp [step1, etaSwap, primTys, hpt, h, Option.map]
      | pNullOrUnd =>
          cases hpt : primTys Prim.pNullOrUnd with
          | none => simp [primTys] at hpt
          | some tt =>
              obtain ⟨tin, tout⟩ := tt
              cases h : popTy anyT ws with
              | none => simp [step1, etaSwap, primTys, hpt, h]
              | some σ'' => simp [step1, etaSwap, primTys, hpt, h, Option.map]
      | pIsNull =>
          cases hpt : primTys Prim.pIsNull with
          | none => simp [primTys] at hpt
          | some tt =>
              obtain ⟨tin, tout⟩ := tt
              cases h : popTy anyT ws with
              | none => simp [step1, etaSwap, primTys, hpt, h]
              | some σ'' => simp [step1, etaSwap, primTys, hpt, h, Option.map]
      | pIsType ty =>
          cases hpt : primTys (Prim.pIsType ty) with
          | none => simp [primTys] at hpt
          | some tt =>
              obtain ⟨tin, tout⟩ := tt
              cases h : popTy anyT ws with
              | none => simp [step1, etaSwap, primTys, hpt, h]
              | some σ'' => simp [step1, etaSwap, primTys, hpt, h, Option.map]
      | pHasField nm2 =>
          cases hpt : primTys (Prim.pHasField nm2) with
          | none => simp [primTys] at hpt
          | some tt =>
              obtain ⟨tin, tout⟩ := tt
              cases h : popTy anyT ws with
              | none => simp [step1, etaSwap, primTys, hpt, h]
              | some σ'' => simp [step1, etaSwap, primTys, hpt, h, Option.map]
      | pIsStr sv =>
          cases hpt : primTys (Prim.pIsStr sv) with
          | none => simp [primTys] at hpt
          | some tt =>
              obtain ⟨tin, tout⟩ := tt
              cases h : popTy anyT ws with
              | none => simp [step1, etaSwap, primTys, hpt, h]
              | some σ'' => simp [step1, etaSwap, primTys, hpt, h, Option.map]
      | pDescField nm2 =>
          cases hpt : primTys (Prim.pDescField nm2) with
          | none => simp [primTys] at hpt
          | some tt =>
              obtain ⟨tin, tout⟩ := tt
              cases h : popTy anyT ws with
              | none => simp [step1, etaSwap, primTys, hpt, h]
              | some σ'' => simp [step1, etaSwap, primTys, hpt, h, Option.map]
  | kCall f n =>
      cases hf : sigFind sigs f with
      | none => simp [step1, etaSwap, hf]
      | some pr =>
          obtain ⟨ps, retj⟩ := pr
          cases hb : ((ps.length == n) || (ps.length == n + 1)) with
          | false => simp [step1, etaSwap, hf, hb]
          | true =>
              cases h : popArgs
                  (if ps.length = n then ps else ps.take n) ws with
              | false => simp [step1, etaSwap, hf, hb, h]
              | true => simp [step1, etaSwap, hf, hb, h, Option.map]
  | kSet x =>
      cases ws with
      | nil => simp [step1, etaSwap]
      | cons t σ' => simp [step1, etaSwap, Option.map]
  | kPop =>
      cases ws with
      | nil => simp [step1, etaSwap]
      | cons t σ' => simp [step1, etaSwap, Option.map]
  | kTest =>
      cases ws with
      | nil => simp [step1, etaSwap]
      | cons t σ' =>
          cases h : complOnly t with
          | false => simp [step1, etaSwap, h]
          | true =>
              cases hn : complNormals t with
              | nil =>
                  cases ht : complHasThrow t with
                  | false => simp [step1, etaSwap, h, hn, ht]
                  | true =>
                      simp [step1, etaSwap, h, hn, ht, Option.map, List.map]
              | cons n ns =>
                  cases ht : complHasThrow t with
                  | false =>
                      simp only [step1, etaSwap]
                      rw [hn]
                      simp [h, ht, Option.map, List.map, etaSwap]
                  | true =>
                      simp [step1, etaSwap, h, hn, ht, Option.map, List.map]
  | kUnwrap =>
      cases ws with
      | nil => simp [step1, etaSwap]
      | cons t σ' =>
          cases h : unwrapSlot t with
          | none => simp [step1, etaSwap, h]
          | some ps => simp [step1, etaSwap, h, Option.map]
  | kIMeth nm n =>
      cases hb : mopArity nm == some n with
      | false => simp [step1, etaSwap, hb]
      | true =>
          cases h1 : popTyN n anyT ws with
          | none => simp [step1, etaSwap, hb, h1]
          | some σ' =>
              cases h2 : popAObj σ' with
              | none => simp [step1, etaSwap, hb, h1, h2]
              | some σ'' =>
                  simp [step1, etaSwap, hb, h1, h2, Option.map]
  | kMkList n =>
      cases h : popTyN n anyT ws with
      | none => simp [step1, etaSwap, h]
      | some σ' => simp [step1, etaSwap, h, Option.map]
  | kNewSlot sn =>
      cases hsn : slotOfName sn with
      | none => simp [step1, etaSwap, hsn]
      | some ord =>
          cases h : popTy anyT ws with
          | none => simp [step1, etaSwap, hsn, h]
          | some σ' => simp [step1, etaSwap, hsn, h, Option.map]
  | kTestVar x p | kRet | kIte t e | kAssert | kRepeatWhile c body
  | kRepeatTest c body | kForStart x body | kForBody x vs body =>
      simp [step1, etaSwap, Option.map]

def extendCallableTy (η : HeapCallableTy) (nl : Nat) :
    HeapCallableTy := fun l => if l = nl then Bool.false else η l

theorem extendCallableTy_ne {η : HeapCallableTy} {nl l : Nat}
    (hne : l ≠ nl) : extendCallableTy η nl l = η l := by
  simp only [extendCallableTy, if_neg hne]

theorem normalizeAtom_extend_ne {η : HeapCallableTy} {nl : Nat}
    {v : JSValue} (hv : ∀ l ∈ locsOf v, l ≠ nl) :
    normalizeAtom η (typeOfV v)
      = normalizeAtom (extendCallableTy η nl) (typeOfV v) := by
  cases v with
  | obj loc =>
      simp only [normalizeAtom, typeOfV, extendCallableTy_ne (hv loc (by simp [locsOf]))]
  | compl abrupt w =>
      cases abrupt with
      | false =>
          simpa [normalizeAtom, typeOfV, locsOf_compl] using
            normalizeAtom_extend_ne (η := η) (nl := nl)
              (fun l hl => hv l (by simp [locsOf_compl]; exact hl))
      | true => rfl
  | undefined | null | boolean _ | number _ | str _
    | listV _ | descV _ => rfl

theorem heapOk_frameLocs_lt {heap : Heap} {nl : Nat} :
    ∀ (fs : List Fr), heapOk heap nl fs →
      ∀ f ∈ fs, ∀ l ∈ frameLocs f, l < nl := by
  intro fs
  induction fs with
  | nil => intro _ f hf; cases hf
  | cons f fs ih =>
      intro h g hg l hl
      by_cases hfg : g = f
      · subst hfg
        exact (h.1 l hl).1
      · exact ih h.2 g
          ((List.mem_cons.mp hg).resolve_left hfg) l hl

theorem extendCallableTy_self {η : HeapCallableTy} {nl : Nat}
    (hnl : η nl = Bool.false) : extendCallableTy η nl = η := by
  funext l
  by_cases hln : l = nl
  · subst hln
    simp [extendCallableTy, hnl]
  · simp only [extendCallableTy, if_neg hln]

theorem heapOk_fresh {heap : Heap} {nl : Nat} :
    ∀ (fs : List Fr), heapOk heap nl fs → ∀ l, nl ≤ l → heap l = none := by
  intro fs
  induction fs with
  | nil => intro h l hl; exact h.2 l hl
  | cons f fs ih => intro h l hl; exact ih h.2 l hl

theorem SR_kNewSlot (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (sn : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kNewSlot sn) s r := by
  intro _ _ hsc hpre
  cases s with
  | fdone => exact ⟨η, hpre⟩
  | fell => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre
          cases hsn : slotOfName sn with
          | none =>
              exfalso
              have h1 : frameTyped sigs η (sigRetTy sigs ret)
                  ⟨.kNewSlot sn :: stmts, env, eval, ret⟩ :=
                hpre.2.2.2.1.1
              rw [frameTyped_kNewSlot_reject hsn] at h1
              exact h1.elim
          | some ord =>
              cases eval with
              | nil =>
                  exfalso
                  have h1 : frameTyped sigs η (sigRetTy sigs ret)
                      ⟨.kNewSlot sn :: stmts, env, [], ret⟩ :=
                    hpre.2.2.2.1.1
                  simp only [frameTyped, frameWorld, List.map_nil, checkSeq,
                    step1, hsn, popTy] at h1
              | cons v eval' =>
                  simp only [withHead] at ⊢
                  simp only [fstep, hsn, objWith, stateTyped,
                    framesTypedFrom] at ⊢
                  have hobjrefs :
                      objRefs { objWith Kind.ordinary none with
                          slots := [(ord, v)] } = [] := rfl
                  have hfresh := heapOk_fresh _ hpre.2.1 nl (Nat.le_refl nl)
                  have hηnl : η nl = Bool.false := by
                    rw [hpre.1 nl]
                    simp [runtimeCallable, hfresh]
                  have hηext : extendCallableTy η nl = η :=
                    extendCallableTy_self hηnl
                  have hcall :=
                    heapCallabilityOk_heapSet (heap := heap) (nl := nl)
                      (o := { objWith Kind.ordinary none with
                          slots := [(ord, v)] })
                      rfl η hpre.1
                  have hcall' : heapCallabilityOk
                      (heapSet heap nl
                        { objWith Kind.ordinary none with slots := [(ord, v)] })
                      η := by
                    rw [← hηext]
                    exact hcall
                  have hheap :=
                    heapOk_heapSet_succ (heap := heap) (nl := nl)
                      (o := { objWith Kind.ordinary none with
                          slots := [(ord, v)] })
                      hobjrefs _ hpre.2.1
                  have houtheap :
                      heapOk (heapSet heap nl
                          { objWith Kind.ordinary none with slots := [(ord, v)] })
                        (nl + 1)
                        (⟨stmts, env, .obj nl :: eval', ret⟩ :: fs') :=
                    heapOk_cons_intro
                      (f := ⟨stmts, env, .obj nl :: eval', ret⟩) (by
                        intro l hl
                        rcases mem_frameLocs_cons_eval
                          (v := .obj nl) (eval := eval') (env := env) hl with
                          hloc | hrest
                        · have heq : l = nl := by
                            simpa [locsOf] using hloc
                          rw [heq]
                          exact ⟨Nat.lt_succ_self nl, by
                            rw [heapSet_get_self heap nl
                              { objWith Kind.ordinary none with
                                slots := [(ord, v)] }]
                            rfl⟩
                        · obtain ⟨hlt, hsome⟩ := hpre.2.1.1 l (by
                            show l ∈ (locsOf v
                              ++ List.flatMap locsOf eval')
                              ++ List.flatMap locsOf (List.map Prod.snd env)
                            rcases List.mem_append.mp hrest with he | henv
                            · exact List.mem_append.mpr
                                (Or.inl (List.mem_append.mpr (Or.inr he)))
                            · exact List.mem_append.mpr (Or.inr henv))
                          exact ⟨Nat.lt_succ_of_lt hlt, by
                            rw [heapSet_get_ne (Nat.ne_of_lt hlt)]
                            exact hsome⟩)
                      hheap.2
                  have hwfbase :=
                    framesWf_heapSet_succ (heap := heap) (nl := nl)
                      (o := { objWith Kind.ordinary none with
                          slots := [(ord, v)] })
                      _ hpre.2.2.1
                  have houtwf :
                      framesWf (heapSet heap nl
                          { objWith Kind.ordinary none with slots := [(ord, v)] })
                        (nl + 1)
                        (⟨stmts, env, .obj nl :: eval', ret⟩ :: fs') :=
                    ⟨instrsWf_heapSet_succ _
                        (instrsWf_tail hpre.2.2.1.1), hwfbase.2⟩
                  refine ⟨η, hcall', houtheap, houtwf,
                    ⟨frameTyped_kNewSlot (ord := ord) hsc hsn
                       hpre.2.2.2.1.1,
                      hpre.2.2.2.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2.2.2.2

theorem checkSeq_kPrim1_bool {sigs : SigTable} {r : Ty} {p : Prim}
    {Γ : TyEnv} {σ' : List Ty} {rest : List Instr} {v : JSValue}
    (hp : primTys p = some (anyT, [.anyValue .bool]))
    (htop : tmoves [normalizeAtom η (typeOfV v)] anyT = Bool.true) :
    checkSeq sigs r { η := η, Γ := Γ, σ := [normalizeAtom η (typeOfV v)] :: σ' } (.kPrim1 p :: rest)
      = checkSeq sigs r { η := η, Γ := Γ, σ := [.anyValue .bool] :: σ' } rest := by
  have htop' : tmoves [normalizeAtom η (typeOfV v)]
      (.anyValue .undef :: .anyValue .null :: .anyValue .bool :: .anyValue .num
        :: .anyValue .str :: (List.map VTy.anyValue objTags
          ++ [.anyValue .list, .anyValue .desc])) = Bool.true := by
    simpa [anyT, anyTags, langTags, anyOf] using htop
  cases p <;> simp [checkSeq, step1, primTys, popTy, htop', forkTC, List.foldl,
    mergeTC_noFlows, anyT, anyTags, langTags, anyOf] at hp ⊢

theorem tyLe_typeOfV_anyT_of_not_compl {v : JSValue}
    (hv : ¬ ∃ b w, v = JSValue.compl b w) :
    tyLe [normalizeAtom η (typeOfV v)] anyT := by
  apply tyLe_of_atom_cov
  intro a' ha'
  simp only [List.mem_singleton] at ha'
  subst a'
  cases v with
  | compl b w => exact False.elim (hv ⟨b, w, rfl⟩)
  | undefined =>
      exact ⟨.anyValue .undef, by simp [anyT, anyTags, langTags, anyOf], by simp [typeOfV, tmovesV, tagOf, normalizeAtom]⟩
  | null =>
      exact ⟨.anyValue .null, by simp [anyT, anyTags, langTags, anyOf], by simp [typeOfV, tmovesV, tagOf, normalizeAtom]⟩
  | boolean b =>
      exact ⟨.anyValue .bool, by simp [anyT, anyTags, langTags, anyOf], by simp [typeOfV, tmovesV, tagOf, normalizeAtom]⟩
  | number n =>
      exact ⟨.anyValue .num, by simp [anyT, anyTags, langTags, anyOf], by simp [typeOfV, tmovesV, tagOf, normalizeAtom]⟩
  | str s =>
      exact ⟨.anyValue .str, by simp [anyT, anyTags, langTags, anyOf], by simp [typeOfV, tmovesV, tagOf, normalizeAtom]⟩
  | obj a =>
      refine ⟨.anyValue (.obj (η a)), ?_, by simp [typeOfV, tmovesV, tagOf, normalizeAtom]⟩
      cases hη : η a <;> simp [anyT, anyTags, langTags, anyOf, objTags, hη]
  | listV xs =>
      exact ⟨.anyValue .list, by simp [anyT, anyTags, langTags, anyOf], by simp [typeOfV, tmovesV, tagOf, normalizeAtom]⟩
  | descV d =>
      exact ⟨.anyValue .desc, by simp [anyT, anyTags, langTags, anyOf], by simp [typeOfV, tmovesV, normalizeAtom]⟩

theorem typeOfV_le_anyT_of_not_compl {v : JSValue}
    (hv : ¬ ∃ b w, v = JSValue.compl b w) :
    tmoves [normalizeAtom η (typeOfV v)] anyT = Bool.true :=
  tyLe_typeOfV_anyT_of_not_compl hv

theorem slotLe_bool_result (η : HeapCallableTy) (b : Bool) :
    slotLe [normalizeAtom η (typeOfV (JSValue.boolean b))] [.anyValue .bool] := by
  constructor
  · apply tyLe_of_atom_cov
    intro a' ha'
    simp only [List.mem_singleton] at ha'
    subst a'
    refine ⟨.anyValue .bool, by simp, ?_⟩
    cases b <;> simp [typeOfV, tmovesV, tagOf, normalizeAtom]
  · simp

theorem frameTyped_prim_bool_bare {sigs : SigTable} {r : Ty} {p : Prim}
    {v : JSValue} {b : Bool} {rest : List Instr}
    {env : Env} {eval' : List JSValue} {ret : «String»}
    (hp : primTys p = some (anyT, [.anyValue .bool]))
    (hsc : sigParamsClosed sigs)
    (hv : ¬ ∃ c w, v = JSValue.compl c w)
    (h : frameTyped sigs η r ⟨.kPrim1 p :: rest, env, v :: eval', ret⟩) :
    frameTyped sigs η r ⟨rest, env, JSValue.boolean b :: eval', ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  rw [checkSeq_kPrim1_bool hp (typeOfV_le_anyT_of_not_compl hv)] at h
  exact frameTyped_pushRefine (ret := ret) hsc (T := [.anyValue .bool])
    (slotLe_bool_result η b)
    (atomCov_single atomCov_boolSing_class) h

theorem frameTyped_prim_bool_reject_compl {sigs : SigTable} {r : Ty} {p : Prim}
    {rest : List Instr} {env : Env} {eval' : List JSValue} {ret : «String»}
    (hp : primTys p = some (anyT, [.anyValue .bool])) (b : Bool) (v : JSValue) :
    frameTyped sigs η r ⟨.kPrim1 p :: rest, env, .compl b v :: eval', ret⟩ = False := by
  cases b <;> cases p <;>
    simp [frameTyped, frameWorld, checkSeq, step1, primTys, popTy, anyT, anyTags,
      langTags, anyOf, tmoves, tmovesV, typeOfV, normalizeAtom] at hp ⊢

theorem applyPrim_bool_of_primTys_bool (p : Prim)
    (hp : primTys p = some (anyT, [.anyValue .bool])) :
    ∀ (heap : Heap) (v : JSValue), ∃ b, applyPrim heap p v = JSValue.boolean b := by
  cases p <;> simp [primTys, applyPrim, anyT, anyTags, langTags, anyOf] at hp ⊢

theorem SR_kPrim1_bool (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy) (p : Prim)
    (s : FM) (r : Ty)
    (hp : primTys p = some (anyT, [.anyValue .bool])) :
    SR_arm sigs reg η (.kPrim1 p) s r := by
  intro _ _ hsc hpre
  cases s with
  | fdone v fs heap nl n => exact ⟨η, hpre⟩
  | fell fs heap nl n => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases eval with
          | nil =>
              exfalso
              have h1 : frameTyped sigs η (sigRetTy sigs ret)
                  ⟨.kPrim1 p :: stmts, env, [], ret⟩ := hpre.2.2.2.1.1
              cases p <;> simp [primTys] at hp <;>
                simp [frameTyped, frameWorld, checkSeq, step1, primTys, popTy,
                  anyT, anyTags, langTags, anyOf] at h1
          | cons v eval' =>
              by_cases hv : ∃ c w, v = JSValue.compl c w
              · rcases hv with ⟨c, w, rfl⟩
                exfalso
                have h1 : frameTyped sigs η (sigRetTy sigs ret)
                    ⟨.kPrim1 p :: stmts, env, .compl c w :: eval', ret⟩ := hpre.2.2.2.1.1
                rw [frameTyped_prim_bool_reject_compl (p := p) hp] at h1
                exact h1.elim
              · obtain ⟨b, hb⟩ := applyPrim_bool_of_primTys_bool p hp heap v
                simp only [fstep] at ⊢
                rw [hb]
                obtain ⟨hhk, hwf⟩ := heapOk_framesWf_pushempty
                  (i := .kPrim1 p) (w := v) (v' := .boolean b)
                  (by simp [locsOf]) hpre.2.1 hpre.2.2.1
                refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_prim_bool_bare (p := p) hp (b := b) hsc hv hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
                · rw [machineRet_head_swap]
                  exact hpre.2.2.2.2

theorem frameTyped_kEval_fused {sigs : SigTable} {r : Ty} {e : Expr}
    {x : «String»} {p : Prim} {rest : List Instr} {env : Env}
    {eval : List JSValue} {ret : «String»}
    (hchk : checkSeq sigs r
      { η := η, Γ := envTyOf η env, σ := eval.map (fun v => [normalizeAtom η (typeOfV v)]) }
      (.kEval e :: rest)
      = checkSeq sigs r
        { η := η, Γ := envTyOf η env, σ := eval.map (fun v => [normalizeAtom η (typeOfV v)]) }
        (.kTestVar x p :: rest))
    (h : frameTyped sigs η r ⟨.kEval e :: rest, env, eval, ret⟩) :
    frameTyped sigs η r ⟨.kTestVar x p :: rest, env, eval, ret⟩ := by
  simp only [frameTyped, frameWorld] at h ⊢
  rw [hchk] at h
  exact h

theorem SR_kEval_isObject_nv (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kEval (.isObject (.nv x))) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact ⟨η, hpre⟩
  | fell => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          simp only [fstep] at ⊢
          obtain ⟨hhk, hwf⟩ := heapOk_framesWf_stmts_swap
            (j := .kTestVar x .pIsObj) hpre.2.1 hpre.2.2.1
            ⟨instrWf_kTestVar, hpre.2.2.1.1.2⟩
          refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kEval_fused (x := x) (p := .pIsObj)
            (by simp [checkSeq]) hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2.2.2.2

theorem SR_kEval_isNotObject_nv (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kEval (.isNotObject (.nv x))) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact ⟨η, hpre⟩
  | fell => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          simp only [fstep] at ⊢
          obtain ⟨hhk, hwf⟩ := heapOk_framesWf_stmts_swap
            (j := .kTestVar x .pIsNotObj) hpre.2.1 hpre.2.2.1
            ⟨instrWf_kTestVar, hpre.2.2.1.1.2⟩
          refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kEval_fused (x := x) (p := .pIsNotObj)
            (by simp [checkSeq]) hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2.2.2.2

theorem SR_kEval_isNotUndefined_nv (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kEval (.isNotUndefined (.nv x))) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact ⟨η, hpre⟩
  | fell => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          simp only [fstep] at ⊢
          obtain ⟨hhk, hwf⟩ := heapOk_framesWf_stmts_swap
            (j := .kTestVar x .pIsNotU) hpre.2.1 hpre.2.2.1
            ⟨instrWf_kTestVar, hpre.2.2.1.1.2⟩
          refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kEval_fused (x := x) (p := .pIsNotU)
            (by simp [checkSeq]) hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2.2.2.2

theorem SR_kEval_isU_nv (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kEval (.isU (.nv x))) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact ⟨η, hpre⟩
  | fell => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          simp only [fstep] at ⊢
          obtain ⟨hhk, hwf⟩ := heapOk_framesWf_stmts_swap
            (j := .kTestVar x .pIsU) hpre.2.1 hpre.2.2.1
            ⟨instrWf_kTestVar, hpre.2.2.1.1.2⟩
          refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kEval_fused (x := x) (p := .pIsU)
            (by simp [checkSeq]) hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2.2.2.2

theorem SR_kEval_hasCall_nv (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kEval (.hasCall (.nv x))) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact ⟨η, hpre⟩
  | fell => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          simp only [fstep] at ⊢
          obtain ⟨hhk, hwf⟩ := heapOk_framesWf_stmts_swap
            (j := .kTestVar x .pHasCall) hpre.2.1 hpre.2.2.1
            ⟨instrWf_kTestVar, hpre.2.2.1.1.2⟩
          refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kEval_fused (x := x) (p := .pHasCall)
            (by simp [checkSeq]) hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2.2.2.2

theorem SR_kEval_hasCtor_nv (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kEval (.hasCtor (.nv x))) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact ⟨η, hpre⟩
  | fell => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          simp only [fstep] at ⊢
          obtain ⟨hhk, hwf⟩ := heapOk_framesWf_stmts_swap
            (j := .kTestVar x .pHasCtor) hpre.2.1 hpre.2.2.1
            ⟨instrWf_kTestVar, hpre.2.2.1.1.2⟩
          refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kEval_fused (x := x) (p := .pHasCtor)
            (by simp [checkSeq]) hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2.2.2.2

theorem SR_kEval_isBoolVal_nv (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (b : Bool) (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kEval (.isBoolVal b (.nv x))) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact ⟨η, hpre⟩
  | fell => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          simp only [fstep] at ⊢
          obtain ⟨hhk, hwf⟩ := heapOk_framesWf_stmts_swap
            (j := .kTestVar x (if b then .pIsTrue else .pIsFalse))
            hpre.2.1 hpre.2.2.1 ⟨instrWf_kTestVar, hpre.2.2.1.1.2⟩
          refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kEval_fused (x := x)
            (p := if b then .pIsTrue else .pIsFalse)
            (by cases b <;> simp [checkSeq]) hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2.2.2.2

theorem SR_kEval_isStrVal_nv (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (sv : «String») (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kEval (.isStrVal sv (.nv x))) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact ⟨η, hpre⟩
  | fell => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          simp only [fstep] at ⊢
          obtain ⟨hhk, hwf⟩ := heapOk_framesWf_stmts_swap
            (j := .kTestVar x (.pIsStr sv)) hpre.2.1 hpre.2.2.1
            ⟨instrWf_kTestVar, hpre.2.2.1.1.2⟩
          refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kEval_fused (x := x) (p := .pIsStr sv)
            (by simp [checkSeq]) hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2.2.2.2

theorem SR_kEval_hasField_nv (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (nm : «String») (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kEval (.hasField nm (.nv x))) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact ⟨η, hpre⟩
  | fell => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          simp only [fstep] at ⊢
          obtain ⟨hhk, hwf⟩ := heapOk_framesWf_stmts_swap
            (j := .kTestVar x (.pHasField nm)) hpre.2.1 hpre.2.2.1
            ⟨instrWf_kTestVar, hpre.2.2.1.1.2⟩
          refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kEval_fused (x := x) (p := .pHasField nm)
            (by simp [checkSeq]) hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2.2.2.2

theorem SR_kEval_isNullOrUnd_nv (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kEval (.isNullOrUnd (.nv x))) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact ⟨η, hpre⟩
  | fell => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          simp only [fstep] at ⊢
          obtain ⟨hhk, hwf⟩ := heapOk_framesWf_stmts_swap
            (j := .kTestVar x .pNullOrUnd) hpre.2.1 hpre.2.2.1
            ⟨instrWf_kTestVar, hpre.2.2.1.1.2⟩
          refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kEval_fused (x := x) (p := .pNullOrUnd)
            (by simp [checkSeq]) hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2.2.2.2

theorem SR_kEval_isBoolVal_call_nv_fused (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (b : Bool) (f : «String») (x : «String») (s : FM) (r : Ty)
    (hf : fusedPred f = Bool.true) :
    SR_arm sigs reg η (.kEval (.isBoolVal b (.call f [.nv x]))) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact ⟨η, hpre⟩
  | fell => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f' fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f'
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          have hcond : ((f == "IsDataDescriptor" || f == "IsAccessorDescriptor")
              || f == "IsCallable") = Bool.true := hf
          simp only [fstep, hcond] at ⊢
          obtain ⟨hhk, hwf⟩ := heapOk_framesWf_stmts_swap
            (j := .kTestVar x (.pPred f b)) hpre.2.1 hpre.2.2.1
            ⟨instrWf_kTestVar, hpre.2.2.1.1.2⟩
          refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kEval_fused (x := x) (p := .pPred f b)
            (by simp [checkSeq, hf]) hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2.2.2.2

theorem split1_pIsObj_singleton {Γ : TyEnv} {x : «String»} {v : JSValue}
    {σ : List Ty}
    (hΓ : tyLookup Γ x = some [normalizeAtom η (typeOfV v)]) :
    split1 x objT { η := η, Γ := Γ, σ := σ }
      = [{ η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: Γ,
           σ := [.isValue (.boolean (isObjV v))] :: σ }] := by
  cases v with
  | compl b w =>
      cases b <;> cases w <;> simp [split1, hΓ, typeOfV, meetTy, meetAtom,
        removeTy, removeAtom, tmovesV, isObjV, tagOf, isBoolClass, isBoolSing, normalizeAtom, objT]
  | obj loc =>
      cases hnl : η loc <;>
        simp [split1, hΓ, typeOfV, meetTy, meetAtom, removeTy, removeAtom,
          objT, tmovesV, isObjV, tagOf, isBoolClass, isBoolSing, normalizeAtom, hnl]
  | undefined | null | boolean _ | number _ | str _ | listV _ | descV _ =>
      simp [split1, hΓ, typeOfV, meetTy, meetAtom, removeTy, removeAtom, objT,
        tmovesV, isObjV, tagOf, isBoolClass, isBoolSing, normalizeAtom]

theorem frameTyped_kTestVar_pIsObj_present {sigs : SigTable} {r : Ty}
    {x : «String»} {v : JSValue} {rest : List Instr} {env : Env}
    {eval : List JSValue} {ret : «String»} {hsc : sigParamsClosed sigs}
    (hΓ : tyLookup (envTyOf η env) x = some [normalizeAtom η (typeOfV v)])
    (h : frameTyped sigs η r ⟨.kTestVar x .pIsObj :: rest, env, eval, ret⟩) :
    frameTyped sigs η r ⟨rest, env, .boolean (isObjV v) :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  simp only [checkSeq, testTypeP, split1_pIsObj_singleton hΓ, forkTC, List.foldl,
    mergeTC_noFlows] at h
  have hres : ∃ fb, checkSeq sigs r
      { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: envTyOf η env,
        σ := [.isValue (.boolean (isObjV v))] :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
      rest = TCResult.flows fb ∧ terminal fb = Bool.true := by
    cases hres : checkSeq sigs r
        { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: envTyOf η env,
          σ := [.isValue (.boolean (isObjV v))] :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
        rest with
    | flows fb => exact ⟨fb, rfl, by rw [hres] at h; exact h⟩
    | reject s why => rw [hres] at h; exact h.elim
  obtain ⟨fb, hchk, hterm⟩ := hres
  have hle : worldLe
      { η := η, Γ := envTyOf η env,
        σ := [normalizeAtom η (typeOfV (JSValue.boolean (isObjV v)))] :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
      { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: envTyOf η env,
        σ := [.isValue (.boolean (isObjV v))] :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) } :=
    ⟨rfl, envLe_shadow_same hΓ,
      stackLe_cons_intro (slotLe_refl _) (stackLe_refl _),
      envCov_shadow_same hΓ,
      stackCov_cons_intro (tyCov_refl _ _) (stackCov_refl _ _)⟩
  obtain ⟨fb', hchk', hterm'⟩ :=
    checkSeq_specialize_terminal sigs r _ _ rest hsc hle hchk hterm
  rw [hchk']
  exact hterm'

theorem frameTyped_kTestVar_pIsObj_reject_unbound {sigs : SigTable} {r : Ty}
    {x : «String»} {rest : List Instr} {env : Env} {eval : List JSValue}
    {ret : «String»}
    (hΓ : tyLookup (envTyOf η env) x = none) :
    frameTyped sigs η r ⟨.kTestVar x .pIsObj :: rest, env, eval, ret⟩ = False := by
  simp [frameTyped, frameWorld, checkSeq, testTypeP, split1, hΓ, forkTC]

theorem SR_kTestVar_pIsObj (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kTestVar x .pIsObj) s r := by
  intro _ _ hsc hpre
  cases s with
  | fdone => exact ⟨η, hpre⟩
  | fell => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases hl : lookup env x with
          | none =>
              have hΓ : tyLookup (envTyOf η env) x = none := by
                have hbridge := envTyOf_lookup η env x
                simp only [hl, Option.map_none] at hbridge
                exact hbridge.symm
              have h1 : frameTyped sigs η (sigRetTy sigs ret)
                  ⟨.kTestVar x .pIsObj :: stmts, env, eval, ret⟩ := hpre.2.2.2.1.1
              rw [frameTyped_kTestVar_pIsObj_reject_unbound hΓ] at h1
              exact h1.elim
          | some v =>
              have hΓ : tyLookup (envTyOf η env) x = some [normalizeAtom η (typeOfV v)] := by
                have hbridge := envTyOf_lookup η env x
                simp only [hl, Option.map_some] at hbridge
                exact hbridge.symm
              simp only [fstep, hl] at ⊢
              obtain ⟨hhk, hwf⟩ := heapOk_framesWf_push_nolocs
                (i := .kTestVar x .pIsObj) (v := .boolean (isObjV v))
                (by simp [locsOf]) hpre.2.1 hpre.2.2.1
              refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kTestVar_pIsObj_present (hsc := hsc) hΓ
                  hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2.2.2.2

theorem frameTyped_kTestVar_shape_present {sigs : SigTable} {r : Ty}
    {p : Prim} {T : Ty} {f : JSValue → Bool} {x : «String»} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    {hsc : sigParamsClosed sigs}
    (hT : testTypeP p = some T)
    (hsplit : ∀ (Γ : TyEnv) (σ : List Ty), tyLookup Γ x = some [normalizeAtom η (typeOfV v)] →
      split1 x T { η := η, Γ := Γ, σ := σ }
        = [{ η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: Γ,
             σ := [.isValue (.boolean (f v))] :: σ }])
    (hΓ : tyLookup (envTyOf η env) x = some [normalizeAtom η (typeOfV v)])
    (h : frameTyped sigs η r ⟨.kTestVar x p :: rest, env, eval, ret⟩) :
    frameTyped sigs η r ⟨rest, env, .boolean (f v) :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  have hstep : checkSeq sigs r
      { η := η, Γ := envTyOf η env, σ := eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
      (.kTestVar x p :: rest)
      = checkSeq sigs r
        { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: envTyOf η env,
          σ := [.isValue (.boolean (f v))] :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
        rest := by
    cases p <;> simp only [testTypeP] at hT <;> cases hT <;>
      simp [checkSeq, testTypeP, hsplit _ _ hΓ, forkTC, List.foldl,
        mergeTC_noFlows]
  rw [hstep] at h
  have hres : ∃ fb, checkSeq sigs r
      { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: envTyOf η env,
        σ := [.isValue (.boolean (f v))] :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
      rest = TCResult.flows fb ∧ terminal fb = Bool.true := by
    cases hres : checkSeq sigs r
        { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: envTyOf η env,
          σ := [.isValue (.boolean (f v))] :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
        rest with
    | flows fb => exact ⟨fb, rfl, by rw [hres] at h; exact h⟩
    | reject s why => rw [hres] at h; exact h.elim
  obtain ⟨fb, hchk, hterm⟩ := hres
  have hle : worldLe
      { η := η, Γ := envTyOf η env,
        σ := [normalizeAtom η (typeOfV (JSValue.boolean (f v)))] :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
      { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: envTyOf η env,
        σ := [.isValue (.boolean (f v))] :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) } :=
    ⟨rfl, envLe_shadow_same hΓ,
      stackLe_cons_intro (slotLe_refl _) (stackLe_refl _),
      envCov_shadow_same hΓ,
      stackCov_cons_intro (tyCov_refl _ _) (stackCov_refl _ _)⟩
  obtain ⟨fb', hchk', hterm'⟩ :=
    checkSeq_specialize_terminal sigs r _ _ rest hsc hle hchk hterm
  rw [hchk']
  exact hterm'

theorem frameTyped_kTestVar_shape_reject_unbound {sigs : SigTable} {r : Ty}
    {p : Prim} {T : Ty} {x : «String»} {rest : List Instr} {env : Env}
    {eval : List JSValue} {ret : «String»}
    (hT : testTypeP p = some T)
    (hΓ : tyLookup (envTyOf η env) x = none) :
    frameTyped sigs η r ⟨.kTestVar x p :: rest, env, eval, ret⟩ = False := by
  cases p <;> simp only [testTypeP] at hT <;> cases hT <;>
    simp [frameTyped, frameWorld, checkSeq, testTypeP, split1, hΓ, forkTC]

theorem SR_kTestVar_shape (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (p : Prim) (T : Ty) (f : JSValue → Bool) (x : «String») (s : FM) (r : Ty)
    (hT : testTypeP p = some T)
    (hsplit : ∀ (v : JSValue) (Γ : TyEnv) (σ : List Ty),
      tyLookup Γ x = some [normalizeAtom η (typeOfV v)] →
      split1 x T { η := η, Γ := Γ, σ := σ }
        = [{ η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: Γ,
             σ := [.isValue (.boolean (f v))] :: σ }])
    (hrun : ∀ (heap : Heap) (v : JSValue), applyPrim heap p v = JSValue.boolean (f v)) :
    SR_arm sigs reg η (.kTestVar x p) s r := by
  intro _ _ hsc hpre
  cases s with
  | fdone => exact ⟨η, hpre⟩
  | fell => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f' fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f'
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases hl : lookup env x with
          | none =>
              have hΓ : tyLookup (envTyOf η env) x = none := by
                have hbridge := envTyOf_lookup η env x
                simp only [hl, Option.map_none] at hbridge
                exact hbridge.symm
              have h1 : frameTyped sigs η (sigRetTy sigs ret)
                  ⟨.kTestVar x p :: stmts, env, eval, ret⟩ := hpre.2.2.2.1.1
              rw [frameTyped_kTestVar_shape_reject_unbound hT hΓ] at h1
              exact h1.elim
          | some v =>
              have hΓ : tyLookup (envTyOf η env) x = some [normalizeAtom η (typeOfV v)] := by
                have hbridge := envTyOf_lookup η env x
                simp only [hl, Option.map_some] at hbridge
                exact hbridge.symm
              simp only [fstep, hl] at ⊢
              rw [hrun heap v]
              obtain ⟨hhk, hwf⟩ := heapOk_framesWf_push_nolocs
                (i := .kTestVar x p) (v := .boolean (f v))
                (by simp [locsOf]) hpre.2.1 hpre.2.2.1
              refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kTestVar_shape_present (hsc := hsc) hT
                  (hsplit v) hΓ hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2.2.2.2

theorem SR_kTestVar_pIsU (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kTestVar x .pIsU) s r :=
  SR_kTestVar_shape sigs reg η .pIsU [.anyValue .undef] isUndV x s r
    (by simp [testTypeP])
    (fun v Γ σ hΓ => by
      cases v with
      | compl b w => cases b <;> simp [split1, hΓ, typeOfV, meetTy, meetAtom,
          removeTy, removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing, isUndV, normalizeAtom]
      | undefined | null | boolean _ | number _ | str _ | obj _ | listV _
        | descV _ =>
          simp [split1, hΓ, typeOfV, meetTy, meetAtom, removeTy, removeAtom,
            tmovesV, tagOf, isBoolClass, isBoolSing, isUndV, normalizeAtom])
    (by simp [applyPrim])

theorem SR_kTestVar_pIsNull (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kTestVar x .pIsNull) s r :=
  SR_kTestVar_shape sigs reg η .pIsNull [.anyValue .null] isNullV x s r
    (by simp [testTypeP])
    (fun v Γ σ hΓ => by
      cases v with
      | compl b w => cases b <;> simp [split1, hΓ, typeOfV, meetTy, meetAtom,
          removeTy, removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing, isNullV, normalizeAtom]
      | undefined | null | boolean _ | number _ | str _ | obj _ | listV _
        | descV _ =>
          simp [split1, hΓ, typeOfV, meetTy, meetAtom, removeTy, removeAtom,
            tmovesV, tagOf, isBoolClass, isBoolSing, isNullV, normalizeAtom])
    (by simp [applyPrim])

theorem SR_kTestVar_pNullOrUnd (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kTestVar x .pNullOrUnd) s r :=
  SR_kTestVar_shape sigs reg η .pNullOrUnd
    [.anyValue .undef, .anyValue .null]
    (fun v => isUndV v || isNullV v) x s r
    (by simp [testTypeP])
    (fun v Γ σ hΓ => by
      cases v with
      | compl b w => cases b <;> simp [split1, hΓ, typeOfV, meetTy, meetAtom,
          removeTy, removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing,
          isUndV, isNullV, normalizeAtom]
      | undefined | null | boolean _ | number _ | str _ | obj _ | listV _
        | descV _ =>
          simp [split1, hΓ, typeOfV, meetTy, meetAtom, removeTy, removeAtom,
            tmovesV, tagOf, isBoolClass, isBoolSing, isUndV, isNullV, normalizeAtom])
    (by simp [applyPrim])

theorem SR_kTestVar_pIsTrue (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kTestVar x .pIsTrue) s r :=
  SR_kTestVar_shape sigs reg η .pIsTrue [.isValue (.boolean Bool.true)]
    (fun v => v == JSValue.boolean Bool.true) x s r
    (by simp [testTypeP])
    (fun v Γ σ hΓ => by
      cases v with
      | compl b w => cases b <;> simp [split1, hΓ, typeOfV, meetTy, meetAtom,
          removeTy, removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing, normalizeAtom]
      | boolean b =>
          cases b <;> simp [split1, hΓ, typeOfV, meetTy, meetAtom, removeTy,
            removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing, normalizeAtom]
      | undefined | null | number _ | str _ | obj _ | listV _ | descV _ =>
          simp [split1, hΓ, typeOfV, meetTy, meetAtom, removeTy, removeAtom,
            tmovesV, tagOf, isBoolClass, isBoolSing, normalizeAtom])
    (by simp [applyPrim])

theorem SR_kTestVar_pIsFalse (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kTestVar x .pIsFalse) s r :=
  SR_kTestVar_shape sigs reg η .pIsFalse [.isValue (.boolean Bool.false)]
    (fun v => v == JSValue.boolean Bool.false) x s r
    (by simp [testTypeP])
    (fun v Γ σ hΓ => by
      cases v with
      | compl b w => cases b <;> simp [split1, hΓ, typeOfV, meetTy, meetAtom,
          removeTy, removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing, normalizeAtom]
      | boolean b =>
          cases b <;> simp [split1, hΓ, typeOfV, meetTy, meetAtom, removeTy,
            removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing, normalizeAtom]
      | undefined | null | number _ | str _ | obj _ | listV _ | descV _ =>
          simp [split1, hΓ, typeOfV, meetTy, meetAtom, removeTy, removeAtom,
            tmovesV, tagOf, isBoolClass, isBoolSing, normalizeAtom])
    (by simp [applyPrim])

theorem SR_kTestVar_pIsStr (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (sv : «String») (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kTestVar x (.pIsStr sv)) s r :=
  SR_kTestVar_shape sigs reg η (.pIsStr sv) [.isValue (.str sv)]
    (fun v => v == JSValue.str sv) x s r
    (by simp [testTypeP])
    (fun v Γ σ hΓ => by
      cases v with
      | compl b w => cases b <;> simp [split1, hΓ, typeOfV, meetTy, meetAtom,
          removeTy, removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing, normalizeAtom]
      | str y =>
          by_cases hy : y = sv <;>
            simp [split1, hΓ, typeOfV, meetTy, meetAtom, removeTy, removeAtom,
              tmovesV, tagOf, isBoolClass, isBoolSing, hy, normalizeAtom]
      | undefined | null | boolean _ | number _ | obj _ | listV _ | descV _ =>
          simp [split1, hΓ, typeOfV, meetTy, meetAtom, removeTy, removeAtom,
            tmovesV, tagOf, isBoolClass, isBoolSing, normalizeAtom])
    (by simp [applyPrim])

def isTypeResult (s : «String») (v : JSValue) : Bool :=
  if s = "Boolean" then
    match v with
    | .boolean _ => Bool.true
    | _ => Bool.false
  else if s = "Number" then
    match v with
    | .number _ => Bool.true
    | _ => Bool.false
  else if s = "String" then
    match v with
    | .str _ => Bool.true
    | _ => Bool.false
  else Bool.false

theorem split1_pIsType_singleton (s : «String») (v : JSValue)
    (Γ : TyEnv) (σ : List Ty) (x : «String»)
    (hΓ : tyLookup Γ x = some [normalizeAtom η (typeOfV v)]) :
    split1 x (typeMask s) { η := η, Γ := Γ, σ := σ }
      = [{ η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: Γ,
           σ := [.isValue (.boolean (isTypeResult s v))] :: σ }] := by
  by_cases h1 : s = "Boolean"
  · subst h1
    cases v with
    | compl b w => cases b <;> simp [split1, hΓ, typeOfV, typeMask, meetTy,
        meetAtom, removeTy, removeAtom, tmovesV, tagOf, isBoolClass,
        isBoolSing, isTypeResult, normalizeAtom]
    | undefined | null | number _ | str _ | obj _ | listV _ | descV _ =>
        simp [split1, hΓ, typeOfV, typeMask, meetTy, meetAtom, removeTy,
          removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing, isTypeResult, normalizeAtom]
    | boolean b =>
        cases b <;> simp [split1, hΓ, typeOfV, typeMask, meetTy, meetAtom,
          removeTy, removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing,
          isTypeResult, normalizeAtom]
  · by_cases h2 : s = "Number"
    · subst h2
      cases v with
      | compl b w => cases b <;> simp [split1, hΓ, typeOfV, typeMask, meetTy,
          meetAtom, removeTy, removeAtom, tmovesV, tagOf, isBoolClass,
          isBoolSing, isTypeResult, normalizeAtom]
      | undefined | null | boolean _ | str _ | obj _ | listV _ | descV _ =>
          simp [split1, hΓ, typeOfV, typeMask, meetTy, meetAtom, removeTy,
            removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing, isTypeResult, normalizeAtom]
      | number n =>
          simp [split1, hΓ, typeOfV, typeMask, meetTy, meetAtom, removeTy,
            removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing, isTypeResult, normalizeAtom]
    · by_cases h3 : s = "String"
      · subst h3
        cases v with
        | compl b w => cases b <;> simp [split1, hΓ, typeOfV, typeMask, meetTy,
            meetAtom, removeTy, removeAtom, tmovesV, tagOf, isBoolClass,
            isBoolSing, isTypeResult, normalizeAtom]
        | undefined | null | boolean _ | number _ | obj _ | listV _ | descV _ =>
            simp [split1, hΓ, typeOfV, typeMask, meetTy, meetAtom, removeTy,
              removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing, isTypeResult, normalizeAtom]
        | str y =>
            simp [split1, hΓ, typeOfV, typeMask, meetTy, meetAtom, removeTy,
              removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing, isTypeResult, normalizeAtom]
      · cases v with
        | compl b w => cases b <;>
            simp [split1, hΓ, typeOfV, typeMask, meetTy, meetAtom, removeTy,
              removeAtom, tagOf, isBoolClass, isTypeResult, h1, h2, h3, normalizeAtom]
        | undefined | null | boolean _ | number _ | str _ | obj _ | listV _
          | descV _ =>
            simp [split1, hΓ, typeOfV, typeMask, meetTy, meetAtom, removeTy,
              removeAtom, tagOf, isBoolClass, isTypeResult, h1, h2, h3, normalizeAtom]

theorem applyPrim_pIsType_eq (s : «String») (heap : Heap) (v : JSValue) :
    applyPrim heap (.pIsType s) v = .boolean (isTypeResult s v) := by
  simp only [applyPrim]
  split <;> simp_all [isTypeResult] <;> try rfl

theorem SR_kTestVar_pIsType (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (s : «String») (x : «String») (st : FM) (r : Ty) :
    SR_arm sigs reg η (.kTestVar x (.pIsType s)) st r :=
  SR_kTestVar_shape sigs reg η (.pIsType s) (typeMask s)
    (isTypeResult s) x st r
    (by simp [testTypeP])
    (fun v Γ σ hΓ => split1_pIsType_singleton s v Γ σ x hΓ)
    (applyPrim_pIsType_eq s)

def isCompletionResult (v : JSValue) : Bool :=
  match v with
  | .compl _ _ => Bool.true
  | _ => Bool.false

theorem applyPrim_pIsCompletion_eq (heap : Heap) (v : JSValue) :
    applyPrim heap .pIsCompletion v = .boolean (isCompletionResult v) := by
  cases v <;> simp [applyPrim, isCompletionResult]

theorem frameTyped_kTestVar_pIsCompletion_present {sigs : SigTable} {r : Ty}
    {x : «String»} {v : JSValue} {rest : List Instr} {env : Env}
    {eval : List JSValue} {ret : «String»} {hsc : sigParamsClosed sigs}
    (hΓ : tyLookup (envTyOf η env) x = some [normalizeAtom η (typeOfV v)])
    (h : frameTyped sigs η r ⟨.kTestVar x .pIsCompletion :: rest, env, eval, ret⟩) :
    frameTyped sigs η r ⟨rest, env, .boolean (isCompletionResult v) :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  simp only [checkSeq, testTypeP, hΓ] at h
  exact frameTyped_pushRefine (ret := ret) hsc (T := [.anyValue .bool])
    (slotLe_bool_result η _)
    (atomCov_single atomCov_boolSing_class) h

theorem frameTyped_kTestVar_pIsCompletion_reject_unbound {sigs : SigTable}
    {r : Ty} {x : «String»} {rest : List Instr} {env : Env}
    {eval : List JSValue} {ret : «String»}
    (hΓ : tyLookup (envTyOf η env) x = none) :
    frameTyped sigs η r ⟨.kTestVar x .pIsCompletion :: rest, env, eval, ret⟩
      = False := by
  simp [frameTyped, frameWorld, checkSeq, testTypeP, hΓ]

theorem SR_kTestVar_pIsCompletion (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kTestVar x .pIsCompletion) s r := by
  intro _ _ hsc hpre
  cases s with
  | fdone => exact ⟨η, hpre⟩
  | fell => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases hl : lookup env x with
          | none =>
              have hΓ : tyLookup (envTyOf η env) x = none := by
                have hbridge := envTyOf_lookup η env x
                simp only [hl, Option.map_none] at hbridge
                exact hbridge.symm
              have h1 : frameTyped sigs η (sigRetTy sigs ret)
                  ⟨.kTestVar x .pIsCompletion :: stmts, env, eval, ret⟩ :=
                hpre.2.2.2.1.1
              rw [frameTyped_kTestVar_pIsCompletion_reject_unbound hΓ] at h1
              exact h1.elim
          | some v =>
              have hΓ : tyLookup (envTyOf η env) x = some [normalizeAtom η (typeOfV v)] := by
                have hbridge := envTyOf_lookup η env x
                simp only [hl, Option.map_some] at hbridge
                exact hbridge.symm
              simp only [fstep, hl] at ⊢
              rw [applyPrim_pIsCompletion_eq heap v]
              obtain ⟨hhk, hwf⟩ := heapOk_framesWf_push_nolocs
                (i := .kTestVar x .pIsCompletion) (v := .boolean (isCompletionResult v))
                (by simp [locsOf]) hpre.2.1 hpre.2.2.1
              refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kTestVar_pIsCompletion_present (hsc := hsc) hΓ
                  hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2.2.2.2

def normalResult (v : JSValue) : Bool :=
  match v with
  | .compl Bool.false _ => Bool.true
  | _ => Bool.false

def normalDec : VTy → Bool :=
  fun a =>
    match a with
    | .complN _ => Bool.true
    | _ => Bool.false

theorem primDecide_pIsNormalC_eq :
    primDecide .pIsNormalC = some normalDec := rfl

theorem applyPrim_pIsNormalC_eq (heap : Heap) (v : JSValue) :
    applyPrim heap .pIsNormalC v = .boolean (normalResult v) := by
  cases v with
  | compl b w => cases b <;> simp [applyPrim, normalResult]
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _ | descV _ =>
      simp [applyPrim, normalResult]

theorem splitP1_pIsNormal_machine {Γ : TyEnv} {x : «String»} {v : JSValue}
    {σ : List Ty}
    (hΓ : tyLookup Γ x = some [normalizeAtom η (typeOfV v)]) :
    { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: Γ,
      σ := [.isValue (.boolean (normalResult v))] :: σ }
      ∈ splitP1 x normalDec { η := η, Γ := Γ, σ := σ } := by
  cases v with
  | compl b w =>
      cases b <;> simp [splitP1, splitP1At, hΓ, typeOfV, normalDec,
        normalResult, normalizeAtom]
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _
    | descV _ =>
      simp [splitP1, splitP1At, hΓ, typeOfV, normalDec, normalResult, normalizeAtom]

theorem frameTyped_kTestVar_pIsNormalC_present {sigs : SigTable} {r : Ty}
    {x : «String»} {v : JSValue} {rest : List Instr} {env : Env}
    {eval : List JSValue} {ret : «String»} {hsc : sigParamsClosed sigs}
    (hΓ : tyLookup (envTyOf η env) x = some [normalizeAtom η (typeOfV v)])
    (h : frameTyped sigs η r ⟨.kTestVar x .pIsNormalC :: rest, env, eval, ret⟩) :
    frameTyped sigs η r ⟨rest, env, .boolean (normalResult v) :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  simp only [checkSeq, primDecide_pIsNormalC_eq] at h
  have hmem := splitP1_pIsNormal_machine (Γ := envTyOf η env)
    (σ := eval.map (fun y => [normalizeAtom η (typeOfV y)])) hΓ
  have hne : splitP1 x normalDec
      { η := η, Γ := envTyOf η env, σ := eval.map (fun y => [normalizeAtom η (typeOfV y)]) } ≠ [] := by
    intro hnil
    rw [hnil] at hmem
    cases hmem
  cases hfork : forkTC (Instr.kTestVar x Prim.pIsNormalC)
      (splitP1 x normalDec
        { η := η, Γ := envTyOf η env, σ := eval.map (fun y => [normalizeAtom η (typeOfV y)]) })
      (fun u => checkSeq sigs r u rest) with
  | flows fb =>
      have hterm0 : terminal fb = Bool.true := by
        rw [hfork] at h; exact h
      cases hws : splitP1 x normalDec
          { η := η, Γ := envTyOf η env, σ := eval.map (fun y => [normalizeAtom η (typeOfV y)]) } with
      | nil => exact absurd hws hne
      | cons u0 us =>
          rw [hws] at hfork hmem
          have hfold : (u0 :: us).foldl
              (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows
            = TCResult.flows fb := by
            simpa [forkTC] using hfork
          obtain ⟨fbm, hchk⟩ :=
            fold_all_flows (J := fun u => checkSeq sigs r u rest) (u0 :: us) fb
              hfold
              { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: envTyOf η env,
                σ := [.isValue (.boolean (normalResult v))]
                  :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
              hmem
          have hfall : fbm.falls = [] :=
            fold_terminal_falls_nil (J := fun u => checkSeq sigs r u rest)
              (u0 :: us) fb hfold hterm0
              { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: envTyOf η env,
                σ := [.isValue (.boolean (normalResult v))]
                  :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
              hmem fbm hchk
          have hexit : fbm.exits = Bool.true :=
            checkSeq_exits sigs r
              { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: envTyOf η env,
                σ := [.isValue (.boolean (normalResult v))]
                  :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
              rest fbm hchk hfall
          have htermm : terminal fbm = Bool.true := by
            simp [terminal, hfall, hexit]
          have hle : worldLe
              { η := η, Γ := envTyOf η env,
                σ := [normalizeAtom η (typeOfV (JSValue.boolean (normalResult v)))]
                  :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
              { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: envTyOf η env,
                σ := [.isValue (.boolean (normalResult v))]
                  :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) } :=
            ⟨rfl, envLe_shadow_same hΓ,
      stackLe_cons_intro (slotLe_refl _) (stackLe_refl _),
      envCov_shadow_same hΓ,
      stackCov_cons_intro (tyCov_refl _ _) (stackCov_refl _ _)⟩
          obtain ⟨fb', hchk', hterm'⟩ :=
            checkSeq_specialize_terminal sigs r _ _ rest hsc hle hchk htermm
          simp only [typeOfV, normalizeAtom] at hchk' ⊢
          rw [hchk']
          exact hterm'
  | reject s why => rw [hfork] at h; exact h.elim

theorem frameTyped_kTestVar_pIsNormalC_reject_unbound {sigs : SigTable}
    {r : Ty} {x : «String»} {rest : List Instr} {env : Env}
    {eval : List JSValue} {ret : «String»}
    (hΓ : tyLookup (envTyOf η env) x = none) :
    frameTyped sigs η r ⟨.kTestVar x .pIsNormalC :: rest, env, eval, ret⟩
      = False := by
  simp [frameTyped, frameWorld, checkSeq, primDecide_pIsNormalC_eq, splitP1,
    hΓ, forkTC]

theorem SR_kTestVar_pIsNormalC (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kTestVar x .pIsNormalC) s r := by
  intro _ _ hsc hpre
  cases s with
  | fdone => exact ⟨η, hpre⟩
  | fell => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases hl : lookup env x with
          | none =>
              have hΓ : tyLookup (envTyOf η env) x = none := by
                have hbridge := envTyOf_lookup η env x
                simp only [hl, Option.map_none] at hbridge
                exact hbridge.symm
              have h1 : frameTyped sigs η (sigRetTy sigs ret)
                  ⟨.kTestVar x .pIsNormalC :: stmts, env, eval, ret⟩ :=
                hpre.2.2.2.1.1
              rw [frameTyped_kTestVar_pIsNormalC_reject_unbound hΓ] at h1
              exact h1.elim
          | some v =>
              have hΓ : tyLookup (envTyOf η env) x = some [normalizeAtom η (typeOfV v)] := by
                have hbridge := envTyOf_lookup η env x
                simp only [hl, Option.map_some] at hbridge
                exact hbridge.symm
              simp only [fstep, hl] at ⊢
              rw [applyPrim_pIsNormalC_eq heap v]
              obtain ⟨hhk, hwf⟩ := heapOk_framesWf_push_nolocs
                (i := .kTestVar x .pIsNormalC) (v := .boolean (normalResult v))
                (by simp [locsOf]) hpre.2.1 hpre.2.2.1
              refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kTestVar_pIsNormalC_present (hsc := hsc) hΓ
                  hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2.2.2.2

def throwResult (v : JSValue) : Bool :=
  match v with
  | .compl Bool.true _ => Bool.true
  | _ => Bool.false

def throwDec : VTy → Bool :=
  fun a =>
    match a with
    | .complT => Bool.true
    | _ => Bool.false

theorem primDecide_pIsThrowC_eq :
    primDecide .pIsThrowC = some throwDec := rfl

theorem applyPrim_pIsThrowC_eq (heap : Heap) (v : JSValue) :
    applyPrim heap .pIsThrowC v = .boolean (throwResult v) := by
  cases v with
  | compl b w => cases b <;> simp [applyPrim, throwResult]
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _ | descV _ =>
      simp [applyPrim, throwResult]

theorem splitP1_pIsThrow_machine {Γ : TyEnv} {x : «String»} {v : JSValue}
    {σ : List Ty}
    (hΓ : tyLookup Γ x = some [normalizeAtom η (typeOfV v)]) :
    { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: Γ,
      σ := [.isValue (.boolean (throwResult v))] :: σ }
      ∈ splitP1 x throwDec { η := η, Γ := Γ, σ := σ } := by
  cases v with
  | compl b w =>
      cases b <;> simp [splitP1, splitP1At, hΓ, typeOfV, throwDec,
        throwResult, normalizeAtom]
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _
    | descV _ =>
      simp [splitP1, splitP1At, hΓ, typeOfV, throwDec, throwResult, normalizeAtom]

theorem frameTyped_kTestVar_pIsThrowC_present {sigs : SigTable} {r : Ty}
    {x : «String»} {v : JSValue} {rest : List Instr} {env : Env}
    {eval : List JSValue} {ret : «String»} {hsc : sigParamsClosed sigs}
    (hΓ : tyLookup (envTyOf η env) x = some [normalizeAtom η (typeOfV v)])
    (h : frameTyped sigs η r ⟨.kTestVar x .pIsThrowC :: rest, env, eval, ret⟩) :
    frameTyped sigs η r ⟨rest, env, .boolean (throwResult v) :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  simp only [checkSeq, primDecide_pIsThrowC_eq] at h
  have hmem := splitP1_pIsThrow_machine (Γ := envTyOf η env)
    (σ := eval.map (fun y => [normalizeAtom η (typeOfV y)])) hΓ
  have hne : splitP1 x throwDec
      { η := η, Γ := envTyOf η env, σ := eval.map (fun y => [normalizeAtom η (typeOfV y)]) } ≠ [] := by
    intro hnil
    rw [hnil] at hmem
    cases hmem
  cases hfork : forkTC (Instr.kTestVar x Prim.pIsThrowC)
      (splitP1 x throwDec
        { η := η, Γ := envTyOf η env, σ := eval.map (fun y => [normalizeAtom η (typeOfV y)]) })
      (fun u => checkSeq sigs r u rest) with
  | flows fb =>
      have hterm0 : terminal fb = Bool.true := by
        rw [hfork] at h; exact h
      cases hws : splitP1 x throwDec
          { η := η, Γ := envTyOf η env, σ := eval.map (fun y => [normalizeAtom η (typeOfV y)]) } with
      | nil => exact absurd hws hne
      | cons u0 us =>
          rw [hws] at hfork hmem
          have hfold : (u0 :: us).foldl
              (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows
            = TCResult.flows fb := by
            simpa [forkTC] using hfork
          obtain ⟨fbm, hchk⟩ :=
            fold_all_flows (J := fun u => checkSeq sigs r u rest) (u0 :: us) fb
              hfold
              { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: envTyOf η env,
                σ := [.isValue (.boolean (throwResult v))]
                  :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
              hmem
          have hfall : fbm.falls = [] :=
            fold_terminal_falls_nil (J := fun u => checkSeq sigs r u rest)
              (u0 :: us) fb hfold hterm0
              { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: envTyOf η env,
                σ := [.isValue (.boolean (throwResult v))]
                  :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
              hmem fbm hchk
          have hexit : fbm.exits = Bool.true :=
            checkSeq_exits sigs r
              { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: envTyOf η env,
                σ := [.isValue (.boolean (throwResult v))]
                  :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
              rest fbm hchk hfall
          have htermm : terminal fbm = Bool.true := by
            simp [terminal, hfall, hexit]
          have hle : worldLe
              { η := η, Γ := envTyOf η env,
                σ := [normalizeAtom η (typeOfV (JSValue.boolean (throwResult v)))]
                  :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
              { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: envTyOf η env,
                σ := [.isValue (.boolean (throwResult v))]
                  :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) } :=
            ⟨rfl, envLe_shadow_same hΓ,
      stackLe_cons_intro (slotLe_refl _) (stackLe_refl _),
      envCov_shadow_same hΓ,
      stackCov_cons_intro (tyCov_refl _ _) (stackCov_refl _ _)⟩
          obtain ⟨fb', hchk', hterm'⟩ :=
            checkSeq_specialize_terminal sigs r _ _ rest hsc hle hchk htermm
          simp only [typeOfV, normalizeAtom] at hchk' ⊢
          rw [hchk']
          exact hterm'
  | reject s why => rw [hfork] at h; exact h.elim

theorem frameTyped_kTestVar_pIsThrowC_reject_unbound {sigs : SigTable}
    {r : Ty} {x : «String»} {rest : List Instr} {env : Env}
    {eval : List JSValue} {ret : «String»}
    (hΓ : tyLookup (envTyOf η env) x = none) :
    frameTyped sigs η r ⟨.kTestVar x .pIsThrowC :: rest, env, eval, ret⟩
      = False := by
  simp [frameTyped, frameWorld, checkSeq, primDecide_pIsThrowC_eq, splitP1,
    hΓ, forkTC]

theorem SR_kTestVar_pIsThrowC (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kTestVar x .pIsThrowC) s r := by
  intro _ _ hsc hpre
  cases s with
  | fdone => exact ⟨η, hpre⟩
  | fell => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases hl : lookup env x with
          | none =>
              have hΓ : tyLookup (envTyOf η env) x = none := by
                have hbridge := envTyOf_lookup η env x
                simp only [hl, Option.map_none] at hbridge
                exact hbridge.symm
              have h1 : frameTyped sigs η (sigRetTy sigs ret)
                  ⟨.kTestVar x .pIsThrowC :: stmts, env, eval, ret⟩ :=
                hpre.2.2.2.1.1
              rw [frameTyped_kTestVar_pIsThrowC_reject_unbound hΓ] at h1
              exact h1.elim
          | some v =>
              have hΓ : tyLookup (envTyOf η env) x = some [normalizeAtom η (typeOfV v)] := by
                have hbridge := envTyOf_lookup η env x
                simp only [hl, Option.map_some] at hbridge
                exact hbridge.symm
              simp only [fstep, hl] at ⊢
              rw [applyPrim_pIsThrowC_eq heap v]
              obtain ⟨hhk, hwf⟩ := heapOk_framesWf_push_nolocs
                (i := .kTestVar x .pIsThrowC) (v := .boolean (throwResult v))
                (by simp [locsOf]) hpre.2.1 hpre.2.2.1
              refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kTestVar_pIsThrowC_present (hsc := hsc) hΓ
                  hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2.2.2.2

theorem frameTyped_kTestVar_plainBool {sigs : SigTable} {r : Ty}
    {p : Prim} {x : «String»} {b : Bool}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    {hsc : sigParamsClosed sigs}
    (hstep : checkSeq sigs r
      { η := η, Γ := envTyOf η env, σ := eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
      (.kTestVar x p :: rest)
      = checkSeq sigs r
        { η := η, Γ := envTyOf η env,
          σ := [.anyValue .bool] :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
        rest)
    (h : frameTyped sigs η r ⟨.kTestVar x p :: rest, env, eval, ret⟩) :
    frameTyped sigs η r ⟨rest, env, .boolean b :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  rw [hstep] at h
  exact frameTyped_pushRefine (ret := ret) hsc (T := [.anyValue .bool])
    (slotLe_bool_result η b) (atomCov_single atomCov_boolSing_class) h

theorem SR_kTestVar_plainBool (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (p : Prim) (x : «String») (s : FM) (r : Ty)
    (hsome : ∀ (rd : Ty) (v : JSValue) (env : Env) (eval : List JSValue)
        (rest : List Instr),
      tyLookup (envTyOf η env) x = some [normalizeAtom η (typeOfV v)] →
      checkSeq sigs rd
        { η := η, Γ := envTyOf η env, σ := eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
        (.kTestVar x p :: rest)
      = checkSeq sigs rd
        { η := η, Γ := envTyOf η env,
          σ := [.anyValue .bool] :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
        rest)
    (hnone : ∀ (rd : Ty) (env : Env) (eval : List JSValue)
        (rest : List Instr),
      tyLookup (envTyOf η env) x = none →
      checkSeq sigs rd
        { η := η, Γ := envTyOf η env, σ := eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
        (.kTestVar x p :: rest)
      = TCResult.reject (.kTestVar x p) "unbound variable")
    (hrun : ∀ (heap : Heap) (v : JSValue),
      ∃ b, applyPrim heap p v = JSValue.boolean b) :
    SR_arm sigs reg η (.kTestVar x p) s r := by
  intro _ _ hsc hpre
  cases s with
  | fdone => exact ⟨η, hpre⟩
  | fell => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases hl : lookup env x with
          | none =>
              have hΓ : tyLookup (envTyOf η env) x = none := by
                have hbridge := envTyOf_lookup η env x
                simp only [hl, Option.map_none] at hbridge
                exact hbridge.symm
              exfalso
              have h1 : frameTyped sigs η (sigRetTy sigs ret)
                  ⟨.kTestVar x p :: stmts, env, eval, ret⟩ := hpre.2.2.2.1.1
              simp only [frameTyped, frameWorld] at h1
              rw [hnone (sigRetTy sigs ret) env eval stmts hΓ] at h1
              exact h1.elim
          | some v =>
              have hΓ : tyLookup (envTyOf η env) x = some [normalizeAtom η (typeOfV v)] := by
                have hbridge := envTyOf_lookup η env x
                simp only [hl, Option.map_some] at hbridge
                exact hbridge.symm
              obtain ⟨b, hb⟩ := hrun heap v
              simp only [fstep, hl] at ⊢
              rw [hb]
              obtain ⟨hhk, hwf⟩ := heapOk_framesWf_push_nolocs
                (i := .kTestVar x p) (v := .boolean b)
                (by simp [locsOf]) hpre.2.1 hpre.2.2.1
              refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kTestVar_plainBool (hsc := hsc)
                  (hstep := hsome (sigRetTy sigs ret) v env eval stmts hΓ)
                  hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2.2.2.2

theorem SR_kTestVar_pHasCall (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kTestVar x .pHasCall) s r :=
  SR_kTestVar_plainBool sigs reg η .pHasCall x s r
    (fun _ _ _ _ _ hΓ => by simp [checkSeq, testTypeP, hΓ])
    (fun _ _ _ _ hΓ => by simp [checkSeq, testTypeP, hΓ])
    (fun heap v => ⟨hasCallV heap v, by simp [applyPrim]⟩)

theorem SR_kTestVar_pHasCtor (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kTestVar x .pHasCtor) s r :=
  SR_kTestVar_plainBool sigs reg η .pHasCtor x s r
    (fun _ _ _ _ _ hΓ => by simp [checkSeq, testTypeP, hΓ])
    (fun _ _ _ _ hΓ => by simp [checkSeq, testTypeP, hΓ])
    (fun heap v => ⟨hasCtorV heap v, by simp [applyPrim]⟩)

theorem SR_kTestVar_pHasField (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (nm : «String») (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kTestVar x (.pHasField nm)) s r :=
  SR_kTestVar_plainBool sigs reg η (.pHasField nm) x s r
    (fun _ _ _ _ _ hΓ => by simp [checkSeq, testTypeP, hΓ])
    (fun _ _ _ _ hΓ => by simp [checkSeq, testTypeP, hΓ])
    (fun _ v => by cases v <;> simp [applyPrim])

theorem SR_kTestVar_pPred_unknown (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (f : «String») (b : Bool) (x : «String») (s : FM) (r : Ty)
    (hf : predDecide η f = none) :
    SR_arm sigs reg η (.kTestVar x (.pPred f b)) s r :=
  SR_kTestVar_plainBool sigs reg η (.pPred f b) x s r
    (fun _ _ _ _ _ hΓ => by simp [checkSeq, hf, hΓ])
    (fun _ _ _ _ hΓ => by simp [checkSeq, hf, hΓ])
    (fun _ v => by
      by_cases h1 : f = "IsDataDescriptor"
      · subst h1; simp [predDecide] at hf
      · by_cases h2 : f = "IsAccessorDescriptor"
        · subst h2; simp [predDecide] at hf
        · by_cases h3 : f = "IsCallable"
          · subst h3; simp [predDecide] at hf
          · simp [applyPrim, h1, h2, h3])

theorem frameTyped_kTestVar_pPred_present {sigs : SigTable} {r : Ty}
    {f : «String»} {b : Bool} {dec : VTy → Bool}
    {g : JSValue → Bool} {x : «String»} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    {hsc : sigParamsClosed sigs}
    (hdec : predDecide η f = some dec)
    (hmem : ∀ (Γ : TyEnv) (σ : List Ty), tyLookup Γ x = some [normalizeAtom η (typeOfV v)] →
      { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: Γ,
        σ := [.isValue (.boolean (g v))] :: σ }
      ∈ splitP1 x (fun a => dec a == b)
        { η := η, Γ := Γ, σ := σ })
    (hΓ : tyLookup (envTyOf η env) x = some [normalizeAtom η (typeOfV v)])
    (h : frameTyped sigs η r ⟨.kTestVar x (.pPred f b) :: rest, env, eval, ret⟩) :
    frameTyped sigs η r ⟨rest, env, .boolean (g v) :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  simp only [checkSeq, hdec] at h
  have hmem0 := hmem (Γ := envTyOf η env)
    (σ := eval.map (fun y => [normalizeAtom η (typeOfV y)])) hΓ
  have hne : splitP1 x (fun a => dec a == b)
      { η := η, Γ := envTyOf η env, σ := eval.map (fun y => [normalizeAtom η (typeOfV y)]) } ≠ [] := by
    intro hnil
    rw [hnil] at hmem0
    cases hmem0
  cases hfork : forkTC (Instr.kTestVar x (Prim.pPred f b))
      (splitP1 x (fun a => dec a == b)
        { η := η, Γ := envTyOf η env, σ := eval.map (fun y => [normalizeAtom η (typeOfV y)]) })
      (fun u => checkSeq sigs r u rest) with
  | flows fb =>
      have hterm0 : terminal fb = Bool.true := by
        rw [hfork] at h; exact h
      cases hws : splitP1 x (fun a => dec a == b)
          { η := η, Γ := envTyOf η env, σ := eval.map (fun y => [normalizeAtom η (typeOfV y)]) } with
      | nil => exact absurd hws hne
      | cons u0 us =>
          rw [hws] at hfork hmem0
          have hfold : (u0 :: us).foldl
              (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows
            = TCResult.flows fb := by
            simpa [forkTC] using hfork
          obtain ⟨fbm, hchk⟩ :=
            fold_all_flows (J := fun u => checkSeq sigs r u rest) (u0 :: us) fb
              hfold
              { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: envTyOf η env,
                σ := [.isValue (.boolean (g v))]
                  :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
              hmem0
          have hfall : fbm.falls = [] :=
            fold_terminal_falls_nil (J := fun u => checkSeq sigs r u rest)
              (u0 :: us) fb hfold hterm0
              { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: envTyOf η env,
                σ := [.isValue (.boolean (g v))]
                  :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
              hmem0 fbm hchk
          have hexit : fbm.exits = Bool.true :=
            checkSeq_exits sigs r
              { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: envTyOf η env,
                σ := [.isValue (.boolean (g v))]
                  :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
              rest fbm hchk hfall
          have htermm : terminal fbm = Bool.true := by
            simp [terminal, hfall, hexit]
          have hle : worldLe
              { η := η, Γ := envTyOf η env,
                σ := [normalizeAtom η (typeOfV (JSValue.boolean (g v)))]
                  :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) }
              { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: envTyOf η env,
                σ := [.isValue (.boolean (g v))]
                  :: eval.map (fun y => [normalizeAtom η (typeOfV y)]) } :=
            ⟨rfl, envLe_shadow_same hΓ,
      stackLe_cons_intro (slotLe_refl _) (stackLe_refl _),
      envCov_shadow_same hΓ,
      stackCov_cons_intro (tyCov_refl _ _) (stackCov_refl _ _)⟩
          obtain ⟨fb', hchk', hterm'⟩ :=
            checkSeq_specialize_terminal sigs r _ _ rest hsc hle hchk htermm
          simp only [typeOfV, normalizeAtom] at hchk' ⊢
          rw [hchk']
          exact hterm'
  | reject s why => rw [hfork] at h; exact h.elim

theorem SR_kTestVar_pPred_split (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (f : «String») (b : Bool) (dec : VTy → Bool)
    (g : JSValue → Bool) (x : «String») (s : FM) (r : Ty)
    (hdec : predDecide η f = some dec)
    (hmem : ∀ (v : JSValue) (Γ : TyEnv) (σ : List Ty),
      tyLookup Γ x = some [normalizeAtom η (typeOfV v)] →
      { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: Γ,
        σ := [.isValue (.boolean (g v))] :: σ }
      ∈ splitP1 x (fun a => dec a == b)
        { η := η, Γ := Γ, σ := σ })
    (hrun : ∀ (heap : Heap) (v : JSValue),
      applyPrim heap (.pPred f b) v = JSValue.boolean (g v)) :
    SR_arm sigs reg η (.kTestVar x (.pPred f b)) s r := by
  intro _ _ hsc hpre
  cases s with
  | fdone => exact ⟨η, hpre⟩
  | fell => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f' fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f'
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases hl : lookup env x with
          | none =>
              have hΓ : tyLookup (envTyOf η env) x = none := by
                have hbridge := envTyOf_lookup η env x
                simp only [hl, Option.map_none] at hbridge
                exact hbridge.symm
              exfalso
              have h1 : frameTyped sigs η (sigRetTy sigs ret)
                  ⟨.kTestVar x (.pPred f b) :: stmts, env, eval, ret⟩ :=
                hpre.2.2.2.1.1
              simp only [frameTyped, frameWorld, checkSeq, hdec, splitP1,
                hΓ, forkTC] at h1
          | some v =>
              have hΓ : tyLookup (envTyOf η env) x = some [normalizeAtom η (typeOfV v)] := by
                have hbridge := envTyOf_lookup η env x
                simp only [hl, Option.map_some] at hbridge
                exact hbridge.symm
              simp only [fstep, hl] at ⊢
              rw [hrun heap v]
              obtain ⟨hhk, hwf⟩ := heapOk_framesWf_push_nolocs
                (i := .kTestVar x (.pPred f b)) (v := .boolean (g v))
                (by simp [locsOf]) hpre.2.1 hpre.2.2.1
              refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kTestVar_pPred_present (hsc := hsc) hdec
                  (hmem v) hΓ hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2.2.2.2

def dataPredResult (v : JSValue) : Bool :=
  match v with
  | .descV (.mk value writable _ _ _ _) =>
      value.isSome || writable.isSome
  | _ => Bool.false

def dataPredDec : VTy → Bool :=
  fun a =>
    match a with
    | .desc fs => fs.any (fun fld => fData.contains fld)
    | _ => Bool.false

theorem predDecide_data (η : HeapCallableTy) :
    predDecide η "IsDataDescriptor" = some dataPredDec := rfl

theorem applyPrim_pPred_data (heap : Heap) (b : Bool) (v : JSValue) :
    applyPrim heap (.pPred "IsDataDescriptor" b) v
      = .boolean (b == dataPredResult v) := by
  cases v with
  | compl abrupt w =>
      cases abrupt <;> cases b <;> simp [applyPrim, dataPredResult]
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _ =>
      cases b <;> simp [applyPrim, dataPredResult]
  | descV d =>
      cases d with
      | mk value writable getter setter enumerable configurable =>
          cases b <;> simp [applyPrim, dataPredResult]

theorem field_value_eq_self :
    (Field.value == Field.value) = Bool.true := rfl
theorem field_writable_eq_self :
    (Field.writable == Field.writable) = Bool.true := rfl

theorem field_getter_ne_value :
    (Field.getter == Field.value) = Bool.false := rfl
theorem field_getter_ne_writable :
    (Field.getter == Field.writable) = Bool.false := rfl
theorem field_setter_ne_value :
    (Field.setter == Field.value) = Bool.false := rfl
theorem field_setter_ne_writable :
    (Field.setter == Field.writable) = Bool.false := rfl
theorem field_enumerable_ne_value :
    (Field.enumerable == Field.value) = Bool.false := rfl
theorem field_enumerable_ne_writable :
    (Field.enumerable == Field.writable) = Bool.false := rfl
theorem field_configurable_ne_value :
    (Field.configurable == Field.value) = Bool.false := rfl
theorem field_configurable_ne_writable :
    (Field.configurable == Field.writable) = Bool.false := rfl

theorem fieldsOf_data_eq (value : Option JSValue)
    (writable enumerable configurable : Option Bool)
    (getter setter : Option Nat) :
    (fieldsOf (Descriptor.mk value writable getter setter enumerable
        configurable)).any (fun fld => fData.contains fld)
      = (value.isSome || writable.isSome) := by
  cases value <;> cases writable <;> cases getter <;> cases setter <;>
    cases enumerable <;> cases configurable <;>
      simp [fieldsOf, fData, field_value_eq_self,
        field_writable_eq_self, field_getter_ne_value,
        field_getter_ne_writable, field_setter_ne_value,
        field_setter_ne_writable, field_enumerable_ne_value,
        field_enumerable_ne_writable, field_configurable_ne_value,
        field_configurable_ne_writable]

theorem splitP1_pPred_data_machine (b : Bool) {Γ : TyEnv} {x : «String»}
    {v : JSValue} {σ : List Ty}
    (hΓ : tyLookup Γ x = some [normalizeAtom η (typeOfV v)]) :
    { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: Γ,
      σ := [.isValue (.boolean (b == dataPredResult v))] :: σ }
      ∈ splitP1 x (fun a => dataPredDec a == b)
        { η := η, Γ := Γ, σ := σ } := by
  cases v with
  | compl b' w =>
      cases b' <;> cases b <;>
        simp [splitP1, splitP1At, hΓ, typeOfV, dataPredDec, dataPredResult, normalizeAtom]
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _ =>
      cases b <;>
        simp [splitP1, splitP1At, hΓ, typeOfV, dataPredDec, dataPredResult, normalizeAtom]
  | descV d =>
      cases d with
      | mk value writable getter setter enumerable configurable =>
          simp only [splitP1, splitP1At, hΓ, typeOfV, dataPredDec,
            dataPredResult, normalizeAtom]
          have hd := fieldsOf_data_eq value writable enumerable configurable
            getter setter
          simp [List.flatMap, splitP1At, hd]
          cases value <;> cases writable <;> cases b <;> simp

theorem SR_kTestVar_pPred_data (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (b : Bool) (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kTestVar x (.pPred "IsDataDescriptor" b)) s r :=
  SR_kTestVar_pPred_split sigs reg η "IsDataDescriptor" b dataPredDec
    (fun v => b == dataPredResult v) x s r
    (predDecide_data η)
    (fun _ Γ σ hΓ => splitP1_pPred_data_machine b hΓ)
    (fun heap v => applyPrim_pPred_data heap b v)

def accPredResult (v : JSValue) : Bool :=
  match v with
  | .descV (.mk _ _ getter setter _ _) =>
      getter.isSome || setter.isSome
  | _ => Bool.false

def accPredDec : VTy → Bool :=
  fun a =>
    match a with
    | .desc fs => fs.any (fun fld => fAcc.contains fld)
    | _ => Bool.false

theorem predDecide_acc (η : HeapCallableTy) :
    predDecide η "IsAccessorDescriptor" = some accPredDec := rfl

theorem applyPrim_pPred_acc (heap : Heap) (b : Bool) (v : JSValue) :
    applyPrim heap (.pPred "IsAccessorDescriptor" b) v
      = .boolean (b == accPredResult v) := by
  cases v with
  | compl abrupt w =>
      cases abrupt <;> cases b <;> simp [applyPrim, accPredResult]
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _ =>
      cases b <;> simp [applyPrim, accPredResult]
  | descV d =>
      cases d with
      | mk value writable getter setter enumerable configurable =>
          cases b <;> simp [applyPrim, accPredResult]

theorem field_getter_eq_self :
    (Field.getter == Field.getter) = Bool.true := rfl
theorem field_setter_eq_self :
    (Field.setter == Field.setter) = Bool.true := rfl

theorem field_value_ne_getter :
    (Field.value == Field.getter) = Bool.false := rfl
theorem field_value_ne_setter :
    (Field.value == Field.setter) = Bool.false := rfl
theorem field_writable_ne_getter :
    (Field.writable == Field.getter) = Bool.false := rfl
theorem field_writable_ne_setter :
    (Field.writable == Field.setter) = Bool.false := rfl
theorem field_enumerable_ne_getter :
    (Field.enumerable == Field.getter) = Bool.false := rfl
theorem field_enumerable_ne_setter :
    (Field.enumerable == Field.setter) = Bool.false := rfl
theorem field_configurable_ne_getter :
    (Field.configurable == Field.getter) = Bool.false := rfl
theorem field_configurable_ne_setter :
    (Field.configurable == Field.setter) = Bool.false := rfl

theorem fieldsOf_acc_eq (value : Option JSValue)
    (writable enumerable configurable : Option Bool)
    (getter setter : Option Nat) :
    (fieldsOf (Descriptor.mk value writable getter setter enumerable
        configurable)).any (fun fld => fAcc.contains fld)
      = (getter.isSome || setter.isSome) := by
  cases value <;> cases writable <;> cases getter <;> cases setter <;>
    cases enumerable <;> cases configurable <;>
      simp [fieldsOf, fAcc, field_getter_eq_self,
        field_setter_eq_self, field_value_ne_getter,
        field_value_ne_setter, field_writable_ne_getter,
        field_writable_ne_setter, field_enumerable_ne_getter,
        field_enumerable_ne_setter, field_configurable_ne_getter,
        field_configurable_ne_setter]

theorem splitP1_pPred_acc_machine (b : Bool) {Γ : TyEnv} {x : «String»}
    {v : JSValue} {σ : List Ty}
    (hΓ : tyLookup Γ x = some [normalizeAtom η (typeOfV v)]) :
    { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: Γ,
      σ := [.isValue (.boolean (b == accPredResult v))] :: σ }
      ∈ splitP1 x (fun a => accPredDec a == b)
        { η := η, Γ := Γ, σ := σ } := by
  cases v with
  | compl b' w =>
      cases b' <;> cases b <;>
        simp [splitP1, splitP1At, hΓ, typeOfV, accPredDec, accPredResult, normalizeAtom]
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _ =>
      cases b <;>
        simp [splitP1, splitP1At, hΓ, typeOfV, accPredDec, accPredResult, normalizeAtom]
  | descV d =>
      cases d with
      | mk value writable getter setter enumerable configurable =>
          simp only [splitP1, splitP1At, hΓ, typeOfV, accPredDec,
            accPredResult, normalizeAtom]
          have hd := fieldsOf_acc_eq value writable enumerable configurable
            getter setter
          simp [List.flatMap, splitP1At, hd]
          cases getter <;> cases setter <;> cases b <;> simp

theorem SR_kTestVar_pPred_acc (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (b : Bool) (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kTestVar x (.pPred "IsAccessorDescriptor" b)) s r :=
  SR_kTestVar_pPred_split sigs reg η "IsAccessorDescriptor" b accPredDec
    (fun v => b == accPredResult v) x s r
    (predDecide_acc η)
    (fun _ Γ σ hΓ => splitP1_pPred_acc_machine b hΓ)
    (fun heap v => applyPrim_pPred_acc heap b v)

theorem applyPrim_pPred_callable (heap : Heap) (b : Bool) (v : JSValue) :
    applyPrim heap (.pPred "IsCallable" b) v
      = .boolean (b == hasCallV heap v) := by
  cases v with
  | obj loc =>
      cases hobj : heap loc with
      | none => simp [applyPrim, hasCallV, hobj]
      | some o =>
          cases o.kind <;> simp [applyPrim, hasCallV, hobj]
  | undefined | null | boolean _ | number _ | str _ | listV _ | descV _
    | compl _ _ =>
      simp [applyPrim, hasCallV]

theorem hasCallV_obj (heap : Heap) (loc : Nat) :
    hasCallV heap (JSValue.obj loc) = runtimeCallable heap loc := by
  simp only [hasCallV, runtimeCallable]
  cases heap loc with
  | none => rfl
  | some o => cases o.kind <;> rfl

theorem splitP1_pPred_callable_obj (heap : Heap) (b : Bool)
    {Γ : TyEnv} {x : «String»} {loc : Nat} {σ : List Ty}
    (hheap : heapCallabilityOk heap η)
    (hΓ : tyLookup Γ x = some [normalizeAtom η (typeOfV (JSValue.obj loc))]) :
    { η := η, Γ := (x, [normalizeAtom η (typeOfV (JSValue.obj loc))]) :: Γ,
      σ := [.isValue (.boolean (b == hasCallV heap (JSValue.obj loc)))] :: σ }
      ∈ splitP1 x (fun a => isCallableAtom η a == b)
        { η := η, Γ := Γ, σ := σ } := by
  have hloc : η loc = hasCallV heap (JSValue.obj loc) := by
    rw [hheap loc, hasCallV_obj]
  cases hb : b == hasCallV heap (JSValue.obj loc)
  · have hnb : ¬ b = hasCallV heap (JSValue.obj loc) := by
      intro h
      rw [h] at hb
      simp at hb
    have hnb' : ¬ η loc = b := by
      rw [hloc]
      exact fun h => hnb h.symm
    simp [splitP1, splitP1At, hΓ, typeOfV, isCallableAtom,
      normalizeAtom, hloc, hnb', hb]
    first
      | rfl
      | exact fun h => hnb h.symm
  · have hb' : η loc = b := by
      rw [hloc]
      simp only [beq_iff_eq] at hb
      exact hb.symm
    simp [splitP1, splitP1At, hΓ, typeOfV, isCallableAtom,
      normalizeAtom, hloc, hb', hb]
    first
      | rfl
      | (rw [← hloc, hb'])

theorem splitP1_pPred_callable_machine (heap : Heap) (b : Bool)
    {Γ : TyEnv} {x : «String»} {v : JSValue} {σ : List Ty}
    (hheap : heapCallabilityOk heap η)
    (hΓ : tyLookup Γ x = some [normalizeAtom η (typeOfV v)]) :
    { η := η, Γ := (x, [normalizeAtom η (typeOfV v)]) :: Γ,
      σ := [.isValue (.boolean (b == hasCallV heap v))] :: σ }
      ∈ splitP1 x (fun a => isCallableAtom η a == b)
        { η := η, Γ := Γ, σ := σ } := by
  cases v with
  | obj loc => exact splitP1_pPred_callable_obj heap b hheap hΓ
  | compl abrupt w =>
      cases abrupt <;> cases b <;>
        simp [splitP1, splitP1At, hΓ, typeOfV, isCallableAtom, hasCallV, normalizeAtom]
  | undefined | null | boolean _ | number _ | str _ | listV _ | descV _ =>
      cases b <;>
        simp [splitP1, splitP1At, hΓ, typeOfV, isCallableAtom, hasCallV, normalizeAtom]

theorem frameTyped_kTestVar_pPred_callable_present {sigs : SigTable}
    {r : Ty} {heap : Heap} {b : Bool} {x : «String»} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    {hsc : sigParamsClosed sigs}
    (hheap : heapCallabilityOk heap η)
    (hΓ : tyLookup (envTyOf η env) x = some [normalizeAtom η (typeOfV v)])
    (h : frameTyped sigs η r ⟨.kTestVar x (.pPred "IsCallable" b) :: rest,
        env, eval, ret⟩) :
    frameTyped sigs η r ⟨rest, env, .boolean (b == hasCallV heap v) :: eval,
        ret⟩ :=
  frameTyped_kTestVar_pPred_present (hsc := hsc)
    (f := "IsCallable") (b := b) (dec := isCallableAtom η)
    (g := fun y => b == hasCallV heap y) (x := x) (v := v)
    (rest := rest) (env := env) (eval := eval) (ret := ret) rfl
    (fun Γ σ hlookup => splitP1_pPred_callable_machine heap b hheap hlookup)
      hΓ h

theorem frameTyped_kTestVar_pPred_callable_reject_unbound {sigs : SigTable}
    {r : Ty} {b : Bool} {x : «String»} {rest : List Instr} {env : Env}
    {eval : List JSValue} {ret : «String»}
    (hΓ : tyLookup (envTyOf η env) x = none) :
    frameTyped sigs η r ⟨.kTestVar x (.pPred "IsCallable" b) :: rest,
        env, eval, ret⟩ = False := by
  simp [frameTyped, frameWorld, checkSeq, predDecide, splitP1, hΓ, forkTC]

theorem SR_kTestVar_pPred_callable (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (b : Bool) (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kTestVar x (.pPred "IsCallable" b)) s r := by
  intro _ _ hsc hpre
  cases s with
  | fdone => exact ⟨η, hpre⟩
  | fell => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases hl : lookup env x with
          | none =>
              have hΓ : tyLookup (envTyOf η env) x = none := by
                have hbridge := envTyOf_lookup η env x
                simp only [hl, Option.map_none] at hbridge
                exact hbridge.symm
              exfalso
              have h1 : frameTyped sigs η (sigRetTy sigs ret)
                  ⟨.kTestVar x (.pPred "IsCallable" b) :: stmts, env, eval,
                      ret⟩ := hpre.2.2.2.1.1
              rw [frameTyped_kTestVar_pPred_callable_reject_unbound hΓ] at h1
              exact h1.elim
          | some v =>
              have hΓ : tyLookup (envTyOf η env) x = some [normalizeAtom η (typeOfV v)] := by
                have hbridge := envTyOf_lookup η env x
                simp only [hl, Option.map_some] at hbridge
                exact hbridge.symm
              simp only [fstep, hl] at ⊢
              rw [applyPrim_pPred_callable heap b v]
              obtain ⟨hhk, hwf⟩ := heapOk_framesWf_push_nolocs
                (i := .kTestVar x (.pPred "IsCallable" b)) (v := .boolean (b == hasCallV heap v))
                (by simp [locsOf]) hpre.2.1 hpre.2.2.1
              refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kTestVar_pPred_callable_present
                  (hsc := hsc) hpre.1 hΓ hpre.2.2.2.1.1, hpre.2.2.2.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2.2.2.2

theorem SR_kEval_fused_step (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (e : Expr) (x : «String») (p : Prim) (s : FM) (r : Ty)
    (hstep : ∀ (stmts : List Instr) (env : Env) (eval : List JSValue)
        (ret : «String») (fs : List Fr) (heap : Heap) (nl : Nat),
      fstep reg (FM.frames
          (⟨.kEval e :: stmts, env, eval, ret⟩ :: fs) heap nl)
        = FM.frames (⟨.kTestVar x p :: stmts, env, eval, ret⟩ :: fs) heap nl)
    (hchk : ∀ (rd : Ty) (rest : List Instr) (Γ : TyEnv) (σ : List Ty),
      checkSeq sigs rd { η := η, Γ := Γ, σ := σ } (.kEval e :: rest)
        = checkSeq sigs rd { η := η, Γ := Γ, σ := σ } (.kTestVar x p :: rest)) :
    SR_arm sigs reg η (.kEval e) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact ⟨η, hpre⟩
  | fell => exact ⟨η, hpre⟩
  | frames fs heap nl =>
      cases fs with
      | nil => exact ⟨η, hpre⟩
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead] at hpre ⊢
          rw [hstep stmts env eval ret fs' heap nl]
          simp only [stateTyped, framesTypedFrom] at hpre ⊢
          obtain ⟨hhk, hwf⟩ := heapOk_framesWf_stmts_swap
            (j := .kTestVar x p) hpre.2.1 hpre.2.2.1
            ⟨instrWf_kTestVar, hpre.2.2.1.1.2⟩
          refine ⟨η, hpre.1, hhk, hwf, ⟨frameTyped_kEval_fused (hchk _ _ _ _) hpre.2.2.2.1.1,
            hpre.2.2.2.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2.2.2.2

theorem SR_kEval_isNull_nv (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kEval (.isNull (.nv x))) s r :=
  SR_kEval_fused_step sigs reg η (.isNull (.nv x)) x .pIsNull s r
    (by intro _ _ _ _ _ _ _; rfl)
    (by intro _ _ _ _; simp [checkSeq])

theorem SR_kEval_isNormalC_nv (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kEval (.isNormalC (.nv x))) s r :=
  SR_kEval_fused_step sigs reg η (.isNormalC (.nv x)) x .pIsNormalC s r
    (by intro _ _ _ _ _ _ _; rfl)
    (by intro _ _ _ _; simp [checkSeq])

theorem SR_kEval_isThrowC_nv (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kEval (.isThrowC (.nv x))) s r :=
  SR_kEval_fused_step sigs reg η (.isThrowC (.nv x)) x .pIsThrowC s r
    (by intro _ _ _ _ _ _ _; rfl)
    (by intro _ _ _ _; simp [checkSeq])

theorem SR_kEval_isCompletion_nv (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kEval (.isCompletion (.nv x))) s r :=
  SR_kEval_fused_step sigs reg η (.isCompletion (.nv x)) x .pIsCompletion s r
    (by intro _ _ _ _ _ _ _; rfl)
    (by intro _ _ _ _; simp [checkSeq])

theorem SR_kEval_isType_nv (sigs : SigTable) (reg : AOReg) (η : HeapCallableTy)
    (ty : «String») (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg η (.kEval (.isType ty (.nv x))) s r :=
  SR_kEval_fused_step sigs reg η (.isType ty (.nv x)) x (.pIsType ty) s r
    (by intro _ _ _ _ _ _ _; rfl)
    (by intro _ _ _ _; simp [checkSeq])