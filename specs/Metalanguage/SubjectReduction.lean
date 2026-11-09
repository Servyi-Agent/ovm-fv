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

def envTyOf : Env → TyEnv := fun env =>
  env.map (fun (n, v) => (n, [typeOfV v]))

theorem envTyOf_lookup (env : Env) (x : «String») :
    (lookup env x).map (fun v => [typeOfV v]) = tyLookup (envTyOf env) x := by
  induction env with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨n, v⟩ := hd
      by_cases h : n == x
      · simp [lookup, tyLookup, envTyOf, h]
      · simp [lookup, tyLookup, envTyOf, h, ih]

theorem envTyOf_cons (n : «String») (v : JSValue) (env : Env) :
    envTyOf ((n, v) :: env) = (n, [typeOfV v]) :: envTyOf env := rfl

/-- THE ABSTRACTION FUNCTION: value frame → type-machine state
    (the canonical singleton map — the bridge, named; implicit in
    frameTyped). -/
def frameWorld (f : Fr) : World :=
  { Γ := envTyOf f.env, σ := f.eval.map (fun v => [typeOfV v]) }

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
def frameChecksAt (sigs : SigTable) (f : Fr) (top : Ty) : Prop :=
  match checkSeq sigs (sigRetTy sigs f.ret)
    { Γ := envTyOf f.env, σ := top :: f.eval.map (fun v => [typeOfV v]) } f.stmts with
  | .flows fb => terminal fb = Bool.true  -- every world returns
  | _ => False

/-- The frame's check as it stands. -/
def frameChecks (sigs : SigTable) (f : Fr) : Prop :=
  match checkSeq sigs (sigRetTy sigs f.ret) (frameWorld f) f.stmts with
  | .flows fb => terminal fb = Bool.true  -- every world returns
  | _ => False

def frameOk (sigs : SigTable) (above : Option «String») (f : Fr) : Prop :=
  -- a frame under a callee MUST be waiting at the self-test idiom:
  -- the delivery assumption of kRet
  (above.isNone ∨ selfTestHead f.stmts = Bool.true)
    ∧ (match above with
       | some n => ∀ c ∈ sigCompls sigs n,
           frameChecksAt sigs f (complTy [c])
       | none => frameChecks sigs f)

/-- Each frame is checked at its own destiny (its AO's declared
    return type), anticipating a delivery TYPED by the frame directly
    above. -/
def framesOkFrom : SigTable → Option «String» → List Fr → Prop
  | _, _, [] => True
  | sigs, above, f :: fs =>
      frameOk sigs above f ∧ framesOkFrom sigs f.ret fs

def framesOk (sigs : SigTable) (fs : List Fr) : Prop :=
  framesOkFrom sigs none fs

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
  | [] => ∀ l < n, ∀ o, heap l = some o →
      (objRefs o).all (fun r => r < n ∧ (heap r).isSome)
  | f :: fs =>
      (∀ l ∈ (f.eval.flatMap locsOf ++ (f.env.map Prod.snd).flatMap locsOf),
        l < n ∧ (heap l).isSome)
      ∧ heapOk heap n fs

/- ## Heap typing (store typing) -/

abbrev HeapTy := Nat → Kind

def objConsistent (k : Kind) (o : JsObj) : Bool :=
  match k, o.kind with
  | .ordinary, .ordinary => Bool.true
  | .string _, .string _ => Bool.true
  | .builtin _ _, .builtin _ _ => Bool.true
  | _, _ => Bool.false

def heapTyOk (heap : Heap) (ht : HeapTy) (n : Nat) : Prop :=
  ∀ l < n, ∀ o, heap l = some o →
    objConsistent (ht l) o = Bool.true
    ∧ ∀ p, o.proto = some p →
        p < n ∧ (heap p).isSome = Bool.true ∧ ht p = .ordinary

/- The machine's return type is the BOTTOM frame's destiny (stable:
    only that frame popping turns the state into fdone). -/
def machineRet (sigs : SigTable) (fs : List Fr) : Ty :=
  match fs.getLast? with
  | some f => sigRetTy sigs f.ret
  | none => [.anyValue .undef]

/- ## State typing, indexed by the machine's answer type r.

    fell is ILL-TYPED: with this definition, preservation alone
    already implies progress. -/

def instrWf (heap : Heap) (nl : Nat) (i : Instr) : Prop :=
  match i with
  | .kEval (.const v) =>
      ∀ l ∈ locsOf v, l < nl ∧ (heap l).isSome = Bool.true
  | .kForBody _ vs _ =>
      ∀ l ∈ vs.flatMap locsOf, l < nl ∧ (heap l).isSome = Bool.true
  | _ => True

def instrsWf (heap : Heap) (nl : Nat) : List Instr → Prop
  | [] => True
  | i :: rest => instrWf heap nl i ∧ instrsWf heap nl rest

def framesWf (heap : Heap) (nl : Nat) : List Fr → Prop
  | [] => True
  | f :: fs => instrsWf heap nl f.stmts ∧ framesWf heap nl fs

def stateOk (sigs : SigTable) (r : Ty) (m : FM) : Prop :=
  match m with
  | .frames fs heap nl =>
      fs.isEmpty = Bool.false
      ∧ framesOk sigs fs ∧ heapOk heap nl fs
      ∧ (∃ ht, heapTyOk heap ht nl)
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
    answered by the registry or natively; the MOP-Get dispatch target
    exists. -/
def closedRegistry (sigs : SigTable) (reg : AOReg) : Prop :=
  (∀ n _ps _ret, sigFind sigs n = some (_ps, _ret) →
      (findAO reg n).isSome = Bool.true ∨ nativeOps.contains n = Bool.true)
  ∧ (findAO reg "OrdinaryGet").isSome = Bool.true

/- ## Registry certification

    kCall pushes the callee's compiled body with a fresh env made from
    the ACTUAL argument values. Nothing about the caller can make that
    frame well-typed, so subject reduction is relative to a registry
    certified at every argument typing that satisfies the signature. -/

/-- The certificate a registry entry carries at a given argument
    typing. -/
def certifies (sigs : SigTable) (name : «String») (ps : List «String»)
    (ts : List Ty) (prog : Prog) : Prop :=
  match checkSeq sigs (sigRetTy sigs name)
      { Γ := zipTy ps ts, σ := []} (compileSteps prog) with
  | .flows fb =>
      terminal fb = Bool.true
        ∧ (fb.throws = Bool.true → complCanThrow (sigCompls sigs name) = Bool.true)
  | _ => False

theorem certifies_flows_elim {sigs : SigTable} {name : «String»}
    {ps : List «String»} {ts : List Ty} {prog : Prog}
    (h : certifies sigs name ps ts prog) :
    ∃ fb, checkSeq sigs (sigRetTy sigs name)
        { Γ := zipTy ps ts, σ := []} (compileSteps prog)
        = TCResult.flows fb ∧ terminal fb = Bool.true
        ∧ (fb.throws = Bool.true
            → complCanThrow (sigCompls sigs name) = Bool.true) := by
  cases hb : checkSeq sigs (sigRetTy sigs name)
      { Γ := zipTy ps ts, σ := []} (compileSteps prog) with
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
    ∀ ts, leTy ts (sigParams sigs name) →
      certifies sigs name ps ts prog

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

def worldLe (w' w : World) : Prop :=
  envLe w'.Γ w.Γ ∧ stackLe w'.σ w.σ

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
              simp only [tmovesV, tagOf] at h₁ h₂ ⊢
              exact decide_eq_true ((of_decide_eq_true h₁).trans (of_decide_eq_true h₂))
          | complN _ | complT | isValue _ | desc _ | notPresent => simp [tmovesV] at h₂
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

theorem worldLe_refl (w : World) : worldLe w w :=
  ⟨envLe_refl w.Γ, stackLe_refl w.σ⟩

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

/-- The payloads of the complN atoms, as one flat type. -/
def payloadsOf (t : Ty) : Ty :=
  t.flatMap (fun a => match a with | .complN p => [p] | _ => [])

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

/- ## Proof layer II: the abstraction commutes with machine pushes -/

/-- frameOk at above = none is exactly frameChecks. -/
theorem frameOk_none_elim {sigs : SigTable} {f : Fr}
    (h : frameOk sigs none f) : frameChecks sigs f := by
  obtain ⟨-, hchk⟩ := h
  exact hchk

theorem frameOk_none_intro {sigs : SigTable} {f : Fr}
    (h : frameChecks sigs f) : frameOk sigs none f :=
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
      = checkSeq sigs r { W with σ := [typeOfV v] :: W.σ } rest := by
  simp only [checkSeq, typeOfE, typeOfV, markThrow_const]


/-- kEval of a nat literal: push the singleton number. -/
theorem checkSeq_kEval_nat {sigs : SigTable} {r : Ty} {W : World} {n : Nat}
    {rest : List Instr} :
    checkSeq sigs r W (.kEval (.nat n) :: rest)
      = checkSeq sigs r
          { W with σ := [VTy.isValue (.number (↑n : Int))] :: W.σ } rest := by
  simp only [checkSeq, typeOfE]
  cases checkSeq sigs r
      { Γ := W.Γ, σ := [VTy.isValue (.number (↑n : Int))] :: W.σ} rest with
  | flows fb => simp only [markThrow, exprCanThrow, Bool.or_false]
  | reject site why => rfl

/-- kEval of a bound variable: push the looked-up (canonical) type. -/
theorem checkSeq_kEval_nv {sigs : SigTable} {r : Ty} {W : World} {x : «String»}
    {v : JSValue} {rest : List Instr}
    (hΓ : tyLookup W.Γ x = some [typeOfV v]) :
    checkSeq sigs r W (.kEval (.nv x) :: rest)
      = checkSeq sigs r { W with σ := [typeOfV v] :: W.σ } rest := by
  simp only [checkSeq, typeOfE, hΓ]
  cases checkSeq sigs r
      { Γ := W.Γ, σ := [typeOfV v] :: W.σ} rest with
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
      = checkSeq sigs r { Γ := (x, ts) :: W.Γ, σ := σ'} rest := by
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
    rename_i sigs r w ty x rest ih1
    intro fb h hf
    rw [checkSeq.eq_18] at h
    exact ih1 fb h hf
  case case23 =>
    rename_i sigs r w nm x rest ih1
    intro fb h hf
    rw [checkSeq.eq_19] at h
    exact ih1 fb h hf
  case case24 =>
    rename_i sigs r w b f x rest hfused ih1
    intro fb h hf
    rw [checkSeq.eq_20, if_pos hfused] at h
    exact ih1 fb h hf
  case case25 =>
    rename_i sigs r w b f x rest hfused hty
    intro fb h hf
    simp only [checkSeq] at h
    split at h
    · next hcond => exact absurd hcond hfused
    · rw [hty] at h
      dsimp only at h
      exact TCResult.noConfusion h
  case case26 =>
    rename_i sigs r w b f x rest hfused S hty ih1
    intro fb h hf
    simp only [checkSeq] at h
    split at h
    · next hcond => exact absurd hcond hfused
    · rw [hty] at h
      dsimp only at h
      exact markThrow_exits h hf ih1
  case case27 =>
    rename_i sigs r w c body rest hempty ps hty hbool ih2 ih1
    intro fb h hf
    simp only [checkSeq, hempty, hty] at h
    split at h
    · cases hbody : checkSeq sigs r w body with
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
    · exact absurd hbool (by assumption)
  case case28 =>
    rename_i sigs r w c body rest hempty ps hty hnt
    intro fb h hf
    simp only [checkSeq, hempty, hty] at h
    split at h
    · next hcond => exact absurd hcond hnt
    · exact TCResult.noConfusion h
  case case29 =>
    rename_i sigs r w c body rest hempty hty
    intro fb h hf
    simp only [checkSeq, hempty, hty] at h
    exact TCResult.noConfusion h
  case case30 =>
    rename_i sigs r w c body rest hne
    intro fb h hf
    cases hσ : w.σ with
    | nil => exact absurd hσ hne
    | cons a as =>
        simp only [checkSeq, hσ] at h
        exact TCResult.noConfusion h
  case case31 =>
    rename_i sigs r w ex rest hdisj hty
    intro fb h hf
    simp only [checkSeq, hty] at h
    exact TCResult.noConfusion h
  case case32 =>
    rename_i sigs r w ex rest hdisj S hty ih1
    intro fb h hf
    simp only [checkSeq, hty] at h
    exact markThrow_exits h hf ih1
  case case33 =>
    rename_i sigs r w x rest f b dec hdec ih1
    intro fb h hf
    rw [checkSeq.eq_23, hdec] at h
    exact forkTC_exits h hf ih1
  case case34 =>
    rename_i sigs r w x rest f b hdec hlook
    intro fb h hf
    rw [checkSeq.eq_23, hdec, hlook] at h
    dsimp only at h
    exact TCResult.noConfusion h
  case case35 =>
    rename_i sigs r w x rest f b hdec S hlook ih1
    intro fb h hf
    rw [checkSeq.eq_23, hdec, hlook] at h
    first
    | exact ih1 fb h hf
    | (dsimp only at h; exact ih1 fb h hf)
    | exact ih1 fb (by dsimp only at h; exact h) hf
  case case36 =>
    rename_i sigs r w x rest dec hdec ih1
    intro fb h hf
    rw [checkSeq.eq_24] at h
    exact forkTC_exits h hf ih1
  case case37 =>
    rename_i sigs r w x rest hdec hlook
    intro fb h hf
    exact absurd hlook (by simp [primDecide])
  case case38 =>
    rename_i sigs r w x rest hdec S hlook ih1
    intro fb h hf
    exact absurd hlook (by simp [primDecide])
  case case39 =>
    rename_i sigs r w x rest dec hdec ih1
    intro fb h hf
    rw [checkSeq.eq_25] at h
    exact forkTC_exits h hf ih1
  case case40 =>
    rename_i sigs r w x rest hdec hlook
    intro fb h hf
    exact absurd hlook (by simp [primDecide])
  case case41 =>
    rename_i sigs r w x rest hdec S hlook ih1
    intro fb h hf
    exact absurd hlook (by simp [primDecide])
  case case42 =>
    rename_i sigs r w x p rest ps hT hpred hn hc ih1
    intro fb h hf
    simp only [checkSeq, hpred, hn, hc, hT] at h
    exact forkTC_exits h hf ih1
  case case43 =>
    rename_i sigs r w x p rest hT hlook hpred hn hc
    intro fb h hf
    simp only [checkSeq, hpred, hn, hc, hT, hlook] at h
    exact TCResult.noConfusion h
  case case44 =>
    rename_i sigs r w x p rest hT S hlook hpred hn hc ih1
    intro fb h hf
    simp only [checkSeq, hpred, hn, hc, hT, hlook] at h
    exact ih1 fb h hf
  case case45 =>
    rename_i sigs r w c body rest hpop
    intro fb h hf
    simp only [checkSeq, hpop] at h
    exact TCResult.noConfusion h
  case case46 =>
    rename_i sigs r w c body rest hpop ih2 ih1
    intro fb h hf
    simp only [checkSeq, hpop] at h
    cases hbody : checkSeq sigs r { Γ := w.Γ, σ := []} body with
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
  case case47 =>
    rename_i sigs r w c body rest hd htl hpop
    intro fb h hf
    simp only [checkSeq, hpop] at h
    exact TCResult.noConfusion h
  case case48 =>
    rename_i sigs r w x body rest hpop
    intro fb h hf
    simp only [checkSeq, hpop] at h
    exact TCResult.noConfusion h
  case case49 =>
    rename_i sigs r w x body rest hpop ih2 ih1
    intro fb h hf
    simp only [checkSeq, hpop] at h
    cases hbody : checkSeq sigs r { Γ := (x, langT) :: w.Γ, σ := []} body with
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
  case case50 =>
    rename_i sigs r w x body rest hd htl hpop
    intro fb h hf
    simp only [checkSeq, hpop] at h
    exact TCResult.noConfusion h
  case case51 =>
    rename_i sigs r w x elems body rest hempty ih2 ih1
    intro fb h hf
    simp only [checkSeq, hempty] at h
    cases hbody : checkSeq sigs r { Γ := (x, langT) :: w.Γ, σ := [] } body with
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
  case case52 =>
    rename_i sigs r w x elems body rest hne
    intro fb h hf
    cases hσ : w.σ with
    | nil => exact absurd hσ hne
    | cons a as =>
        simp only [checkSeq, hσ] at h
        exact TCResult.noConfusion h
  case case53 =>
    rename_i sigs r w rest hσ
    intro fb h hf
    simp only [checkSeq, hσ] at h
    exact TCResult.noConfusion h
  case case54 =>
    rename_i sigs r w rest ts σ' hσ ih1
    intro fb h hf
    simp only [checkSeq, hσ] at h
    obtain ⟨-, heq⟩ := fold_merge_flows _ ts vacOk (ne_reject_of_flows h)
    rw [heq] at h
    have hinj := TCResult.flows.inj h
    subst hinj
    rfl
  case case55 =>
    rename_i sigs r w i rest hdisj hstep
    intro fb h hf
    simp only [checkSeq, hstep] at h
    exact TCResult.noConfusion h
  case case56 =>
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
  simp only [checkSeq, step1, hσ, complNormals, complHasThrow, List.filterMap_cons, List.filterMap_nil, List.any_cons, List.any_nil, Bool.true_or, List.isEmpty_cons, ite_true, if_true, Bool.false_or, Bool.true_and, List.cons_append, List.nil_append, forkTC, List.foldl, mergeTC_noFlows]

theorem checkSeq_kTest_throw {sigs : SigTable} {r : Ty} {W : World}
    {σ' : List Ty} {rest : List Instr} (hσ : W.σ = [VTy.complT] :: σ') :
    checkSeq sigs r W (.kTest :: rest)
      = checkSeq sigs r { W with σ := [.isValue (.boolean Bool.true)] :: [VTy.complT] :: σ' } rest := by
  simp only [checkSeq, step1, hσ, complNormals, complHasThrow, List.filterMap_cons, List.filterMap_nil, List.any_cons, List.any_nil, Bool.true_or, List.isEmpty_cons, ite_true, if_true, Bool.false_or, Bool.true_and, List.cons_append, List.nil_append, forkTC, List.foldl, mergeTC_noFlows]

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
  simp only [checkSeq, step1, hσ, bareSlot, hbar, Option.map_some, List.map,
    forkTC, List.foldl, mergeTC_noFlows]

theorem checkSeq_pThrowC {sigs : SigTable} {r : Ty} {W : World} {v : JSValue}
    {σ' : List Ty} {rest : List Instr} (hσ : W.σ = [typeOfV v] :: σ') :
    checkSeq sigs r W (.kPrim1 .pThrowC :: rest)
      = checkSeq sigs r { W with σ := [VTy.complT] :: σ' } rest := by
  simp only [checkSeq, step1, hσ, complNormals, complHasThrow, List.filterMap_cons, List.filterMap_nil, List.any_cons, List.any_nil, Bool.true_or, List.isEmpty_cons, ite_true, if_true, Bool.false_or, Bool.true_and, List.cons_append, List.nil_append, forkTC, List.foldl, mergeTC_noFlows]

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
theorem sr_kIte_loud {sigs : SigTable} {t e : List Instr} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»} {v : JSValue}
    (hv : ∀ b, v ≠ JSValue.boolean b)
    (h : frameOk sigs none ⟨.kIte t e :: rest, env, v :: eval, ret⟩) : False := by
  obtain ⟨-, hchk⟩ := h
  rw [frameChecks] at hchk
  simp only [frameWorld, List.map_cons] at hchk
  have hrej : checkSeq sigs (sigRetTy sigs ret)
      { Γ := envTyOf env, σ := [typeOfV v] :: eval.map (fun v => [typeOfV v])} (.kIte t e :: rest)
      = TCResult.reject (.kIte t e) "kIte: verdict is not boolean" := by
    cases v with
    | undefined => simp only [checkSeq, typeOfV, List.foldl, vacOk, mergeTC]
    | null => simp only [checkSeq, typeOfV, List.foldl, vacOk, mergeTC]
    | boolean b => exact absurd rfl (hv b)
    | number n => simp only [checkSeq, typeOfV, List.foldl, vacOk, mergeTC]
    | str s => simp only [checkSeq, typeOfV, List.foldl, vacOk, mergeTC]
    | listV l => simp only [checkSeq, typeOfV, List.foldl, vacOk, mergeTC]
    | obj o => simp only [checkSeq, typeOfV, List.foldl, vacOk, mergeTC]
    | descV d => simp only [checkSeq, typeOfV, List.foldl, vacOk, mergeTC]
    | compl b pv =>
        cases b <;> simp only [checkSeq, typeOfV, List.foldl, vacOk, mergeTC]
  rw [hrej] at hchk
  exact hchk

/- ## Proof layer XVII: frameTyped (the type-machine judgement) and
    its step transfers. The abstraction function is frameWorld
    (defined with the bridge, above). -/

/-- The type machine accepts the abstracted frame: every
    exploration path returns inside r. -/
def frameTyped (sigs : SigTable) (r : Ty) (f : Fr) : Prop :=
  match checkSeq sigs r (frameWorld f) f.stmts with
  | .flows fb => terminal fb = Bool.true  -- every world returns
  | _ => False

theorem frameTyped_eq_frameChecks (sigs : SigTable) (f : Fr) :
    frameTyped sigs (sigRetTy sigs f.ret) f = frameChecks sigs f := rfl

/-- kIte transfer: dispatching the singleton verdict atom equals the
    machine's jump. -/
theorem frameTyped_kIte {sigs : SigTable} {b : Bool} {t e : List Instr}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»} {r : Ty}
    (h : frameTyped sigs r ⟨.kIte t e :: rest, env, .boolean b :: eval, ret⟩) :
    frameTyped sigs r ⟨(if b then t else e) ++ rest, env, eval, ret⟩ := by
  simp only [frameTyped, frameWorld, Fr.stmts, Fr.env, Fr.eval, List.map_cons] at h ⊢
  cases hb : b with
  | true =>
      rw [hb] at h
      have hslot : [typeOfV (JSValue.boolean Bool.true)]
          = [VTy.isValue (JSValue.boolean Bool.true)] := rfl
      rw [hslot] at h
      rw [checkSeq_kIte_true rfl] at h
      rw [if_pos rfl]
      cases hres : checkSeq sigs r
          { Γ := envTyOf env, σ := eval.map (fun v => [typeOfV v]) } (t ++ rest) with
      | reject s w =>
          have hrej : mergeTC vacOk (TCResult.reject s w) = TCResult.reject s w := rfl
          rw [hres, hrej] at h
          exact h.elim
      | flows fbr =>
          cases hm : mergeTC vacOk (checkSeq sigs r
              { Γ := envTyOf env, σ := eval.map (fun v => [typeOfV v]) } (t ++ rest)) with
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
      have hslot : [typeOfV (JSValue.boolean Bool.false)]
          = [VTy.isValue (JSValue.boolean Bool.false)] := rfl
      rw [hslot] at h
      rw [checkSeq_kIte_false rfl] at h
      rw [if_neg (by decide)]
      cases hres : checkSeq sigs r
          { Γ := envTyOf env, σ := eval.map (fun v => [typeOfV v]) } (e ++ rest) with
      | reject s w =>
          have hrej : mergeTC vacOk (TCResult.reject s w) = TCResult.reject s w := rfl
          rw [hres, hrej] at h
          exact h.elim
      | flows fbr =>
          cases hm : mergeTC vacOk (checkSeq sigs r
              { Γ := envTyOf env, σ := eval.map (fun v => [typeOfV v]) } (e ++ rest)) with
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
theorem frameTyped_kIte_reject_nil {sigs : SigTable} {r : Ty} {t e : List Instr}
    {rest : List Instr} {env : Env} {ret : «String»} :
    frameTyped sigs r ⟨.kIte t e :: rest, env, [], ret⟩ = False := by
  simp only [frameTyped, frameWorld, List.map, checkSeq]

theorem frameTyped_kIte_reject_nonbool {sigs : SigTable} {r : Ty} {t e : List Instr}
    {rest : List Instr} {env : Env} {eval' : List JSValue} {ret : «String»} {v : JSValue}
    (hv : ∀ b, v ≠ JSValue.boolean b) :
    frameTyped sigs r ⟨.kIte t e :: rest, env, v :: eval', ret⟩ = False := by
  cases v with
  | boolean b => exact absurd rfl (hv b)
  | undefined | null | number _ | str _ | obj _ | listV _ | descV _ =>
      simp only [frameTyped, frameWorld, List.map, List.map_cons, typeOfV, checkSeq,
        List.foldl_cons, List.foldl_nil, mergeTC]
      rfl
  | compl a b =>
      cases a <;>
        simp only [frameTyped, frameWorld, List.map, List.map_cons, typeOfV, checkSeq,
          List.foldl_cons, List.foldl_nil, mergeTC]
      all_goals rfl

/-- kPop transfer. -/
theorem frameTyped_kPop {sigs : SigTable} {w : JSValue} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»} {r : Ty}
    (h : frameTyped sigs r ⟨.kPop :: rest, env, w :: eval, ret⟩) :
    frameTyped sigs r ⟨rest, env, eval, ret⟩ := by
  simp only [frameTyped, frameWorld, Fr.stmts, Fr.env, Fr.eval, List.map_cons] at h ⊢
  rw [checkSeq_kPop rfl] at h
  exact h

theorem frameTyped_kPop_reject_nil {sigs : SigTable} {r : Ty} {rest : List Instr}
    {env : Env} {ret : «String»} :
    frameTyped sigs r ⟨.kPop :: rest, env, [], ret⟩ = False := by
  simp only [frameTyped, frameWorld, List.map, checkSeq, step1]

/-- kSet transfer. -/
theorem frameTyped_kSet {sigs : SigTable} {x : «String»} {w : JSValue} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»} {r : Ty}
    (h : frameTyped sigs r ⟨.kSet x :: rest, env, w :: eval, ret⟩) :
    frameTyped sigs r ⟨rest, (x, w) :: env, eval, ret⟩ := by
  simp only [frameTyped, frameWorld, Fr.stmts, Fr.env, Fr.eval, List.map_cons] at h ⊢
  rw [checkSeq_kSet rfl] at h
  rw [envTyOf_cons]
  exact h

theorem frameTyped_kSet_reject_nil {sigs : SigTable} {r : Ty} {x : «String»} {rest : List Instr}
    {env : Env} {ret : «String»} :
    frameTyped sigs r ⟨.kSet x :: rest, env, [], ret⟩ = False := by
  simp only [frameTyped, frameWorld, List.map, checkSeq, step1]

/-- kEval of a literal — ALL value shapes (compl literals use the
    checker's dedicated push arms; everything else the generic one). -/
theorem frameTyped_kEval_const {sigs : SigTable} {v : JSValue} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»} {r : Ty}
    (h : frameTyped sigs r ⟨.kEval (.const v) :: rest, env, eval, ret⟩) :
    frameTyped sigs r ⟨rest, env, v :: eval, ret⟩ := by
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
def frameOkUnder (sigs : SigTable) (callee : «String») (f : Fr) : Prop :=
  match checkSeq sigs (sigRetTy sigs f.ret)
    { Γ := envTyOf f.env,
      σ := complTy (sigCompls sigs callee) :: f.eval.map (fun v => [typeOfV v]) }
    f.stmts with
  | .flows fb => terminal fb = Bool.true
  | _ => False

/-- Each frame at its own destiny; the frame under f anticipates
    f's declared completions. -/
def framesTypedFrom (sigs : SigTable) (above : Option «String») : List Fr → Prop
  | [] => True
  | f :: fs =>
      (match above with
       | none => frameChecks sigs f
       | some n => frameOkUnder sigs n f)
      ∧ framesTypedFrom sigs (some f.ret) fs

/-- The type machine's judgment on a WHOLE value state: every frame
    typed (heads at own destinies, under-callees anticipated), the
    bottom frame's destiny = r, the final answer inside r, stuck
    states untyped. -/
def stateTyped (sigs : SigTable) (r : Ty) (m : FM) : Prop :=
  match m with
  | .frames [] _ _ => False
  | .frames (f :: fs) _ _ =>
      framesTypedFrom sigs none (f :: fs) ∧ machineRet sigs (f :: fs) = r
  | .fdone v _ _ _ _ => tmoves [typeOfV v] r = Bool.true
  | .fell _ _ _ _ => False

/-- THE SR PREDICATE — one shape; every arm theorem instantiates it.
    The registry premise is part of the predicate: the callee's
    body is the one thing the caller's check never sees, so the
    kCall arm draws its post-frame typing from the registry's
    certificates. -/

def SR_arm (sigs : SigTable) (reg : AOReg) (h : Instr) (s : FM) (r : Ty) : Prop :=
  registryCertified sigs reg →
    stateTyped sigs r (withHead h s) →
      stateTyped sigs r (fstep reg (withHead h s))

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
theorem envTyOf_zipTy : ∀ (ps : List «String») (vs : List JSValue),
    envTyOf (ps.zip vs) = zipTy ps (vs.map (fun v => [typeOfV v])) := by
  intro ps
  induction ps with
  | nil => intro vs; cases vs <;> simp [envTyOf, zipTy]
  | cons p pst ih =>
      intro vs
      cases vs with
      | nil => simp [List.zip, envTyOf, zipTy]
      | cons v vt =>
          show envTyOf ((p, v) :: pst.zip vt)
            = (p, [typeOfV v]) :: zipTy pst (vt.map (fun v => [typeOfV v]))
          rw [envTyOf_cons, ih]

/-- The kIte arm. -/
theorem SR_kIte (sigs : SigTable) (reg : AOReg) (t e : List Instr) (s : FM) (r : Ty) :
    SR_arm sigs reg (.kIte t e) s r := by
  intro _ hpre
  cases s with
  | fdone v fs heap nl n => exact hpre
  | fell fs heap nl n => exact hpre
  | frames fs heap nl =>
      cases fs with
      | nil => exact hpre
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases eval with
          | nil =>
              have h1 : frameTyped sigs (sigRetTy sigs ret)
                  ⟨.kIte t e :: stmts, env, [], ret⟩ := hpre.1.1
              rw [frameTyped_kIte_reject_nil] at h1
              exact h1.elim
          | cons v eval' =>
              cases v with
              | boolean b =>
                  refine ⟨⟨frameTyped_kIte hpre.1.1, hpre.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2
              | undefined =>
                  exfalso
                  have h1 : frameTyped sigs (sigRetTy sigs ret)
                      ⟨.kIte t e :: stmts, env, .undefined :: eval', ret⟩ := hpre.1.1
                  rw [frameTyped_kIte_reject_nonbool
                    (by intro b hb; exact JSValue.noConfusion hb)] at h1
                  exact h1.elim
              | null =>
                  exfalso
                  have h1 : frameTyped sigs (sigRetTy sigs ret)
                      ⟨.kIte t e :: stmts, env, .null :: eval', ret⟩ := hpre.1.1
                  rw [frameTyped_kIte_reject_nonbool
                    (by intro b hb; exact JSValue.noConfusion hb)] at h1
                  exact h1.elim
              | number m =>
                  exfalso
                  have h1 : frameTyped sigs (sigRetTy sigs ret)
                      ⟨.kIte t e :: stmts, env, .number m :: eval', ret⟩ := hpre.1.1
                  rw [frameTyped_kIte_reject_nonbool
                    (by intro b hb; exact JSValue.noConfusion hb)] at h1
                  exact h1.elim
              | str m =>
                  exfalso
                  have h1 : frameTyped sigs (sigRetTy sigs ret)
                      ⟨.kIte t e :: stmts, env, .str m :: eval', ret⟩ := hpre.1.1
                  rw [frameTyped_kIte_reject_nonbool
                    (by intro b hb; exact JSValue.noConfusion hb)] at h1
                  exact h1.elim
              | obj m =>
                  exfalso
                  have h1 : frameTyped sigs (sigRetTy sigs ret)
                      ⟨.kIte t e :: stmts, env, .obj m :: eval', ret⟩ := hpre.1.1
                  rw [frameTyped_kIte_reject_nonbool
                    (by intro b hb; exact JSValue.noConfusion hb)] at h1
                  exact h1.elim
              | listV m =>
                  exfalso
                  have h1 : frameTyped sigs (sigRetTy sigs ret)
                      ⟨.kIte t e :: stmts, env, .listV m :: eval', ret⟩ := hpre.1.1
                  rw [frameTyped_kIte_reject_nonbool
                    (by intro b hb; exact JSValue.noConfusion hb)] at h1
                  exact h1.elim
              | descV m =>
                  exfalso
                  have h1 : frameTyped sigs (sigRetTy sigs ret)
                      ⟨.kIte t e :: stmts, env, .descV m :: eval', ret⟩ := hpre.1.1
                  rw [frameTyped_kIte_reject_nonbool
                    (by intro b hb; exact JSValue.noConfusion hb)] at h1
                  exact h1.elim
              | compl a b =>
                  exfalso
                  have h1 : frameTyped sigs (sigRetTy sigs ret)
                      ⟨.kIte t e :: stmts, env, .compl a b :: eval', ret⟩ := hpre.1.1
                  rw [frameTyped_kIte_reject_nonbool
                    (by intro b hb; exact JSValue.noConfusion hb)] at h1
                  exact h1.elim

/-- The kPop arm. -/
theorem SR_kPop (sigs : SigTable) (reg : AOReg) (s : FM) (r : Ty) :
    SR_arm sigs reg .kPop s r := by
  intro _ hpre
  cases s with
  | fdone v fs heap nl n => exact hpre
  | fell fs heap nl n => exact hpre
  | frames fs heap nl =>
      cases fs with
      | nil => exact hpre
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases eval with
          | nil =>
              have h1 : frameTyped sigs (sigRetTy sigs ret)
                  ⟨.kPop :: stmts, env, [], ret⟩ := hpre.1.1
              rw [frameTyped_kPop_reject_nil] at h1
              exact h1.elim
          | cons w eval' =>
              refine ⟨⟨frameTyped_kPop hpre.1.1, hpre.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2

/-- The kSet arm. -/
theorem SR_kSet (sigs : SigTable) (reg : AOReg) (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kSet x) s r := by
  intro _ hpre
  cases s with
  | fdone v fs heap nl n => exact hpre
  | fell fs heap nl n => exact hpre
  | frames fs heap nl =>
      cases fs with
      | nil => exact hpre
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases eval with
          | nil =>
              have h1 : frameTyped sigs (sigRetTy sigs ret)
                  ⟨.kSet x :: stmts, env, [], ret⟩ := hpre.1.1
              rw [frameTyped_kSet_reject_nil] at h1
              exact h1.elim
          | cons w eval' =>
              refine ⟨⟨frameTyped_kSet hpre.1.1, hpre.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2

/-- The kEval-const arm (a pushing arm; all value shapes). -/
theorem SR_kEval_const (sigs : SigTable) (reg : AOReg) (v : JSValue) (s : FM) (r : Ty) :
    SR_arm sigs reg (.kEval (.const v)) s r := by
  intro _ hpre
  cases s with
  | fdone v' fs heap nl n => exact hpre
  | fell fs heap nl n => exact hpre
  | frames fs heap nl =>
      cases fs with
      | nil => exact hpre
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          refine ⟨⟨frameTyped_kEval_const hpre.1.1, hpre.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2

/- ## kCall roadmap (the arm this shape was built for)

    Post = callee :: callerPost :: fs' (registry hit), and the
    obligations map exactly onto the existing machinery:
    1. callee frameChecks = certifies sigs fname ps' ts body at
       ts := (eval.take n).reverse.map singleton — leTy ts params
       from the checker's popArgs (via map_take/reverse_map), the
       callee's Γ = envTyOf (ps'.zip …) = zipTy ps' ts
       (envTyOf_zipTy).
    2. callerPost frameOkUnder fname — VERBATIM the checker's kCall
       arm: it pushed complTy (sigCompls fname) onto σ.drop n; the
       bridge lemma is checkSeq_kCall_inv (the inversion of the
       catch-all + step1's single-world kCall).
    3. machineRet — cons_cons + head_swap.
    4. Vacuous arms: underflow (popArgs rejects), unknown callee
       (sigFind none → checker rejects), reg-miss non-native
       (closedRegistry). The reg-miss NATIVE arm needs either the
       native names answered by the registry (a completeness
       premise) or the refinement lemma (anticipated union →
       native singleton) — the same monotonicity kRet needs. -/

/- ## Next: the specialization capstone (pointwise)

    theorem checkSeq_specialize : ∀ seq w w', worldLe w' w →
      tterm (checkSeq sigs r w seq) → tterm (checkSeq sigs r w' seq)

    Induction on seq; each arm pointwise: kRet (pending payload ⊑
    via pendLe), kIte (verdict dispatch forks a both-verdict world —
    both sides covered), splits (split1_cov), the catch-all (step1_mono
    + a fold-terminality lift: every refined world's check terminal
    because its coarse cover's is; the fold merges exits/disj,
    falls/append — terminal iff every element exits with no falls;
    step1 outputs are nonempty). Loop joins: ⊑-neutrality per path.
    -/
