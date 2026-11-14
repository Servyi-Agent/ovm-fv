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
    -- the certificate is at every PREFIX typing that the checker may
    -- pass: kCall accepts an n+1-parameter callee called with n
    -- arguments (the optional trailing parameter stays unbound), so
    -- the argument typing covers a prefix of the declared parameters.
    ∀ ts, ts.length ≤ (sigParams sigs name).length →
      leTy ts ((sigParams sigs name).take ts.length) →
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


theorem typeOfE_cov (sigs : SigTable) (Γ' Γ : TyEnv) :
    ∀ (e : Expr), envLe Γ' Γ →
      ∀ t, typeOfE sigs Γ e = some t →
        ∃ t', typeOfE sigs Γ' e = some t' ∧ slotLe t' t := by
  intro e
  induction e using typeOfE.induct (sigs := sigs) (Γ := Γ)
    (motive1 := fun es => envLe Γ' Γ →
      ∀ ts, typesOf sigs Γ es = some ts →
        ∃ ts', typesOf sigs Γ' es = some ts' ∧ slotsLe ts' ts) with
  | case1 =>
      rename_i _ ts ht
      simp only [typesOf] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      exact ⟨[], by simp [typesOf], True.intro⟩

  | case2 =>
      rename_i x xs t0 ts0 hxs hx ih2 ih1 hle ts ht
      simp only [typesOf, hx, hxs, Option.some.injEq] at ht
      subst ht
      obtain ⟨tx', htx', hslotx⟩ := ih2 hle t0 hx
      obtain ⟨txs', htxs', hslotxs⟩ := ih1 hle ts0 hxs
      exact ⟨tx' :: txs', by
        simp only [typesOf, htx', htxs'], hslotx, hslotxs⟩

  | case3 =>
      rename_i x xs hcontra ih2 ih1 hle ts ht
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
      intro hle t ht
      simp only [typeOfE] at ht
      obtain ⟨t', ht', hle', hne'⟩ := envLe_lookup_cov_full hle ht
      exact ⟨t', by simp only [typeOfE]; exact ht', hle', hne'⟩

  | case5 =>
      intro _ t ht
      refine ⟨t, ?_, slotLe_refl t⟩
      simp only [typeOfE] at ht ⊢
      exact ht

  | case6 =>
      intro _ t ht
      refine ⟨t, ?_, slotLe_refl t⟩
      simp only [typeOfE] at ht ⊢
      exact ht

  | case7 =>
      intro _ t ht
      refine ⟨t, ?_, slotLe_refl t⟩
      simp only [typeOfE] at ht ⊢
      exact ht

  | case8 =>
      intro _ t ht
      refine ⟨t, ?_, slotLe_refl t⟩
      simp only [typeOfE] at ht ⊢
      exact ht

  | case9 =>
      intro _ t ht
      refine ⟨t, ?_, slotLe_refl t⟩
      simp only [typeOfE] at ht ⊢
      exact ht

  | case10 =>
      intro _ t ht
      refine ⟨t, ?_, slotLe_refl t⟩
      simp only [typeOfE] at ht ⊢
      exact ht

  | case11 =>
      rename_i e ps hps ih
      intro hle t ht
      simp only [typeOfE, hps] at ht
      cases hpay : payloadOf ps with
      | none => rw [hpay] at ht; simp at ht
      | some psv =>
          rw [hpay] at ht
          simp only [Option.some.injEq] at ht
          subst ht
          obtain ⟨ps', hps', hslot⟩ := ih hle ps hps
          obtain ⟨t', ht', hslot'⟩ := payloadOf_cov hslot hpay
          exact ⟨t', by simp only [typeOfE, hps', ht'], hslot'⟩

  | case12 =>
      rename_i e hnone ih
      intro _ t ht
      simp only [typeOfE, hnone] at ht
      exact absurd ht (by simp)

  | case13 =>
      rename_i e ps hps ih
      intro hle t ht
      simp only [typeOfE, hps] at ht
      cases hb : bareOf ps with
      | none => rw [hb] at ht; simp at ht
      | some bs =>
          rw [hb] at ht
          simp only [Option.map_some, Option.some.injEq] at ht
          subst ht
          obtain ⟨ps', hps', hslot⟩ := ih hle ps hps
          obtain ⟨hb', hbs'⟩ := bareOf_cov hslot hb
          exact ⟨ps'.map VTy.complN, by
            simp only [typeOfE, hps', hb', Option.map_some],
            complN_map_cov hbs'⟩

  | case14 =>
      rename_i e hnone ih
      intro _ t ht
      simp only [typeOfE, hnone] at ht
      exact absurd ht (by simp)

  | case15 =>
      rename_i f as ps snd hsig ts hts hguard ih1
      intro hle t ht
      simp only [typeOfE, hsig, hts] at ht
      rw [if_pos hguard] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      obtain ⟨ts', hts', hslots⟩ := ih1 hle ts hts
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
        simp only [typeOfE, hsig, hts', if_pos hguard'], slotLe_refl _⟩

  | case16 =>
      rename_i f as ps snd hsig ts hts hguard ih1
      intro _ t ht
      rw [show typeOfE sigs Γ (.call f as) = none from by
        simp only [typeOfE, hsig, hts, if_neg hguard]] at ht
      exact absurd ht (by simp)

  | case17 =>
      rename_i f as ps snd hsig hnone ih1
      intro _ t ht
      rw [show typeOfE sigs Γ (.call f as) = none from by
        simp only [typeOfE, hsig, hnone]] at ht
      exact absurd ht (by simp)

  | case18 =>
      rename_i f as hsig
      intro _ t ht
      simp only [typeOfE, hsig] at ht
      exact absurd ht (by simp)

  | case19 =>
      rename_i nm recv args k harity hguard ih2 ih1
      intro hle t ht
      rw [Bool.and_eq_true] at hguard
      obtain ⟨hAB, h3⟩ := hguard
      rw [Bool.and_eq_true] at hAB
      obtain ⟨h1, h2⟩ := hAB
      cases hrecv : typeOfE sigs Γ recv with
      | none => rw [hrecv] at h2; simp at h2
      | some tr =>
          rw [hrecv] at h2
          simp only at h2
          obtain ⟨tr', htr', hslotr⟩ := ih2 hle tr hrecv
          have h2' : (match typeOfE sigs Γ' recv with
              | some t2 => tmoves t2 [VTy.anyValue Ctor.obj]
              | none => Bool.false) = Bool.true := by
            rw [htr']
            exact tmoves_trans hslotr.1 h2
          have htr'move : tmoves tr' [VTy.anyValue Ctor.obj] = Bool.true :=
            tmoves_trans hslotr.1 h2
          have h3' : (typesOf sigs Γ' args).isSome = Bool.true := by
            cases hc : typesOf sigs Γ args with
            | none => rw [hc] at h3; simp at h3
            | some sv =>
                obtain ⟨sv', hsv', _⟩ := ih1 hle sv hc
                rw [hsv']
                rfl
          have hguard' : ((args.length == k &&
              (match typeOfE sigs Γ' recv with
              | some t2 => tmoves t2 [VTy.anyValue Ctor.obj]
              | none => Bool.false)) && (typesOf sigs Γ' args).isSome)
              = Bool.true :=
            by
              simp only [htr', htr'move, h1, h3', Bool.true_and, Bool.and_true]
          simp only [typeOfE, harity] at ht
          rw [if_pos (by
            simp only [hrecv, h1, h2, h3, Bool.true_and, Bool.and_true])] at ht
          simp only [Option.some.injEq] at ht
          subst ht
          refine ⟨mopPayload nm, ?_, slotLe_refl _⟩
          rw [show typeOfE sigs Γ' (Expr.imeth nm recv args)
              = some (mopPayload nm) from by
            simp only [typeOfE, harity, htr', htr'move, h1, h3',
              Bool.true_and, Bool.and_true, if_true]]

  | case20 =>
      rename_i nm recv args k harity hguard ih2 ih1
      intro _ t ht
      simp only [typeOfE, harity] at ht
      rw [if_neg hguard] at ht
      exact absurd ht (by simp)

  | case21 =>
      rename_i nm recv args hnone
      intro _ t ht
      simp only [typeOfE, hnone] at ht
      exact absurd ht (by simp)

  | case22 =>
      rename_i nm x hval ps1 hx1 ps hpay ih
      intro hle t ht
      simp only [typeOfE, if_pos hval, hx1, hpay] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      obtain ⟨ps1', hx1', hslot⟩ := ih hle ps1 hx1
      obtain ⟨ps', hpay', hslot'⟩ := payloadOf_cov hslot hpay
      exact ⟨ps', by
        simp only [typeOfE, if_pos hval, hx1', hpay'], hslot'⟩

  | case23 =>
      rename_i nm x hval ps1 hx1 hpnone ih
      intro hle t ht
      simp only [typeOfE, if_pos hval, hx1, hpnone] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      obtain ⟨ps1', hx1', hslot⟩ := ih hle ps1 hx1
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
            simp only [typeOfE, if_pos hval, hx1', hpay'], ?_⟩
          refine ⟨?_, ?_⟩
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
      | none =>
          refine ⟨payloadsOf ps1' ++ mopPayload nm, by
            simp only [typeOfE, if_pos hval, hx1', hpay'], ?_⟩
          refine ⟨?_, ?_⟩
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

  | case24 =>
      rename_i nm x hval hnone ih
      intro _ t ht
      simp only [typeOfE, if_pos hval, hnone] at ht
      exact absurd ht (by simp)

  | case25 =>
      rename_i nm x hnv hsame ih
      intro hle t ht
      simp only [typeOfE, if_neg hnv, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle sv hc
            rw [hsv']
            rfl
      exact ⟨mopPayload nm, by
        simp only [typeOfE, if_neg hnv, if_pos hx'], slotLe_refl _⟩

  | case26 =>
      rename_i nm x hnv hnone ih
      intro _ t ht
      simp only [typeOfE, if_neg hnv] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case27 =>
      rename_i es hsame ih1
      intro hle t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typesOf sigs Γ' es).isSome = Bool.true := by
        cases hc : typesOf sigs Γ es with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih1 hle sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .list], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _⟩

  | case28 =>
      rename_i es hnone ih1
      intro _ t ht
      simp only [typeOfE] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case29 =>
      rename_i x ps hx hobj ih
      intro hle t ht
      simp only [typeOfE, hx, if_pos hobj] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      obtain ⟨ps', hx', hslot⟩ := ih hle ps hx
      refine ⟨[.isValue (.boolean Bool.true)], ?_, slotLe_refl _⟩
      simp only [typeOfE, hx']
      rw [if_pos (show tmoves ps' [VTy.anyValue Ctor.obj] = Bool.true
        from tmoves_trans hslot.1 hobj)]

  | case30 =>
      rename_i x ps hx hnobj hf ih
      exfalso
      rw [Bool.and_eq_true] at hf
      obtain ⟨hrne, hpne⟩ := hf
      have hnil : removeTy ps [VTy.anyValue Ctor.obj] = [] := by
        simpa using hrne
      exact absurd (removeTy_nil_imp
        (t := ps) (T := [.anyValue .obj]) (by
          intro b hb
          cases b <;> simp_all [List.mem_singleton])
        hnil) hnobj

  | case31 =>
      rename_i x ps hx hnobj hnf ih
      intro hle t ht
      simp only [typeOfE, hx, if_neg hnobj, if_neg hnf] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      obtain ⟨ps', hx', hslot⟩ := ih hle ps hx
      by_cases h1 : tmoves ps' [VTy.anyValue Ctor.obj] = Bool.true
      · refine ⟨[.isValue (.boolean Bool.true)], ?_,
          ⟨isObject_result_le _ (Or.inl rfl), by intro _; simp⟩⟩
        simp only [typeOfE, hx']
        rw [if_pos h1]
      · by_cases h2 : (List.isEmpty (removeTy ps' [VTy.anyValue Ctor.obj])
            && !List.isEmpty ps') = Bool.true
        · refine ⟨[.isValue (.boolean Bool.false)], ?_,
            ⟨isObject_result_le _ (Or.inr (Or.inl rfl)), by intro _; simp⟩⟩
          simp only [typeOfE, hx']
          rw [if_neg h1, if_pos h2]
        · refine ⟨[.anyValue .bool], ?_, slotLe_refl _⟩
          simp only [typeOfE, hx']
          rw [if_neg h1, if_neg h2]

  | case32 =>
      rename_i x hnone ih
      intro _ t ht
      simp only [typeOfE, hnone] at ht
      exact absurd ht (by simp)

  | case33 =>
      rename_i x hsame ih
      intro hle t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .bool], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _⟩

  | case34 =>
      rename_i x hnone ih
      intro _ t ht
      simp only [typeOfE] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case35 =>
      rename_i x hsame ih
      intro hle t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .bool], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _⟩

  | case36 =>
      rename_i x hnone ih
      intro _ t ht
      simp only [typeOfE] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case37 =>
      rename_i x hsame ih
      intro hle t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .bool], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _⟩

  | case38 =>
      rename_i x hnone ih
      intro _ t ht
      simp only [typeOfE] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case39 =>
      rename_i x hsame ih
      intro hle t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .bool], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _⟩

  | case40 =>
      rename_i x hnone ih
      intro _ t ht
      simp only [typeOfE] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case41 =>
      rename_i x hsame ih
      intro hle t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .bool], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _⟩

  | case42 =>
      rename_i x hnone ih
      intro _ t ht
      simp only [typeOfE] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case43 =>
      rename_i b x hsame ih
      intro hle t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .bool], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _⟩

  | case44 =>
      rename_i b x hnone ih
      intro _ t ht
      simp only [typeOfE] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case45 =>
      rename_i s x hsame ih
      intro hle t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .bool], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _⟩

  | case46 =>
      rename_i s x hnone ih
      intro _ t ht
      simp only [typeOfE] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case47 =>
      rename_i x hsame ih
      intro hle t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .bool], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _⟩

  | case48 =>
      rename_i x hnone ih
      intro _ t ht
      simp only [typeOfE] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case49 =>
      rename_i x hsame ih
      intro hle t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .bool], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _⟩

  | case50 =>
      rename_i x hnone ih
      intro _ t ht
      simp only [typeOfE] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case51 =>
      rename_i ty x hsame ih
      intro hle t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .bool], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _⟩

  | case52 =>
      rename_i ty x hnone ih
      intro _ t ht
      simp only [typeOfE] at ht
      rw [if_neg hnone] at ht
      exact absurd ht (by simp)

  | case53 =>
      rename_i name x hsame ih
      intro hle t ht
      simp only [typeOfE, if_pos hsame] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      have hx' : (typeOfE sigs Γ' x).isSome = Bool.true := by
        cases hc : typeOfE sigs Γ x with
        | none => rw [hc] at hsame; simp at hsame
        | some sv =>
            obtain ⟨sv', hsv', _⟩ := ih hle sv hc
            rw [hsv']
            rfl
      exact ⟨[.anyValue .bool], by
        simp only [typeOfE, if_pos hx'], slotLe_refl _⟩

  | case54 =>
      rename_i name x hnone ih
      intro _ t ht
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
      | undef | null | bool | num | str | obj | list =>
          exact absurd hm' (by simp [meetAtom])
  | undef | null | bool | num | str | obj | list =>
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

theorem step1_cov (sigs : SigTable) (i : Instr) :
    ∀ (w' w : World), worldLe w' w → ∀ ws, step1 sigs i w = some ws →
      ∃ ws', step1 sigs i w' = some ws' ∧
        ∀ u' ∈ ws', ∃ u ∈ ws, worldLe u' u := by
  intro w' w hwl ws hstep
  obtain ⟨Γ', σ'⟩ := w'
  obtain ⟨Γ, σ⟩ := w
  obtain ⟨hΓ, hσ⟩ := hwl
  cases i with
  | kEval e | kIte t e | kRet | kAssert | kTestVar x p
  | kRepeatWhile c b | kRepeatTest c b | kForStart x b | kForBody x l b =>
      simp only [step1, Option.some.injEq] at hstep
      subst hstep
      refine ⟨(⟨Γ', σ'⟩ : World) :: [], rfl, ?_⟩
      intro u' hu'
      simp only [List.mem_singleton] at hu'
      subst hu'
      exact ⟨⟨Γ, σ⟩, List.mem_singleton.mpr rfl, hΓ, hσ⟩
  | kPop =>
      cases σ with
      | nil => exact absurd hstep (by simp [step1])
      | cons t σr =>
          cases σ' with
          | nil => exact absurd hσ (by simp [stackLe])
          | cons t' σr' =>
              simp only [step1, Option.some.injEq] at hstep
              subst hstep
              refine ⟨(⟨Γ', σr'⟩ : World) :: [], rfl, ?_⟩
              intro u' hu'
              simp only [List.mem_singleton] at hu'
              subst hu'
              exact ⟨⟨Γ, σr⟩, List.mem_singleton.mpr rfl, hΓ, hσ.2⟩
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
              refine ⟨(⟨(x, t') :: Γ', σr'⟩ : World) :: [], rfl, ?_⟩
              intro u' hu'
              simp only [List.mem_singleton] at hu'
              subst hu'
              exact ⟨⟨(x, t) :: Γ, σr⟩, List.mem_singleton.mpr rfl,
                envLe_cons hΓ hslot, hrest⟩
  | kMkList n =>
      simp only [step1] at hstep
      cases hpop : popTyN n anyT σ with
      | none => simp only [hpop] at hstep; exact absurd hstep (by simp)
      | some mid =>
          simp only [hpop, Option.some.injEq] at hstep
          subst hstep
          obtain ⟨mid', hpop', hle'⟩ := popTyN_cov n anyT hσ hpop
          refine ⟨(⟨Γ', [.anyValue .list] :: mid'⟩ : World) :: [], ?_, ?_⟩
          · simp only [step1, hpop']
          · intro u' hu2
            simp only [List.mem_singleton] at hu2
            subst hu2
            exact ⟨⟨Γ, [.anyValue .list] :: mid⟩, List.mem_singleton.mpr rfl,
              hΓ, ⟨slotLe_refl _, hle'⟩⟩
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
                      refine ⟨(⟨Γ', [.anyValue .obj] :: σr'⟩ : World) :: [], ?_, ?_⟩
                      · simp only [step1, hsn, hpop']
                      · intro u' hu2
                        simp only [List.mem_singleton] at hu2
                        subst hu2
                        exact ⟨⟨Γ, [.anyValue .obj] :: mid⟩,
                          List.mem_singleton.mpr rfl, hΓ,
                          ⟨slotLe_refl _, hrest⟩⟩
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
                  refine ⟨(⟨Γ', payloadsOf t' :: σr'⟩ : World) :: [], rfl, ?_⟩
                  intro u' hu2
                  simp only [List.mem_singleton] at hu2
                  subst hu2
                  exact ⟨⟨Γ, ps :: σr⟩, List.mem_singleton.mpr rfl, hΓ,
                    ⟨hslot2, hrest⟩⟩
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
                          refine ⟨(⟨Γ', t' :: σr'⟩ : World) :: [], rfl, ?_⟩
                          intro u' hu2
                          simp only [List.mem_singleton] at hu2
                          subst hu2
                          exact ⟨⟨Γ, t :: σr⟩, List.mem_singleton.mpr rfl,
                            hΓ, ⟨hslot, hrest⟩⟩
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
                                      refine ⟨(⟨Γ', ([] : Ty) :: σr'⟩ : World) :: [], rfl, ?_⟩
                                      intro u' hu2
                                      simp only [List.mem_singleton] at hu2
                                      subst hu2
                                      exact ⟨⟨Γ, wt.map VTy.complN :: σr⟩,
                                        List.mem_singleton.mpr rfl, hΓ,
                                        ⟨hslot2, hrest⟩⟩
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
                                  refine ⟨(⟨Γ', t'.map VTy.complN :: σr'⟩ : World) :: [], rfl, ?_⟩
                                  intro u' hu2
                                  simp only [List.mem_singleton] at hu2
                                  subst hu2
                                  exact ⟨⟨Γ, wt.map VTy.complN :: σr⟩,
                                    List.mem_singleton.mpr rfl, hΓ,
                                    ⟨hslot2, hrest⟩⟩
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
                      refine ⟨(⟨Γ', [VTy.complT] :: σr'⟩ : World) :: [], rfl, ?_⟩
                      intro u' hu2
                      simp only [List.mem_singleton] at hu2
                      subst hu2
                      exact ⟨⟨Γ, [VTy.complT] :: σr⟩,
                        List.mem_singleton.mpr rfl, hΓ,
                        ⟨slotLe_refl _, hrest⟩⟩
          | pIsObj | pIsNotObj | pIsNotU | pHasCall | pHasCtor | pIsU
          | pIsTrue | pIsFalse | pNullOrUnd | pIsNull
          | pIsType _ | pHasField _ | pIsStr _ | pDescField _
          | pUnwrapC | pIsNormalC | pIsThrowC | pIsCompletion | pPred _ _ =>
              simp only [step1, hpt, Option.some.injEq] at hstep
              subst hstep
              refine ⟨(⟨Γ', σ'⟩ : World) :: [], by
                simp only [step1, hpt], ?_⟩
              intro u' hu2
              simp only [List.mem_singleton] at hu2
              subst hu2
              exact ⟨⟨Γ, σ⟩, List.mem_singleton.mpr rfl, hΓ, hσ⟩
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
                      refine ⟨(⟨Γ', tout :: σr'⟩ : World) :: [], ?_, ?_⟩
                      · simp only [step1, hpt, hpop']
                      · intro u' hu2
                        simp only [List.mem_singleton] at hu2
                        subst hu2
                        exact ⟨⟨Γ, tout :: mid⟩,
                          List.mem_singleton.mpr rfl, hΓ,
                          ⟨slotLe_refl _, hrest⟩⟩
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
                  refine ⟨(⟨Γ', complTy retj :: σ'.drop n⟩ : World) :: [], ?_, ?_⟩
                  · simp only [step1, hsig, har, hpa']
                  · intro u' hu2
                    simp only [List.mem_singleton] at hu2
                    subst hu2
                    exact ⟨⟨Γ, complTy retj :: σ.drop n⟩,
                      List.mem_singleton.mpr rfl, hΓ,
                      ⟨slotLe_refl _, stackLe_drop n hσ⟩⟩
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
              | nil => exact absurd hstep (by simp [popA, popTy])
              | cons m mr =>
                  cases hpop2 : popA (VTy.anyValue Ctor.obj) (m :: mr) with
                  | none => simp only [hpop2] at hstep
                            exact absurd hstep (by simp)
                  | some m2 =>
                      have hm2 : m2 = mr := by
                        simp only [popA, popTy] at hpop2
                        cases hif : tmoves m [VTy.anyValue Ctor.obj] with
                        | false => rw [hif] at hpop2; simp at hpop2
                        | true =>
                            rw [hif] at hpop2
                            simp only [Option.some.injEq, reduceIte] at hpop2
                            exact hpop2.symm
                      subst hm2
                      simp only [hpop2, Option.some.injEq] at hstep
                      subst hstep
                      obtain ⟨mid', hpop', hle'⟩ := popTyN_cov n anyT hσ hpop
                      cases mid' with
                      | nil => exact absurd hle' (by simp [stackLe])
                      | cons m' mr' =>
                          obtain ⟨hslotm, hrestm⟩ := hle'
                          have hpa' : popA (VTy.anyValue Ctor.obj) (m' :: mr')
                              = some mr' := popTy_cov hslotm hrestm hpop2
                          refine ⟨(⟨Γ', complTy (mopResult nm) :: mr'⟩ : World) :: [], ?_, ?_⟩
                          · simp only [step1, har, hpop']
                            rw [hpa']
                          · intro u' hu2
                            simp only [List.mem_singleton] at hu2
                            subst hu2
                            exact ⟨⟨Γ, complTy (mopResult nm) :: m2⟩,
                              List.mem_singleton.mpr rfl, hΓ,
                              ⟨slotLe_refl _, hrestm⟩⟩
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
                              refine ⟨(⟨Γ', [.isValue (.boolean Bool.true)]
                                :: [VTy.complT] :: σr'⟩ : World) :: [], rfl, ?_⟩
                              intro u' hu2
                              simp only [List.mem_singleton] at hu2
                              subst hu2
                              exact ⟨⟨Γ, [.isValue (.boolean Bool.true)]
                                :: [VTy.complT] :: σr⟩,
                                List.mem_singleton.mpr rfl, hΓ,
                                ⟨slotLe_refl _, ⟨slotLe_refl _, hrest⟩⟩⟩
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
                              refine ⟨(⟨Γ', [.isValue (.boolean Bool.false)]
                                :: (h1 :: hs) :: σr'⟩ : World) :: [], rfl, ?_⟩
                              intro u' hu2
                              simp only [List.mem_singleton] at hu2
                              subst hu2
                              refine ⟨⟨Γ, [.isValue (.boolean Bool.false)]
                                :: (n1 :: ns) :: σr⟩,
                                List.mem_singleton.mpr rfl, hΓ, ?_⟩
                              refine ⟨slotLe_refl _, ⟨?_, hrest⟩⟩
                              refine ⟨?_, ?_⟩
                              · have hle := tyLe_of_atom_cov
                                  (complNormals_cov hcov)
                                rw [hnorm', hnorm] at hle
                                exact hle
                              · intro _ hc2
                                exact List.cons_ne_nil h1 hs hc2
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
                              refine ⟨(⟨Γ', [.isValue (.boolean Bool.true)]
                                :: [VTy.complT] :: σr'⟩ : World) :: [], rfl, ?_⟩
                              intro u' hu2
                              simp only [List.mem_singleton] at hu2
                              subst hu2
                              exact ⟨⟨Γ, [.isValue (.boolean Bool.true)]
                                :: [VTy.complT] :: σr⟩,
                                List.mem_cons.mpr (Or.inr
                                  (List.mem_singleton.mpr rfl)), hΓ,
                                ⟨slotLe_refl _, ⟨slotLe_refl _, hrest⟩⟩⟩
                          | cons h1 hs =>
                              have hco' : complOnly t' = Bool.true :=
                                complOnly_of_compl hpure'
                              cases hthrow' : complHasThrow t' with
                              | false =>
                                  simp only [step1, hco', hnorm', hthrow',
                                    reduceIte, List.append_nil]
                                  refine ⟨(⟨Γ', [.isValue (.boolean Bool.false)]
                                    :: (h1 :: hs) :: σr'⟩ : World) :: [], rfl, ?_⟩
                                  intro u' hu2
                                  simp only [List.mem_singleton] at hu2
                                  subst hu2
                                  refine ⟨⟨Γ, [.isValue (.boolean Bool.false)]
                                    :: (n1 :: ns) :: σr⟩,
                                    List.mem_cons.mpr (Or.inl rfl), hΓ, ?_⟩
                                  refine ⟨slotLe_refl _, ⟨?_, hrest⟩⟩
                                  refine ⟨?_, ?_⟩
                                  · have hle := tyLe_of_atom_cov
                                      (complNormals_cov hcov)
                                    rw [hnorm', hnorm] at hle
                                    exact hle
                                  · intro _ hc2
                                    exact List.cons_ne_nil h1 hs hc2
                              | true =>
                                  simp only [step1, hco', hnorm', hthrow',
                                    reduceIte, List.cons_append, List.nil_append]
                                  refine ⟨(⟨Γ', [.isValue (.boolean Bool.false)]
                                    :: (h1 :: hs) :: σr'⟩ : World)
                                    :: (⟨Γ', [.isValue (.boolean Bool.true)]
                                    :: [VTy.complT] :: σr'⟩ : World) :: [],
                                    ?_, ?_⟩
                                  · rfl
                                  · intro u' hu2
                                    simp only [List.mem_cons, List.mem_singleton] at hu2
                                    rcases hu2 with rfl | hu2
                                    · refine ⟨⟨Γ, [.isValue (.boolean Bool.false)]
                                        :: (n1 :: ns) :: σr⟩,
                                        List.mem_cons.mpr (Or.inl rfl), hΓ, ?_⟩
                                      exact ⟨slotLe_refl _, ⟨by
                                        have hle := tyLe_of_atom_cov
                                          (complNormals_cov hcov)
                                        rw [hnorm', hnorm] at hle
                                        exact ⟨hle, by
                                          intro _ hc
                                          exact List.cons_ne_nil h1 hs hc⟩,
                                        hrest⟩⟩
                                    · rcases hu2 with h2 | h2
                                      · subst h2
                                        exact ⟨⟨Γ, [.isValue (.boolean Bool.true)]
                                          :: [VTy.complT] :: σr⟩,
                                          List.mem_cons.mpr
                                            (Or.inr (List.mem_singleton.mpr rfl)),
                                          hΓ, ⟨slotLe_refl _,
                                          ⟨slotLe_refl _, hrest⟩⟩⟩
                                      · cases h2
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
  case case29 =>
    rename_i sigs r w c body rest hempty ps hty hnt
    intro fb h hf
    simp only [checkSeq, hempty, hty] at h
    split at h
    · next hcond => exact absurd hcond hnt
    · exact TCResult.noConfusion h
  case case30 =>
    rename_i sigs r w c body rest hempty hty
    intro fb h hf
    simp only [checkSeq, hempty, hty] at h
    exact TCResult.noConfusion h
  case case31 =>
    rename_i sigs r w c body rest hne
    intro fb h hf
    cases hσ : w.σ with
    | nil => exact absurd hσ hne
    | cons a as =>
        simp only [checkSeq, hσ] at h
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
  case case51 =>
    rename_i sigs r w x body rest hd htl hpop
    intro fb h hf
    simp only [checkSeq, hpop] at h
    exact TCResult.noConfusion h
  case case52 =>
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
theorem runtime_args_le {sigs : SigTable} {f : «String»} {n : Nat}
    {ps : List Ty} {retj : List Pending} {eval : List JSValue}
    (hsig : sigFind sigs f = some (ps, retj))
    (har : ((ps.length == n) || (ps.length == n + 1)) = Bool.true)
    (hpop : popArgs (if ps.length == n then ps else ps.take n)
      (eval.map (fun v => [typeOfV v])) = Bool.true) :
    ((eval.take n).reverse.map (fun v => [typeOfV v])).length
        ≤ (sigParams sigs f).length
      ∧ leTy ((eval.take n).reverse.map (fun v => [typeOfV v]))
          ((sigParams sigs f).take
            ((eval.take n).reverse.map (fun v => [typeOfV v])).length)
          = Bool.true := by
  have hnl : n ≤ eval.length := by
    simpa [List.length_map] using popArgs_n_le har hpop
  have htake_len : (eval.take n).length = n := by
    rw [List.length_take, Nat.min_eq_left hnl]
  have hts : (eval.take n).reverse.map (fun v => [typeOfV v])
      = ((eval.map (fun v => [typeOfV v])).take n).reverse := by
    rw [List.map_reverse, List.map_take]
  have hlen_eq : ((eval.take n).reverse.map (fun v => [typeOfV v])).length = n := by
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
theorem callee_frameChecks {sigs : SigTable} {reg : AOReg} {fname : «String»}
    {ps : List «String»} {body : Prog} {args : List JSValue}
    (hcert : registryCertified sigs reg)
    (hmem : (fname, (ps, body)) ∈ reg)
    (hlen : (args.reverse.map (fun v => [typeOfV v])).length
      ≤ (sigParams sigs fname).length)
    (hle : leTy (args.reverse.map (fun v => [typeOfV v]))
      ((sigParams sigs fname).take
        (args.reverse.map (fun v => [typeOfV v])).length) = Bool.true) :
    frameChecks sigs ⟨compileSteps body, ps.zip args.reverse, [], fname⟩ := by
  obtain ⟨-, hc⟩ := hcert fname ps body hmem
  obtain ⟨fb, hchk, hterm, -⟩ := certifies_flows_elim (hc _ hlen hle)
  simp only [frameChecks, frameWorld, envTyOf_zipTy, hchk, hterm, List.map_nil]

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
theorem frameChecks_elim {sigs : SigTable} {f : Fr}
    (h : frameChecks sigs f) :
    ∃ fb, checkSeq sigs (sigRetTy sigs f.ret) (frameWorld f) f.stmts
        = TCResult.flows fb ∧ terminal fb = Bool.true := by
  cases hc : checkSeq sigs (sigRetTy sigs f.ret) (frameWorld f) f.stmts with
  | flows fb =>
      exact ⟨fb, rfl, by rw [frameChecks, hc] at h; exact h⟩
  | reject s w =>
      rw [frameChecks, hc] at h
      exact h.elim

/-- THE kCall ARM (registry-hit; the native branch is the
    specialization capstone's business). -/
theorem SR_kCall (sigs : SigTable) (reg : AOReg)
    (hclosed : ∀ (m : «String») (ps : List Ty) (retj : List Pending),
      sigFind sigs m = some (ps, retj) → (findAO reg m).isSome = Bool.true)
    (fname : «String») (n : Nat) (s : FM) (r : Ty) :
    SR_arm sigs reg (.kCall fname n) s r := by
  intro hcert hpre
  cases s with
  | fdone v fs heap nl n' => exact hpre
  | fell fs heap nl n' => exact hpre
  | frames fs heap nl =>
      cases fs with
      | nil => exact hpre
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          obtain ⟨fb, hchk, hterm⟩ := frameChecks_elim hpre.1.1
          simp only [frameWorld] at hchk
          obtain ⟨ps, retj, hsig, har, hpop, hpost⟩ := checkSeq_kCall_elim hchk
          dsimp only at hpost
          -- machine: underflow impossible
          have hlen : n ≤ eval.length := by
            simpa [List.length_map] using popArgs_n_le har hpop
          obtain ⟨⟨psr, body⟩, hfao⟩ :=
            findAO_isSome (hclosed fname ps retj hsig)
          -- arg typings
          obtain ⟨hlen', hle'⟩ := runtime_args_le hsig har hpop
          have hle : ((eval.take n).reverse.map (fun v => [typeOfV v])).length
              ≤ (sigParams sigs fname).length := hlen'
          have hcl := callee_frameChecks hcert (findAO_mem hfao) hlen' hle'
          -- caller anticipation = the checker's post-world
          have hcaller : frameOkUnder sigs fname ⟨stmts, env, eval.drop n, ret⟩ := by
            simp only [frameOkUnder, sigCompls_of_sigFind hsig]
            rw [List.map_drop, hpost]
            exact hterm
          rw [fstep_kCall_found hfao hlen]
          refine ⟨⟨hcl, hcaller, hpre.1.2⟩, ?_⟩
          rw [machineRet_cons_cons,
            machineRet_cons_congr (f := ⟨stmts, env, eval.drop n, ret⟩)
              (g := ⟨.kCall fname n :: stmts, env, eval, ret⟩) rfl]
          exact hpre.2

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