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
  match checkSeq sigs (sigRetTy sigs f.ret)
    { Γ := envTyOf f.env, σ := f.eval.map (fun v => [typeOfV v]) } f.stmts with
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

/-- Pointwise refinement of type environments: every refined atom is
    covered by some coarse atom (the ∃-form gives existence
    covariance: a nonempty refined lookup implies a nonempty coarse
    lookup - needed by the split arms). -/
def envLe (Γ Δ : TyEnv) : Prop :=
  ∀ (x : «String»), ∀ t ∈ tyLookup Γ x, ∃ u ∈ tyLookup Δ x, tyLe t u

def stackLe (σ τ : List Ty) : Prop :=
  σ.length = τ.length ∧
    ∀ (i : Nat), ∀ t ∈ σ[i]?, ∀ u ∈ τ[i]?, tyLe t u

def worldLe (w u : World) : Prop :=
  envLe w.Γ u.Γ ∧ stackLe w.σ u.σ

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
    {rest : List Instr} (hv : isCompl v = Bool.false) :
    checkSeq sigs r W (.kEval (.const v) :: rest)
      = checkSeq sigs r { W with σ := [typeOfV v] :: W.σ } rest := by
  cases v with
  | compl b pv => simp [isCompl] at hv
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _ | descV _ =>
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


theorem sr_kEval_const {sigs : SigTable} {v : JSValue} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»}
    (hv : isCompl v = Bool.false)
    (h : frameOk sigs none ⟨.kEval (.const v) :: rest, env, eval, ret⟩) :
    frameOk sigs none ⟨rest, env, v :: eval, ret⟩ := by
  have hchk := frameOk_none_elim h
  rw [frameChecks] at hchk
  simp only [List.map_cons] at hchk
  rw [checkSeq_kEval_const hv] at hchk
  refine frameOk_none_intro ?_
  rw [frameChecks]
  simp only [List.map_cons]
  exact hchk

theorem sr_kEval_nat {sigs : SigTable} {n : Nat} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameOk sigs none ⟨.kEval (.nat n) :: rest, env, eval, ret⟩) :
    frameOk sigs none ⟨rest, env, .number (↑n : Int) :: eval, ret⟩ := by
  have hchk := frameOk_none_elim h
  rw [frameChecks] at hchk
  simp only [List.map_cons] at hchk
  rw [checkSeq_kEval_nat] at hchk
  refine frameOk_none_intro ?_
  rw [frameChecks]
  simp only [List.map_cons]
  exact hchk

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

theorem sr_kEval_nv {sigs : SigTable} {x : «String»} {v : JSValue} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»}
    (hl : lookup env x = some v)
    (h : frameOk sigs none ⟨.kEval (.nv x) :: rest, env, eval, ret⟩) :
    frameOk sigs none ⟨rest, env, v :: eval, ret⟩ := by
  have hchk := frameOk_none_elim h
  rw [frameChecks] at hchk
  have hΓ : tyLookup (envTyOf env) x = some [typeOfV v] := by
    rw [← envTyOf_lookup env x, hl]
    rfl
  rw [checkSeq_kEval_nv hΓ] at hchk
  refine frameOk_none_intro ?_
  rw [frameChecks]
  simp only [List.map_cons]
  exact hchk

/- ## Proof layer Vb: kPop / kSet (the parked-discipline arms) -/

/-- A head value never parks: if the parked slot stayed none, the
    head cannot be a completion. -/
theorem checkSeq_reject_kPop {sigs : SigTable} {r : Ty} {W : World}
    {rest : List Instr} (hbad : step1 sigs .kPop W = none) :
    ∃ why, checkSeq sigs r W (.kPop :: rest)
      = TCResult.reject .kPop why := by
  simp only [checkSeq, hbad]
  exact ⟨_, rfl⟩

theorem checkSeq_reject_kSet {sigs : SigTable} {r : Ty} {W : World} {x : «String»}
    {rest : List Instr} (hbad : step1 sigs (.kSet x) W = none) :
    ∃ why, checkSeq sigs r W (.kSet x :: rest)
      = TCResult.reject (.kSet x) why := by
  simp only [checkSeq, hbad]
  exact ⟨_, rfl⟩

theorem sr_kPop {sigs : SigTable} {w : JSValue} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameOk sigs none ⟨.kPop :: rest, env, w :: eval, ret⟩) :
    frameOk sigs none ⟨rest, env, eval, ret⟩ := by
  have hchk := frameOk_none_elim h
  rw [frameChecks] at hchk
  simp only [List.map_cons] at hchk
  rw [checkSeq_kPop rfl] at hchk
  refine frameOk_none_intro ?_
  rw [frameChecks]
  exact hchk

theorem sr_kSet {sigs : SigTable} {x : «String»} {w : JSValue} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameOk sigs none ⟨.kSet x :: rest, env, w :: eval, ret⟩) :
    frameOk sigs none ⟨rest, (x, w) :: env, eval, ret⟩ := by
  have hchk := frameOk_none_elim h
  rw [frameChecks] at hchk
  simp only [List.map_cons] at hchk
  rw [checkSeq_kSet rfl] at hchk
  refine frameOk_none_intro ?_
  rw [frameChecks, envTyOf_cons]
  exact hchk

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
    rw [if_neg hnt] at h
    exact TCResult.noConfusion h
  case case4 =>
    rename_i sigs r w tail hσ
    intro fb h hf
    simp only [checkSeq, hσ] at h; exact TCResult.noConfusion h
  case case5 =>
    rename_i sigs r w t e rest hσ
    intro fb h hf
    simp only [checkSeq, hσ] at h; exact TCResult.noConfusion h
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
    rename_i sigs r w pv rest ih1
    intro fb h hf
    simp only [checkSeq] at h; exact ih1 fb h hf
  case case8 =>
    rename_i sigs r w v rest ih1
    intro fb h hf
    simp only [checkSeq] at h; exact ih1 fb h hf
  case case9 =>
    rename_i sigs r w x rest hlook ih1
    intro fb h hf
    simp only [checkSeq, hlook] at h; exact ih1 fb h hf
  case case10 =>
    rename_i sigs r w x rest S hlook ih1
    intro fb h hf
    simp only [checkSeq, hlook] at h; exact forkTC_exits h hf ih1
  case case11 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_7] at h; exact ih1 fb h hf
  case case12 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_8] at h; exact ih1 fb h hf
  case case13 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_9] at h; exact ih1 fb h hf
  case case14 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_10] at h; exact ih1 fb h hf
  case case15 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_11] at h; exact ih1 fb h hf
  case case16 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_12] at h; exact ih1 fb h hf
  case case17 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_13] at h; exact ih1 fb h hf
  case case18 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_14] at h; exact ih1 fb h hf
  case case19 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_15] at h; exact ih1 fb h hf
  case case20 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_16] at h; exact ih1 fb h hf
  case case21 =>
    rename_i sigs r w s x rest ih1
    intro fb h hf
    rw [checkSeq.eq_17] at h; exact ih1 fb h hf
  case case22 =>
    rename_i sigs r w ty x rest ih1
    intro fb h hf
    rw [checkSeq.eq_18] at h; exact ih1 fb h hf
  case case23 =>
    rename_i sigs r w nm x rest ih1
    intro fb h hf
    rw [checkSeq.eq_19] at h; exact ih1 fb h hf
  case case24 =>
    rename_i sigs r w b f x rest hfused ih1
    intro fb h hf
    rw [checkSeq.eq_20, if_pos hfused] at h; exact ih1 fb h hf
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
    rename_i sigs r w c body rest t hty hbool ih2 ih1
    intro fb h hf
    simp only [checkSeq, hty] at h
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
    · next hcond => exact absurd hbool hcond
  case case28 =>
    rename_i sigs r w c body rest t hty hnt
    intro fb h hf
    simp only [checkSeq, hty] at h
    split at h
    · next hcond => exact absurd hcond hnt
    · exact TCResult.noConfusion h
  case case29 =>
    rename_i sigs r w c body rest hty
    intro fb h hf
    simp only [checkSeq, hty] at h; exact TCResult.noConfusion h
  case case30 =>
    rename_i sigs r w ex rest hdisj hty
    intro fb h hf
    simp only [checkSeq, hty] at h; exact TCResult.noConfusion h
  case case31 =>
    rename_i sigs r w ex rest hdisj S hty ih1
    intro fb h hf
    simp only [checkSeq, hty] at h; exact markThrow_exits h hf ih1
  case case32 =>
    rename_i sigs r w x rest f b dec hdec ih1
    intro fb h hf
    simp only [checkSeq, hdec] at h; exact forkTC_exits h hf ih1
  case case33 =>
    rename_i sigs r w x rest f b hdec hlook
    intro fb h hf
    simp only [checkSeq, hdec, hlook] at h; exact TCResult.noConfusion h
  case case34 =>
    rename_i sigs r w x rest f b hdec S hlook ih1
    intro fb h hf
    simp only [checkSeq, hdec, hlook] at h; exact ih1 fb h hf
  case case35 =>
    rename_i sigs r w x p rest t hT hpred ih1
    intro fb h hf
    simp only [checkSeq, hT] at h; exact forkTC_exits h hf ih1
  case case36 =>
    rename_i sigs r w x p rest hT hlook hpred
    intro fb h hf
    simp only [checkSeq, hT, hlook] at h; exact TCResult.noConfusion h
  case case37 =>
    rename_i sigs r w x p rest hT S hlook hpred ih1
    intro fb h hf
    simp only [checkSeq, hT, hlook] at h; exact ih1 fb h hf
  case case38 =>
    rename_i sigs r w c body rest hpop
    intro fb h hf
    simp only [checkSeq, hpop] at h; exact TCResult.noConfusion h
  case case39 =>
    rename_i sigs r w c body rest σ' hpop ih2 ih1
    intro fb h hf
    simp only [checkSeq, hpop] at h
    cases hbody : checkSeq sigs r { Γ := w.Γ, σ := σ'} body with
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
  case case40 =>
    rename_i sigs r w x body rest hpop
    intro fb h hf
    simp only [checkSeq, hpop] at h; exact TCResult.noConfusion h
  case case41 =>
    rename_i sigs r w x body rest σ' hpop ih2 ih1
    intro fb h hf
    simp only [checkSeq, hpop] at h
    cases hbody : checkSeq sigs r { Γ := (x, langT) :: w.Γ, σ := σ'} body with
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
  case case42 =>
    rename_i sigs r w x elems body rest ih2 ih1
    intro fb h hf
    simp only [checkSeq] at h
    cases hbody : checkSeq sigs r { Γ := (x, langT) :: w.Γ, σ := w.σ} body with
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
  case case43 =>
    rename_i sigs r w rest hσ
    intro fb h hf
    simp only [checkSeq, hσ] at h; exact TCResult.noConfusion h
  case case44 =>
    rename_i sigs r w rest ts σ' hσ ih1
    intro fb h hf
    simp only [checkSeq, hσ] at h
    obtain ⟨-, heq⟩ := fold_merge_flows _ ts vacOk (ne_reject_of_flows h)
    rw [heq] at h
    have hinj := TCResult.flows.inj h
    subst hinj
    rfl
  case case45 =>
    rename_i sigs r w i rest hdisj hstep
    intro fb h hf
    simp only [checkSeq, hstep] at h; exact TCResult.noConfusion h
  case case46 =>
    rename_i sigs r w i rest hdisj ws' hstep ih1
    intro fb h hf
    simp only [checkSeq, hstep] at h; exact forkTC_exits h hf ih1

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

theorem sr_kEval_compl_normal {sigs : SigTable} {pv : JSValue} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameOk sigs none ⟨.kEval (.const (.compl Bool.false pv)) :: rest, env, eval, ret⟩) :
    frameOk sigs none ⟨rest, env, .compl Bool.false pv :: eval, ret⟩ := by
  have hchk := frameOk_none_elim h
  rw [frameChecks] at hchk
  simp only [checkSeq] at hchk
  refine frameOk_none_intro ?_
  rw [frameChecks]
  simp only [List.map_cons, typeOfV]
  exact hchk

theorem sr_kEval_compl_throw {sigs : SigTable} {v : JSValue} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameOk sigs none ⟨.kEval (.const (.compl Bool.true v)) :: rest, env, eval, ret⟩) :
    frameOk sigs none ⟨rest, env, .compl Bool.true v :: eval, ret⟩ := by
  have hchk := frameOk_none_elim h
  rw [frameChecks] at hchk
  simp only [checkSeq] at hchk
  refine frameOk_none_intro ?_
  rw [frameChecks]
  simp only [List.map_cons, typeOfV]
  exact hchk

theorem sr_kTest_normal {sigs : SigTable} {pv : JSValue} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameOk sigs none ⟨.kTest :: rest, env, .compl Bool.false pv :: eval, ret⟩) :
    frameOk sigs none
      ⟨rest, env, .boolean Bool.false :: .compl Bool.false pv :: eval, ret⟩ := by
  have hchk := frameOk_none_elim h
  rw [frameChecks] at hchk
  simp only [List.map_cons, typeOfV] at hchk
  rw [checkSeq_kTest_normal rfl] at hchk
  refine frameOk_none_intro ?_
  rw [frameChecks]
  simp only [List.map_cons, typeOfV]
  exact hchk

theorem sr_kTest_throw {sigs : SigTable} {pv : JSValue} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameOk sigs none ⟨.kTest :: rest, env, .compl Bool.true pv :: eval, ret⟩) :
    frameOk sigs none
      ⟨rest, env, .boolean Bool.true :: .compl Bool.true pv :: eval, ret⟩ := by
  have hchk := frameOk_none_elim h
  rw [frameChecks] at hchk
  simp only [List.map_cons, typeOfV] at hchk
  rw [checkSeq_kTest_throw rfl] at hchk
  refine frameOk_none_intro ?_
  rw [frameChecks]
  simp only [List.map_cons, typeOfV]
  exact hchk

theorem sr_kUnwrap {sigs : SigTable} {pv : JSValue} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameOk sigs none ⟨.kUnwrap :: rest, env, .compl Bool.false pv :: eval, ret⟩) :
    frameOk sigs none ⟨rest, env, pv :: eval, ret⟩ := by
  have hchk := frameOk_none_elim h
  rw [frameChecks] at hchk
  simp only [List.map_cons, typeOfV] at hchk
  rw [checkSeq_kUnwrap rfl] at hchk
  refine frameOk_none_intro ?_
  rw [frameChecks]
  simp only [List.map_cons]
  exact hchk

theorem sr_pWrapC {sigs : SigTable} {v : JSValue} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»}
    (hv : isCompl v = Bool.false)
    (h : frameOk sigs none ⟨.kPrim1 .pWrapC :: rest, env, v :: eval, ret⟩) :
    frameOk sigs none ⟨rest, env, .compl Bool.false v :: eval, ret⟩ := by
  have hchk := frameOk_none_elim h
  rw [frameChecks] at hchk
  simp only [List.map_cons] at hchk
  rw [checkSeq_pWrapC rfl (by
    cases v with
    | compl a b => simp [isCompl] at hv
    | undefined | null | boolean _ | number _ | str _
    | obj _ | listV _ | descV _ => rfl)] at hchk
  refine frameOk_none_intro ?_
  rw [frameChecks]
  simp only [List.map_cons, typeOfV]
  exact hchk

theorem sr_pThrowC {sigs : SigTable} {v : JSValue} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameOk sigs none ⟨.kPrim1 .pThrowC :: rest, env, v :: eval, ret⟩) :
    frameOk sigs none ⟨rest, env, .compl Bool.true v :: eval, ret⟩ := by
  have hchk := frameOk_none_elim h
  rw [frameChecks] at hchk
  simp only [List.map_cons] at hchk
  rw [checkSeq_pThrowC rfl] at hchk
  refine frameOk_none_intro ?_
  rw [frameChecks]
  simp only [List.map_cons, typeOfV]
  exact hchk

/- ## QUARANTINED (to re-derive on the flat completion universe):
    layers X-XIII (step1_mono and its plumbing) referenced the old
    step1 equations; git history preserves the proofs. Nothing
    proven depends on them yet — they serve sr_kTestVar/sr_kCall,
    which come with the completion-corpus work. -/

/- ## Proof layer XVI: sr_kIte and the no-silent-falls bridge

    The kIte commutation: one machine step through a decided
    verdict equals the checker's vacOk-merge of the chosen branch;
    terminality transfers across the merge ONLY because of the
    no-silent-falls invariant (checkSeq_exits, layer Vb). The loud
    arm is excluded by the per-atom dispatch itself — on the
    pending-machine, a completion can never sit on eval at all, so
    there is no position caveat: EVERY loud kIte state is
    statically rejected. -/

/-- Terminal transfer across the vacOk merge. -/
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
theorem sr_kIte {sigs : SigTable} {b : Bool} {t e : List Instr} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameOk sigs none ⟨.kIte t e :: rest, env, .boolean b :: eval, ret⟩) :
    frameOk sigs none ⟨(if b then t else e) ++ rest, env, eval, ret⟩ := by
  obtain ⟨-, hchk⟩ := h
  rw [frameChecks] at hchk
  simp only [List.map_cons] at hchk
  cases hb : b with
  | true =>
      rw [hb] at hchk
      have hslot : [typeOfV (JSValue.boolean Bool.true)] = [VTy.isValue (JSValue.boolean Bool.true)] := rfl
      rw [hslot] at hchk
      have hid : checkSeq sigs (sigRetTy sigs ret)
          { Γ := envTyOf env, σ := [VTy.isValue (JSValue.boolean Bool.true)] :: eval.map (fun v => [typeOfV v])} (.kIte t e :: rest)
          = mergeTC vacOk (checkSeq sigs (sigRetTy sigs ret)
              { Γ := envTyOf env, σ := eval.map (fun v => [typeOfV v])} (t ++ rest)) :=
        checkSeq_kIte_true rfl
      rw [hid] at hchk
      cases hres : checkSeq sigs (sigRetTy sigs ret)
          { Γ := envTyOf env, σ := eval.map (fun v => [typeOfV v])} (t ++ rest) with
      | reject s w =>
          rw [hres] at hchk
          have hrej : mergeTC vacOk (TCResult.reject s w) = TCResult.reject s w := rfl
          rw [hrej] at hchk
          exact hchk.elim
      | flows fbr =>
          cases hm : mergeTC vacOk (checkSeq sigs (sigRetTy sigs ret)
              { Γ := envTyOf env, σ := eval.map (fun v => [typeOfV v])} (t ++ rest)) with
          | reject s w =>
              rw [hm] at hchk
              exact hchk.elim
          | flows fbm =>
              rw [hm] at hchk
              obtain ⟨fbr', hfb, htr⟩ := merge_vacOk_terminal hm hchk
              have hbr' : fbr' = fbr := TCResult.flows.inj (hfb.symm.trans hres)
              subst hbr'
              refine ⟨by simp, ?_⟩
              rw [frameChecks]
              show (match checkSeq sigs (sigRetTy sigs ret)
                  { Γ := envTyOf env, σ := eval.map (fun v => [typeOfV v])} (t ++ rest) with
                  | .flows fb => terminal fb = Bool.true | _ => False)
              rw [hres]
              exact htr
  | false =>
      rw [hb] at hchk
      have hslot : [typeOfV (JSValue.boolean Bool.false)] = [VTy.isValue (JSValue.boolean Bool.false)] := rfl
      rw [hslot] at hchk
      have hid : checkSeq sigs (sigRetTy sigs ret)
          { Γ := envTyOf env, σ := [VTy.isValue (JSValue.boolean Bool.false)] :: eval.map (fun v => [typeOfV v])} (.kIte t e :: rest)
          = mergeTC vacOk (checkSeq sigs (sigRetTy sigs ret)
              { Γ := envTyOf env, σ := eval.map (fun v => [typeOfV v])} (e ++ rest)) :=
        checkSeq_kIte_false rfl
      rw [hid] at hchk
      cases hres : checkSeq sigs (sigRetTy sigs ret)
          { Γ := envTyOf env, σ := eval.map (fun v => [typeOfV v])} (e ++ rest) with
      | reject s w =>
          rw [hres] at hchk
          have hrej : mergeTC vacOk (TCResult.reject s w) = TCResult.reject s w := rfl
          rw [hrej] at hchk
          exact hchk.elim
      | flows fbr =>
          cases hm : mergeTC vacOk (checkSeq sigs (sigRetTy sigs ret)
              { Γ := envTyOf env, σ := eval.map (fun v => [typeOfV v])} (e ++ rest)) with
          | reject s w =>
              rw [hm] at hchk
              exact hchk.elim
          | flows fbm =>
              rw [hm] at hchk
              obtain ⟨fbr', hfb, htr⟩ := merge_vacOk_terminal hm hchk
              have hbr' : fbr' = fbr := TCResult.flows.inj (hfb.symm.trans hres)
              subst hbr'
              refine ⟨by simp, ?_⟩
              rw [frameChecks]
              first
              | (simp only [ite_false]; rw [hres])
              | (rw [if_neg (by decide), hres])
              exact htr

/-- The loud arm is EXCLUDED — and on the pending-machine,
    COMPLETELY: a completion can never sit on eval, so every loud
    kIte state (a non-boolean verdict) is rejected by the per-atom
    dispatch. No position caveat. -/
theorem sr_kIte_loud {sigs : SigTable} {t e : List Instr} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»} {v : JSValue}
    (hv : ∀ b, v ≠ JSValue.boolean b)
    (h : frameOk sigs none ⟨.kIte t e :: rest, env, v :: eval, ret⟩) : False := by
  obtain ⟨-, hchk⟩ := h
  rw [frameChecks] at hchk
  simp only [List.map_cons] at hchk
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
