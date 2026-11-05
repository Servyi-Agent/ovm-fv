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

/- ## The frame <-> world bridge (direct, post-pending-machine)

    The machine parks completions in Fr.pend; eval and env are
    completion-FREE BY CONSTRUCTION. So the abstraction is direct:
    values map to singleton slots, the pending field abstracts
    pointwise. splitStack — and its position-blindness — is gone. -/

def isCompl : JSValue → Bool
  | .compl _ _ => Bool.true
  | _ => Bool.false

def envTyOf : Env → TyEnv := fun env =>
  env.map (fun (n, v) => (n, [typeOfV v]))

/-- The frame's undelivered completion, abstracted. -/
def pendAbstr : Option PendV → Option Pending
  | some (.normal v) => some (.normal [typeOfV v])
  | some PendV.throw => some Pending.throw
  | none => none

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

/-- The frame's check from a given abstract stack + parked
    (or anticipated) completion. -/
def frameChecks (sigs : SigTable) (f : Fr) (p : Option Pending) : Prop :=
  match checkSeq sigs (sigRetTy sigs f.ret)
    { Γ := envTyOf f.env, σ := f.eval.map (fun v => [typeOfV v]), pending := p } f.stmts with
  | .flows fb => terminal fb = Bool.true  -- every world returns
  | _ => False

def frameOk (sigs : SigTable) (above : Option «String») (f : Fr) : Prop :=
  -- a frame under a callee MUST be waiting at the self-test idiom:
  -- the delivery assumption of kRet
  (above.isNone ∨ selfTestHead f.stmts = Bool.true)
    ∧ (match above with
       | some n => ∀ c ∈ sigCompls sigs n, frameChecks sigs f (some c)
       | none => frameChecks sigs f (pendAbstr f.pend))

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
  | .fdone p _ _ _ _ =>
      -- the final pending: normal payload ⊑ r, or a throw
      match p with
      | .normal pv => tmoves [typeOfV pv] r = Bool.true
      | PendV.throw => True
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
      { Γ := zipTy ps ts, σ := [], pending := none } (compileSteps prog) with
  | .flows fb =>
      terminal fb = Bool.true
        ∧ (fb.throws = Bool.true → complCanThrow (sigCompls sigs name) = Bool.true)
  | _ => False

theorem certifies_flows_elim {sigs : SigTable} {name : «String»}
    {ps : List «String»} {ts : List Ty} {prog : Prog}
    (h : certifies sigs name ps ts prog) :
    ∃ fb, checkSeq sigs (sigRetTy sigs name)
        { Γ := zipTy ps ts, σ := [], pending := none } (compileSteps prog)
        = TCResult.flows fb ∧ terminal fb = Bool.true
        ∧ (fb.throws = Bool.true
            → complCanThrow (sigCompls sigs name) = Bool.true) := by
  cases hb : checkSeq sigs (sigRetTy sigs name)
      { Γ := zipTy ps ts, σ := [], pending := none } (compileSteps prog) with
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

/-- Refinement of worlds: Γ and σ refine pointwise; the pending is
    equal (both sides describe the SAME parked delivery shape), or
    the finer side is below on the payload. -/
def pendLe (p q : Option Pending) : Prop :=
  match p, q with
  | none, none => True
  | some (.normal t), some (.normal u) => tyLe t u
  | some .throw, some .throw => True
  | _, _ => False

def stackLe (σ τ : List Ty) : Prop :=
  σ.length = τ.length ∧
    ∀ (i : Nat), ∀ t ∈ σ[i]?, ∀ u ∈ τ[i]?, tyLe t u

def worldLe (w u : World) : Prop :=
  envLe w.Γ u.Γ ∧ stackLe w.σ u.σ ∧ pendLe w.pending u.pending

/-- Subtyping is a preorder on the flat lattice (the atom grid is
    essentially discrete: identity, singleton-into-class, and
    desc-into-anyValue-desc). -/
theorem tmovesV_refl (a : VTy) : tmovesV a a = Bool.true := by
  cases a with
  | anyValue c => simp [tmovesV]
  | isValue v => simp [tmovesV]
  | desc fs => exact decide_eq_true (rfl : fs = fs)
  | notPresent => rfl

theorem tmoves_refl (t : Ty) : tyLe t t := by
  unfold tyLe tmoves
  simp only [List.all_eq_true]
  intro a ha
  exact List.any_eq_true.mpr ⟨a, ha, tmovesV_refl a⟩

theorem tmovesV_trans {a b c : VTy}
    (h₁ : tmovesV a b = Bool.true) (h₂ : tmovesV b c = Bool.true) :
    tmovesV a c = Bool.true := by
  cases a <;> cases b <;> cases c <;>
    simp_all [tmovesV, tagOf, decide_eq_true, beq_iff_eq] <;>
  first
    | rfl
    | simp_all
    | exact of_decide_eq_true (by assumption)
    | (exfalso; simp_all)

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
      { Γ := W.Γ, σ := [VTy.isValue (.number (↑n : Int))] :: W.σ,
        pending := W.pending } rest with
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
      { Γ := W.Γ, σ := [typeOfV v] :: W.σ, pending := W.pending } rest with
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
    {rest : List Instr} (hpn : W.pending = none) (hσ : W.σ = ts :: σ') :
    checkSeq sigs r W (.kPop :: rest)
      = checkSeq sigs r { W with σ := σ' } rest := by
  simp only [checkSeq, step1, hσ, hpn, List.foldl, mergeTC_noFlows, forkTC_cons]

/-- kSet: bind the top slot into Γ. -/
theorem checkSeq_kSet {sigs : SigTable} {r : Ty} {W : World} {x : «String»}
    {ts : Ty} {σ' : List Ty} {rest : List Instr}
    (hpn : W.pending = none) (hσ : W.σ = ts :: σ') :
    checkSeq sigs r W (.kSet x :: rest)
      = checkSeq sigs r { Γ := (x, ts) :: W.Γ, σ := σ', pending := none } rest := by
  simp only [checkSeq, step1, hσ, hpn, List.foldl, mergeTC_noFlows, forkTC_cons]


/- ## Proof layer V: the exact-match sr arms (head frame, above = none) -/


theorem sr_kEval_const {sigs : SigTable} {v : JSValue} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»} {pend : Option PendV}
    (hv : isCompl v = Bool.false)
    (h : frameOk sigs none ⟨.kEval (.const v) :: rest, env, eval, ret, pend⟩) :
    frameOk sigs none ⟨rest, env, v :: eval, ret, pend⟩ := by
  obtain ⟨-, hchk⟩ := h
  rw [frameChecks] at hchk
  simp only [List.map_cons] at hchk
  rw [checkSeq_kEval_const hv] at hchk
  refine ⟨by simp, ?_⟩
  rw [frameChecks]
  simp only [List.map_cons]
  exact hchk

theorem sr_kEval_nat {sigs : SigTable} {n : Nat} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»} {pend : Option PendV}
    (h : frameOk sigs none ⟨.kEval (.nat n) :: rest, env, eval, ret, pend⟩) :
    frameOk sigs none ⟨rest, env, .number (↑n : Int) :: eval, ret, pend⟩ := by
  obtain ⟨-, hchk⟩ := h
  rw [frameChecks] at hchk
  simp only [List.map_cons] at hchk
  rw [checkSeq_kEval_nat] at hchk
  refine ⟨by simp, ?_⟩
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
    {env : Env} {eval : List JSValue} {ret : «String»} {pend : Option PendV}
    (hl : lookup env x = some v)
    (h : frameOk sigs none ⟨.kEval (.nv x) :: rest, env, eval, ret, pend⟩) :
    frameOk sigs none ⟨rest, env, v :: eval, ret, pend⟩ := by
  obtain ⟨-, hchk⟩ := h
  rw [frameChecks] at hchk
  have hΓ : tyLookup (envTyOf env) x = some [typeOfV v] := by
    rw [← envTyOf_lookup env x, hl]
    rfl
  rw [checkSeq_kEval_nv hΓ] at hchk
  refine ⟨by simp, ?_⟩
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
    {env : Env} {eval : List JSValue} {ret : «String»} {pend : Option PendV}
    (h : frameOk sigs none ⟨.kPop :: rest, env, w :: eval, ret, pend⟩) :
    frameOk sigs none ⟨rest, env, eval, ret, pend⟩ := by
  obtain ⟨-, hchk⟩ := h
  rw [frameChecks] at hchk
  simp only [List.map_cons] at hchk
  cases hp : pendAbstr pend with
  | none =>
      rw [checkSeq_kPop hp rfl] at hchk
      refine ⟨by simp, ?_⟩
      rw [frameChecks]
      exact hchk
  | some p' =>
      rw [hp] at hchk
      exfalso
      have hbad : step1 sigs .kPop
          { Γ := envTyOf env, σ := [typeOfV w] :: eval.map (fun v => [typeOfV v]),
            pending := some p' } = none := by
        simp only [step1]
      obtain ⟨why, hrej⟩ := checkSeq_reject_kPop hbad
      rw [hrej] at hchk
      exact hchk

theorem sr_kSet {sigs : SigTable} {x : «String»} {w : JSValue} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»} {pend : Option PendV}
    (h : frameOk sigs none ⟨.kSet x :: rest, env, w :: eval, ret, pend⟩) :
    frameOk sigs none ⟨rest, (x, w) :: env, eval, ret, pend⟩ := by
  obtain ⟨-, hchk⟩ := h
  rw [frameChecks] at hchk
  simp only [List.map_cons] at hchk
  cases hp : pendAbstr pend with
  | none =>
      rw [checkSeq_kSet hp rfl] at hchk
      rw [hp] at hchk
      refine ⟨by simp, ?_⟩
      rw [frameChecks, envTyOf_cons, hp]
      exact hchk
  | some p' =>
      rw [hp] at hchk
      exfalso
      have hbad : step1 sigs (.kSet x)
          { Γ := envTyOf env, σ := [typeOfV w] :: eval.map (fun v => [typeOfV v]),
            pending := some p' } = none := by
        simp only [step1]
      obtain ⟨why, hrej⟩ := checkSeq_reject_kSet hbad
      rw [hrej] at hchk
      exact hchk

/- ## Proof layer Vb: the fold algebra + THE NO-SILENT-FALLS INVARIANT

    Every checkSeq result that is flows with EMPTY FALLS EXITED.
    The load-bearing structural fact of the checker: type_safety's
    frame demand (terminal = exits ∧ falls-empty) transfers across
    instruction boundaries only because no path can fall silent.
    Proven by functional induction over all checkSeq arms (49). -/


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

/-- A rejecting seed absorbs the whole fold. -/
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
    rename_i sigs r w tail t hp ht
    intro fb h hf
    simp only [checkSeq, hp, ht] at h
    have hinj := TCResult.flows.inj h
    subst hinj
    rfl
  case case3 =>
    rename_i sigs r w tail t hp hnt
    intro fb h hf
    simp only [checkSeq, hp] at h
    split at h
    · exact absurd (by assumption) hnt
    · exact TCResult.noConfusion h
  case case4 =>
    rename_i sigs r w tail hp
    intro fb h hf
    simp only [checkSeq, hp] at h
    have hinj := TCResult.flows.inj h
    subst hinj
    rfl
  case case5 =>
    rename_i sigs r w tail hp
    intro fb h hf
    simp only [checkSeq, hp] at h; exact TCResult.noConfusion h
  case case6 =>
    rename_i sigs r w t e rest hσ
    intro fb h hf
    simp only [checkSeq, hσ] at h; exact TCResult.noConfusion h
  case case7 =>
    rename_i sigs r w t e rest ts σ' hσ ih2 ih1
    intro fb h hf
    simp only [checkSeq, hσ] at h
    obtain ⟨-, heq⟩ := fold_merge_flows _ ts vacOk (ne_reject_of_flows h)
    rw [heq] at h
    have hinj := TCResult.flows.inj h
    subst hinj
    rfl
  case case8 =>
    rename_i sigs r w pv rest hpark
    intro fb h hf
    simp only [checkSeq, hpark] at h; exact TCResult.noConfusion h
  case case9 =>
    rename_i sigs r w pv rest w' hpark ih1
    intro fb h hf
    simp only [checkSeq, hpark] at h; exact ih1 fb h hf
  case case10 =>
    rename_i sigs r w v rest hpark
    intro fb h hf
    simp only [checkSeq, hpark] at h; exact TCResult.noConfusion h
  case case11 =>
    rename_i sigs r w v rest w' hpark ih1
    intro fb h hf
    simp only [checkSeq, hpark] at h; exact ih1 fb h hf
  case case12 =>
    rename_i sigs r w x rest hlook ih1
    intro fb h hf
    simp only [checkSeq, hlook] at h; exact ih1 fb h hf
  case case13 =>
    rename_i sigs r w x rest S hlook ih1
    intro fb h hf
    simp only [checkSeq, hlook] at h; exact forkTC_exits h hf ih1
  case case14 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_7] at h; exact ih1 fb h hf
  case case15 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_8] at h; exact ih1 fb h hf
  case case16 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_9] at h; exact ih1 fb h hf
  case case17 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_10] at h; exact ih1 fb h hf
  case case18 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_11] at h; exact ih1 fb h hf
  case case19 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_12] at h; exact ih1 fb h hf
  case case20 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_13] at h; exact ih1 fb h hf
  case case21 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_14] at h; exact ih1 fb h hf
  case case22 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_15] at h; exact ih1 fb h hf
  case case23 =>
    rename_i sigs r w x rest ih1
    intro fb h hf
    rw [checkSeq.eq_16] at h; exact ih1 fb h hf
  case case24 =>
    rename_i sigs r w s x rest ih1
    intro fb h hf
    rw [checkSeq.eq_17] at h; exact ih1 fb h hf
  case case25 =>
    rename_i sigs r w ty x rest ih1
    intro fb h hf
    rw [checkSeq.eq_18] at h; exact ih1 fb h hf
  case case26 =>
    rename_i sigs r w nm x rest ih1
    intro fb h hf
    rw [checkSeq.eq_19] at h; exact ih1 fb h hf
  case case27 =>
    rename_i sigs r w b f x rest hfused ih1
    intro fb h hf
    rw [checkSeq.eq_20, if_pos hfused] at h; exact ih1 fb h hf
  case case28 =>
    rename_i sigs r w b f x rest hfused hty
    intro fb h hf
    simp only [checkSeq, hfused, hty] at h; exact TCResult.noConfusion h
  case case29 =>
    rename_i sigs r w b f x rest hfused S hty ih1
    intro fb h hf
    simp only [checkSeq, hfused, hty] at h; exact markThrow_exits h hf ih1
  case case30 =>
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
    · exact absurd hbool (by assumption)
  case case31 =>
    rename_i sigs r w c body rest t hty hnt
    intro fb h hf
    simp only [checkSeq, hty] at h
    split at h
    · exact absurd (by assumption) hnt
    · exact TCResult.noConfusion h
  case case32 =>
    rename_i sigs r w c body rest hty
    intro fb h hf
    simp only [checkSeq, hty] at h; exact TCResult.noConfusion h
  case case33 =>
    rename_i sigs r w ex rest hdisj hty
    intro fb h hf
    simp only [checkSeq, hty] at h; exact TCResult.noConfusion h
  case case34 =>
    rename_i sigs r w ex rest hdisj S hty ih1
    intro fb h hf
    simp only [checkSeq, hty] at h; exact markThrow_exits h hf ih1
  case case35 =>
    rename_i sigs r w x rest f b dec hdec ih1
    intro fb h hf
    simp only [checkSeq, hdec] at h; exact forkTC_exits h hf ih1
  case case36 =>
    rename_i sigs r w x rest f b hdec hlook
    intro fb h hf
    simp only [checkSeq, hdec, hlook] at h; exact TCResult.noConfusion h
  case case37 =>
    rename_i sigs r w x rest f b hdec S hlook ih1
    intro fb h hf
    simp only [checkSeq, hdec, hlook] at h; exact ih1 fb h hf
  case case38 =>
    rename_i sigs r w x p rest t hT hpred ih1
    intro fb h hf
    simp only [checkSeq, hT] at h; exact forkTC_exits h hf ih1
  case case39 =>
    rename_i sigs r w x p rest hT hlook hpred
    intro fb h hf
    simp only [checkSeq, hT, hlook] at h; exact TCResult.noConfusion h
  case case40 =>
    rename_i sigs r w x p rest hT S hlook hpred ih1
    intro fb h hf
    simp only [checkSeq, hT, hlook] at h; exact ih1 fb h hf
  case case41 =>
    rename_i sigs r w c body rest hpop
    intro fb h hf
    simp only [checkSeq, hpop] at h; exact TCResult.noConfusion h
  case case42 =>
    rename_i sigs r w c body rest σ' hpop ih2 ih1
    intro fb h hf
    simp only [checkSeq, hpop] at h
    cases hbody : checkSeq sigs r { Γ := w.Γ, σ := σ', pending := w.pending } body with
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
    rename_i sigs r w x body rest hpop
    intro fb h hf
    simp only [checkSeq, hpop] at h; exact TCResult.noConfusion h
  case case44 =>
    rename_i sigs r w x body rest σ' hpop ih2 ih1
    intro fb h hf
    simp only [checkSeq, hpop] at h
    cases hbody : checkSeq sigs r { Γ := (x, langT) :: w.Γ, σ := σ', pending := w.pending } body with
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
  case case45 =>
    rename_i sigs r w x elems body rest ih2 ih1
    intro fb h hf
    simp only [checkSeq] at h
    cases hbody : checkSeq sigs r { Γ := (x, langT) :: w.Γ, σ := w.σ, pending := w.pending } body with
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
  case case46 =>
    rename_i sigs r w rest hσ
    intro fb h hf
    simp only [checkSeq, hσ] at h; exact TCResult.noConfusion h
  case case47 =>
    rename_i sigs r w rest ts σ' hσ ih1
    intro fb h hf
    simp only [checkSeq, hσ] at h
    obtain ⟨-, heq⟩ := fold_merge_flows _ ts vacOk (ne_reject_of_flows h)
    rw [heq] at h
    have hinj := TCResult.flows.inj h
    subst hinj
    rfl
  case case48 =>
    rename_i sigs r w i rest hdisj hstep
    intro fb h hf
    simp only [checkSeq, hstep] at h; exact TCResult.noConfusion h
  case case49 =>
    rename_i sigs r w i rest hdisj ws' hstep ih1
    intro fb h hf
    simp only [checkSeq, hstep] at h; exact forkTC_exits h hf ih1

/- ## Proof layer VI: the pending-protocol identities -/

theorem checkSeq_kTest_normal {sigs : SigTable} {r : Ty} {W : World} {t : Ty}
    {rest : List Instr} (hpn : W.pending = some (.normal t)) :
    checkSeq sigs r W (.kTest :: rest)
      = checkSeq sigs r { W with σ := [.isValue (.boolean Bool.false)] :: W.σ } rest := by
  simp only [checkSeq, step1, List.foldl, hpn, mergeTC_noFlows, forkTC_cons]

theorem checkSeq_kTest_throw {sigs : SigTable} {r : Ty} {W : World}
    {rest : List Instr} (hpn : W.pending = some Pending.throw) :
    checkSeq sigs r W (.kTest :: rest)
      = checkSeq sigs r { W with σ := [.isValue (.boolean Bool.true)] :: W.σ } rest := by
  simp only [checkSeq, step1, List.foldl, hpn, mergeTC_noFlows, forkTC_cons]

theorem checkSeq_kUnwrap_normal {sigs : SigTable} {r : Ty} {W : World} {t : Ty}
    {rest : List Instr} (hpn : W.pending = some (.normal t)) :
    checkSeq sigs r W (.kUnwrap :: rest)
      = checkSeq sigs r { W with σ := t :: W.σ, pending := none } rest := by
  simp only [checkSeq, step1, List.foldl, hpn, mergeTC_noFlows, forkTC_cons]

theorem checkSeq_pWrapC {sigs : SigTable} {r : Ty} {W : World} {ts : Ty} {σ' : List Ty}
    {rest : List Instr} (hpn : W.pending = none) (hσ : W.σ = ts :: σ') :
    checkSeq sigs r W (.kPrim1 .pWrapC :: rest)
      = checkSeq sigs r { W with σ := σ', pending := some (.normal ts) } rest := by
  simp only [checkSeq, step1, List.foldl, parkPending, Option.map_some,
             hpn, hσ, List.append_nil, mergeTC_noFlows, forkTC_cons]

theorem checkSeq_pThrowC {sigs : SigTable} {r : Ty} {W : World} {ts : Ty} {σ' : List Ty}
    {rest : List Instr} (hpn : W.pending = none) (hσ : W.σ = ts :: σ') :
    checkSeq sigs r W (.kPrim1 .pThrowC :: rest)
      = checkSeq sigs r { W with σ := σ', pending := some Pending.throw } rest := by
  simp only [checkSeq, step1, List.foldl, parkPending, Option.map_some,
             hpn, hσ, List.append_nil, mergeTC_noFlows, forkTC_cons]

/- ## Proof layer VII: the pending-protocol sr arms

    The machine parks in Fr.pend; the static world's pending is its
    pointwise abstraction (pendAbstr). The arms below are the
    commutations of that square — each is the pending-identity
    transported across frameChecks. -/

/-- Parking identities. -/
theorem checkSeq_kEval_compl_normal {sigs : SigTable} {r : Ty} {W : World} {pv : JSValue}
    {rest : List Instr} (hpn : W.pending = none) :
    checkSeq sigs r W (.kEval (.const (.compl Bool.false pv)) :: rest)
      = checkSeq sigs r { W with pending := some (.normal [typeOfV pv]) } rest := by
  simp only [checkSeq, parkPending, hpn]

theorem checkSeq_kEval_compl_throw {sigs : SigTable} {r : Ty} {W : World} {v : JSValue}
    {rest : List Instr} (hpn : W.pending = none) :
    checkSeq sigs r W (.kEval (.const (.compl Bool.true v)) :: rest)
      = checkSeq sigs r { W with pending := some Pending.throw } rest := by
  simp only [checkSeq, parkPending, hpn]

theorem sr_kEval_compl_normal {sigs : SigTable} {pv : JSValue} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameOk sigs none ⟨.kEval (.const (.compl Bool.false pv)) :: rest, env, eval, ret, none⟩) :
    frameOk sigs none ⟨rest, env, eval, ret, some (.normal pv)⟩ := by
  obtain ⟨-, hchk⟩ := h
  rw [frameChecks] at hchk
  rw [checkSeq_kEval_compl_normal rfl] at hchk
  refine ⟨by simp, ?_⟩
  rw [frameChecks]
  exact hchk

theorem sr_kEval_compl_throw {sigs : SigTable} {v : JSValue} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameOk sigs none ⟨.kEval (.const (.compl Bool.true v)) :: rest, env, eval, ret, none⟩) :
    frameOk sigs none ⟨rest, env, eval, ret, some PendV.throw⟩ := by
  obtain ⟨-, hchk⟩ := h
  rw [frameChecks] at hchk
  rw [checkSeq_kEval_compl_throw rfl] at hchk
  refine ⟨by simp, ?_⟩
  rw [frameChecks]
  exact hchk

theorem sr_kTest_normal {sigs : SigTable} {pv : JSValue} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameOk sigs none ⟨.kTest :: rest, env, eval, ret, some (.normal pv)⟩) :
    frameOk sigs none
      ⟨rest, env, .boolean Bool.false :: eval, ret, some (.normal pv)⟩ := by
  obtain ⟨-, hchk⟩ := h
  rw [frameChecks] at hchk
  rw [checkSeq_kTest_normal rfl] at hchk
  refine ⟨by simp, ?_⟩
  rw [frameChecks]
  simp only [List.map_cons, typeOfV]
  exact hchk

theorem sr_kTest_throw {sigs : SigTable} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameOk sigs none ⟨.kTest :: rest, env, eval, ret, some PendV.throw⟩) :
    frameOk sigs none
      ⟨rest, env, .boolean Bool.true :: eval, ret, some PendV.throw⟩ := by
  obtain ⟨-, hchk⟩ := h
  rw [frameChecks] at hchk
  rw [checkSeq_kTest_throw rfl] at hchk
  refine ⟨by simp, ?_⟩
  rw [frameChecks]
  simp only [List.map_cons, typeOfV]
  exact hchk

theorem sr_kUnwrap {sigs : SigTable} {pv : JSValue} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameOk sigs none ⟨.kUnwrap :: rest, env, eval, ret, some (.normal pv)⟩) :
    frameOk sigs none ⟨rest, env, pv :: eval, ret, none⟩ := by
  obtain ⟨-, hchk⟩ := h
  rw [frameChecks] at hchk
  rw [checkSeq_kUnwrap_normal rfl] at hchk
  refine ⟨by simp, ?_⟩
  rw [frameChecks]
  simp only [List.map_cons]
  exact hchk

theorem sr_pWrapC {sigs : SigTable} {v : JSValue} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameOk sigs none ⟨.kPrim1 .pWrapC :: rest, env, v :: eval, ret, none⟩) :
    frameOk sigs none ⟨rest, env, eval, ret, some (.normal v)⟩ := by
  obtain ⟨-, hchk⟩ := h
  rw [frameChecks] at hchk
  simp only [List.map_cons] at hchk
  rw [checkSeq_pWrapC rfl rfl] at hchk
  refine ⟨by simp, ?_⟩
  rw [frameChecks]
  exact hchk

theorem sr_pThrowC {sigs : SigTable} {v : JSValue} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameOk sigs none ⟨.kPrim1 .pThrowC :: rest, env, v :: eval, ret, none⟩) :
    frameOk sigs none ⟨rest, env, eval, ret, some PendV.throw⟩ := by
  obtain ⟨-, hchk⟩ := h
  rw [frameChecks] at hchk
  simp only [List.map_cons] at hchk
  rw [checkSeq_pThrowC rfl rfl] at hchk
  refine ⟨by simp, ?_⟩
  rw [frameChecks]
  exact hchk

/- ## Proof layer VIII: monotonicity of the flat lattice ops -/

/-- Meet coverage: refining the left argument refines the meet. -/
theorem tmovesV_meet_left {a a' b : VTy}
    (hle : tmovesV a' a = Bool.true) (hm : meetAtom a' b = some m') :
    ∃ m, meetAtom a b = some m ∧ tmovesV m' m = Bool.true := by
  cases a' with
  | anyValue c =>
      cases a with
      | anyValue c₂ =>
          simp only [tmovesV, decide_eq_true_eq] at hle
          subst hle
          exact ⟨m', hm, tmovesV_refl m'⟩
      | isValue w => exfalso; cases w <;> simp_all [tmovesV, tagOf]
      | desc fs => simp [tmovesV] at hle
      | notPresent => simp [tmovesV] at hle
  | isValue w =>
      cases a with
      | anyValue c =>
          simp only [tmovesV, decide_eq_true_eq] at hle
          -- tagOf w = c; the meet keeps isValue-side witnesses
          cases b with
          | anyValue c₃ =>
              simp only [meetAtom, decide_eq_true_eq] at hm
              split at hm
              · next htag =>
                  have hcc : c = c₃ := by rw [← hle, htag]
                  injection hm with hmi
                  subst hmi
                  exact ⟨.anyValue c, by simp [meetAtom, hcc],
                    by simp [tmovesV, hle]⟩
              · simp at hm
          | isValue w₃ =>
              simp only [meetAtom, beq_iff_eq] at hm
              split at hm
              · next hw =>
                  have hw' : w = w₃ := by
                    cases w <;> simp_all [beq_iff_eq]
                  have htag : tagOf w₃ = c := by rw [← hw', hle]
                  injection hm with hmi
                  subst hmi
                  exact ⟨.isValue w₃, by simp [meetAtom, htag],
                    by simp [tmovesV, hw']⟩
              · simp at hm
          | desc fs => simp [meetAtom] at hm
          | notPresent => simp [meetAtom] at hm
      | isValue w₂ =>
          simp only [tmovesV, beq_iff_eq] at hle
          subst hle
          exact ⟨m', hm, tmovesV_refl m'⟩
      | desc fs => simp [tmovesV] at hle
      | notPresent => simp [tmovesV] at hle
  | desc fs =>
      cases a with
      | anyValue c =>
          cases c with
          | desc =>
              cases b with
              | anyValue c₃ =>
                  cases c₃ with
                  | desc =>
                      injection hm with hmi
                      subst hmi
                      exact ⟨.anyValue .desc, by simp [meetAtom], by simp [tmovesV]⟩
                  | undef => simp [meetAtom] at hm
                  | null => simp [meetAtom] at hm
                  | bool => simp [meetAtom] at hm
                  | num => simp [meetAtom] at hm
                  | str => simp [meetAtom] at hm
                  | obj => simp [meetAtom] at hm
                  | list => simp [meetAtom] at hm
              | isValue w => simp [meetAtom] at hm
              | desc fs₃ =>
                  simp only [meetAtom, decide_eq_true_eq] at hm
                  split at hm
                  · next hfs =>
                      injection hm with hmi
                      subst hmi
                      exact ⟨.desc fs₃, by simp [meetAtom, hfs],
                        by simp [tmovesV, hfs]⟩
                  · simp at hm
              | notPresent => simp [meetAtom] at hm
          | undef => simp [tmovesV] at hle
          | null => simp [tmovesV] at hle
          | bool => simp [tmovesV] at hle
          | num => simp [tmovesV] at hle
          | str => simp [tmovesV] at hle
          | obj => simp [tmovesV] at hle
          | list => simp [tmovesV] at hle
      | isValue w => simp [tmovesV] at hle
      | desc fs₂ =>
          simp only [tmovesV, decide_eq_true_eq] at hle
          subst hle
          exact ⟨m', hm, tmovesV_refl m'⟩
      | notPresent => simp [tmovesV] at hle
  | notPresent =>
      cases a with
      | notPresent => exact ⟨m', hm, tmovesV_refl m'⟩
      | anyValue c => simp [tmovesV] at hle
      | isValue w => simp [tmovesV] at hle
      | desc fs => simp [tmovesV] at hle

/-- Removal covariance: a kept refined atom is covered by a kept
    coarse atom. -/
theorem removeTy_cov {S S' T : Ty}
    (h : ∀ a' ∈ S', ∃ a ∈ S, tmovesV a' a = Bool.true) :
    ∀ m' ∈ removeTy S' T, ∃ m ∈ removeTy S T, tmovesV m' m = Bool.true := by
  intro m' hm'
  simp only [removeTy, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true] at hm' ⊢
  obtain ⟨ha', hkeep⟩ := hm'
  obtain ⟨a, ha, hle⟩ := h m' ha'
  refine ⟨a, ⟨ha, ?_⟩, hle⟩
  cases hany : (T.any fun b => tmovesV a b) with
  | false => rfl
  | true =>
      obtain ⟨b, hb, hba⟩ := List.any_eq_true.mp hany
      rw [List.any_eq_true.mpr ⟨b, hb, tmovesV_trans hle hba⟩] at hkeep
      exact Bool.noConfusion hkeep

/-- Meet covariance at the flat-type level. -/
theorem meetTy_cov {S S' T : Ty}
    (h : ∀ a' ∈ S', ∃ a ∈ S, tmovesV a' a = Bool.true) :
    ∀ m' ∈ meetTy S' T, ∃ m ∈ meetTy S T, tmovesV m' m = Bool.true := by
  intro m' hm'
  simp only [meetTy, List.mem_flatMap] at hm' ⊢
  obtain ⟨a', ha', b, hb, hma⟩ := hm'
  obtain ⟨a, ha, hle⟩ := h a' ha'
  cases hma2 : meetAtom a' b with
  | none => rw [hma2] at hma; cases hma
  | some mm =>
      rw [hma2, List.mem_singleton] at hma
      obtain ⟨m, hm2, hmm⟩ := tmovesV_meet_left hle hma2
      subst hma
      refine ⟨m, ⟨a, ha, b, hb, ?_⟩, hmm⟩
      simp only [hm2, List.mem_singleton]

/-- Stack coverage: cons projection. -/
theorem stackLe_cons {t u : Ty} {σ τ : List Ty}
    (h : stackLe (t :: σ) (u :: τ)) : stackLe σ τ ∧ tyLe t u := by
  obtain ⟨hlen, hcov⟩ := h
  constructor
  · refine ⟨by simpa using hlen, ?_⟩
    intro i m hm n hn
    exact hcov (i + 1) m hm n (by simpa using hn)
  · exact hcov 0 t (by simp) u (by simp)

/- ## Proof layer IX: split monotonicity -/

/-- World coverage: every refined world is covered by a coarse one. -/
def worldsLe (ws' ws : Worlds) : Prop :=
  ∀ w' ∈ ws', ∃ w ∈ ws, worldLe w' w

theorem tyLe_trans {t u v : Ty} (h₁ : tyLe t u) (h₂ : tyLe u v) : tyLe t v :=
  tmoves_trans h₁ h₂

theorem envLe_cons {x : «String»} {t u : Ty} {Γ Δ : TyEnv}
    (h : tyLe t u) (hrest : envLe Γ Δ) : envLe ((x, t) :: Γ) ((x, u) :: Δ) := by
  intro y s hs
  by_cases hxy : x = y
  · rw [hxy] at hs ⊢
    simp only [tyLookup, beq_self_eq_true, if_true] at hs ⊢
    cases hs
    exact ⟨u, rfl, h⟩
  · simp only [tyLookup, beq_iff_eq, hxy, if_false] at hs ⊢
    exact hrest y s hs

theorem meetTy_nil (T : Ty) : meetTy [] T = [] := rfl

theorem removeTy_nil (T : Ty) : removeTy [] T = [] := rfl

theorem tyLe_iff {t u : Ty} :
    tyLe t u ↔ (∀ a ∈ t, ∃ b ∈ u, tmovesV a b = Bool.true) := by
  unfold tyLe tmoves
  rw [List.all_eq_true]
  constructor
  · intro h a ha
    exact List.any_eq_true.mp (h a ha)
  · intro h a ha
    exact List.any_eq_true.mpr (h a ha)

theorem stackLe_cons_same {t : Ty} {σ τ : List Ty}
    (h : stackLe σ τ) : stackLe (t :: σ) (t :: τ) := by
  obtain ⟨hlen, hcov⟩ := h
  refine ⟨by simpa using hlen, ?_⟩
  intro i m hm u hu
  cases i with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.mem_some] at hm hu
      subst hm; subst hu; exact tmoves_refl _
  | succ j =>
      simp only [List.getElem?_cons_succ] at hm hu
      exact hcov j m hm u hu

/-- Nonempty transfer under coverage. -/
theorem cover_ne {l' l : List VTy}
    (hc : ∀ m' ∈ l', ∃ m ∈ l, tmovesV m' m = Bool.true)
    (hne' : l' ≠ []) : l ≠ [] := by
  rintro rfl
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, m₀ ∈ l' := by
    cases l' with
    | nil => exact absurd rfl hne'
    | cons m ms => exact ⟨m, List.Mem.head _⟩
  obtain ⟨m, hm, -⟩ := hc m₀ hm₀
  exact absurd hm (by simp)

theorem split1_cov {x : «String»} {T : Ty} {w' w : World}
    (hle : worldLe w' w) {u' : World} (hu' : u' ∈ split1 x T w') :
    ∃ u ∈ split1 x T w, worldLe u' u := by
  obtain ⟨hΓ, hσ, hp⟩ := hle
  simp only [split1] at hu' ⊢
  cases hlk' : tyLookup w'.Γ x with
  | none => rw [hlk'] at hu'; exact absurd hu' (by simp)
  | some S' =>
      rw [hlk'] at hu'
      obtain ⟨S, hSmem, hSle⟩ := hΓ x S' (by rw [hlk']; exact Option.mem_some_self _)
      cases hlk : tyLookup w.Γ x with
      | none => rw [hlk] at hSmem; exact absurd hSmem (by simp)
      | some S₂ =>
          rw [hlk] at hSmem
          have hSlk : S = S₂ := Eq.symm (by simpa using hSmem)
          rw [hSlk] at hSle
          have hcover : ∀ a ∈ S', ∃ b ∈ S₂, tmovesV a b = Bool.true :=
            tyLe_iff.mp hSle
          have hmeetcov : ∀ m ∈ meetTy S' T, ∃ n ∈ meetTy S₂ T,
              tmovesV m n = Bool.true := meetTy_cov hcover
          have hremcov : ∀ m ∈ removeTy S' T, ∃ n ∈ removeTy S₂ T,
              tmovesV m n = Bool.true := removeTy_cov hcover
          simp only [List.mem_append] at hu' ⊢
          cases hu' with
          | inl hmem =>
              cases hmeet' : meetTy S' T with
              | nil => rw [hmeet'] at hmem; exact absurd hmem (by simp)
              | cons m' ms' =>
                  rw [hmeet'] at hmem hmeetcov
                  simp only [List.mem_singleton] at hmem
                  subst hmem
                  have hneS : meetTy S₂ T ≠ [] :=
                    cover_ne hmeetcov (List.cons_ne_nil m' ms')
                  cases hmeet : meetTy S₂ T with
                  | nil => rw [hmeet] at hneS; exact (hneS rfl).elim
                  | cons m ms =>
                      rw [hmeet] at hmeetcov
                      exact ⟨{ Γ := (x, m :: ms) :: w.Γ,
                               σ := [.isValue (.boolean Bool.true)] :: w.σ,
                               pending := w.pending }, Or.inl (List.Mem.head _),
                             ⟨envLe_cons (tyLe_iff.mpr hmeetcov) hΓ,
                              stackLe_cons_same (t := [.isValue (.boolean Bool.true)]) hσ, hp⟩⟩
          | inr hmem =>
              cases hrem' : removeTy S' T with
              | nil => rw [hrem'] at hmem; exact absurd hmem (by simp)
              | cons m' ms' =>
                  rw [hrem'] at hmem hremcov
                  simp only [List.mem_singleton] at hmem
                  subst hmem
                  have hneS : removeTy S₂ T ≠ [] :=
                    cover_ne hremcov (List.cons_ne_nil m' ms')
                  cases hrem : removeTy S₂ T with
                  | nil => rw [hrem] at hneS; exact (hneS rfl).elim
                  | cons m ms =>
                      rw [hrem] at hremcov
                      exact ⟨{ Γ := (x, m :: ms) :: w.Γ,
                               σ := [.isValue (.boolean Bool.false)] :: w.σ,
                               pending := w.pending }, Or.inr (List.Mem.head _),
                             ⟨envLe_cons (tyLe_iff.mpr hremcov) hΓ,
                              stackLe_cons_same (t := [.isValue (.boolean Bool.false)]) hσ, hp⟩⟩

theorem worldsLe_split {x : «String»} {T : Ty} {ws ws' : Worlds}
    (hcov : worldsLe ws' ws) :
    ∀ u' ∈ ws'.flatMap (split1 x T), ∃ u ∈ ws.flatMap (split1 x T), worldLe u' u := by
  intro u' hu'
  simp only [List.mem_flatMap] at hu'
  obtain ⟨w', hw', hu'⟩ := hu'
  obtain ⟨w, hw, hle⟩ := hcov w' hw'
  obtain ⟨u, hu, hle'⟩ := split1_cov hle hu'
  refine ⟨u, ?_, hle'⟩
  simp only [List.mem_flatMap]
  exact ⟨w, hw, hu⟩

/- ## Proof layer X: the per-world static step is monotone -/

/-- Subject-weakening: a refined slot satisfies every demand the
    coarse slot satisfies. -/
theorem tmoves_subj_mono {t u T : Ty}
    (hle : tyLe t u) (hpop : tmoves u T = Bool.true) :
    tmoves t T = Bool.true := by
  rw [tyLe_iff] at hle
  have hu := tyLe_iff.mp hpop
  show tyLe t T
  rw [tyLe_iff]
  intro a ha
  obtain ⟨b, hb, hab⟩ := hle a ha
  obtain ⟨c, hc, hcb⟩ := hu b hb
  exact ⟨c, hc, tmovesV_trans hab hcb⟩

theorem popTy_mono {T : Ty} {σ' σ : List Ty} {σ₂ : List Ty}
    (hcov : stackLe σ' σ) (hpop : popTy T σ = some σ₂) :
    ∃ σ₂', popTy T σ' = some σ₂' ∧ stackLe σ₂' σ₂ := by
  cases hσ : σ with
  | nil =>
      exfalso
      have hnone : popTy T [] = none := rfl
      rw [hσ, hnone] at hpop
      cases hpop
  | cons ts σ₀ =>
      rw [hσ] at hpop hcov
      cases hσ' : σ' with
      | nil =>
          exfalso
          rw [hσ'] at hcov
          exact absurd hcov.1 (by simp)
      | cons ts' σ₀' =>
          rw [hσ'] at hcov
          obtain ⟨hrest, hhd⟩ := stackLe_cons hcov
          have hpass : tmoves ts' T = Bool.true :=
            tmoves_subj_mono hhd (by
              simp only [popTy] at hpop
              cases hif : tmoves ts T with
              | true => rfl
              | false =>
                  rw [hif] at hpop
                  cases hpop)
          -- σ₂ = σ₀ (the coarse pop returned the tail)
          have hσ₂ : σ₂ = σ₀ := by
            simp only [popTy] at hpop
            cases hif : tmoves ts T with
            | true =>
                rw [hif] at hpop
                rw [if_pos rfl] at hpop
                exact Option.some.inj hpop.symm
            | false =>
                rw [hif] at hpop
                cases hpop
          subst hσ₂
          exact ⟨σ₀', by
            simp only [popTy, hpass]
            rfl, hrest⟩

/- ## Next (the monotonicity induction's remaining pieces):

    step1_mono (per-world, ~12 arms: park/park/pop-push/split-over-
    judgements/drops/Γ-ext; needs popTyN-mono, popA-mono, drop-
    coverage, popArgs-mono), stepWorlds_mono (mapM lift), then the
    checkSeq worldLe induction with the result-shape transfer
    (exits/throws preserved, falls covered), then the remaining sr
    arms (kTestVar exact+refined, kPrim1-generic via mono, kCall,
    kRet delivery, loops, kMkList/kNewSlot/kIMeth), then the master
    frames case and type_safety. -/

/- ## Proof layer XI: monotonicity plumbing (drops, pops, args) -/

theorem stackLe_drop {σ' σ : List Ty} (h : stackLe σ' σ) (n : Nat) :
    stackLe (σ'.drop n) (σ.drop n) := by
  obtain ⟨hlen, hcov⟩ := h
  refine ⟨by simp [hlen], ?_⟩
  intro i t ht u hu
  have h1 : t ∈ σ'[n + i]? := by
    have := ht
    rw [List.getElem?_drop] at this
    exact this
  have h2 : u ∈ σ[n + i]? := by
    have := hu
    rw [List.getElem?_drop] at this
    exact this
  exact hcov (n + i) t h1 u h2

theorem stackLe_cons_le {t u : Ty} {σ' σ : List Ty}
    (h : stackLe σ' σ) (htu : tyLe t u) : stackLe (t :: σ') (u :: σ) := by
  obtain ⟨hlen, hcov⟩ := h
  refine ⟨by simp [hlen], ?_⟩
  intro i m hm n hn
  cases i with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.mem_some] at hm hn
      subst hm; subst hn; exact htu
  | succ j =>
      simp only [List.getElem?_cons_succ] at hm hn
      exact hcov j m hm n hn

theorem popTyN_mono {T : Ty} : ∀ (n : Nat) {σ' σ σ₂ : List Ty},
    stackLe σ' σ → popTyN n T σ = some σ₂ →
    ∃ σ₂', popTyN n T σ' = some σ₂' ∧ stackLe σ₂' σ₂ := by
  intro n
  induction n with
  | zero =>
      intro σ' σ σ₂ hcov h
      cases h
      exact ⟨σ', rfl, hcov⟩
  | succ n ih =>
      intro σ' σ σ₂ hcov h
      rw [popTyN] at h
      cases hpop : popTy T σ with
      | none => rw [hpop] at h; cases h
      | some σ₁ =>
          rw [hpop] at h
          obtain ⟨σ₁', hp₁, hc₁⟩ := popTy_mono hcov hpop
          obtain ⟨σ₂', hp₂, hc₂⟩ := ih hc₁ h
          refine ⟨σ₂', ?_, hc₂⟩
          simp only [popTyN, hp₁, hp₂]

theorem popA_mono {t : VTy} {σ' σ σ₂ : List Ty}
    (hcov : stackLe σ' σ) (h : popA t σ = some σ₂) :
    ∃ σ₂', popA t σ' = some σ₂' ∧ stackLe σ₂' σ₂ := popTy_mono hcov h

theorem stackLe_take {σ' σ : List Ty} (h : stackLe σ' σ) (k : Nat) :
    stackLe (σ'.take k) (σ.take k) := by
  induction k generalizing σ' σ with
  | zero =>
      refine ⟨rfl, ?_⟩
      intro i t ht
      exact absurd ht (by simp [List.getElem?_nil])
  | succ k ih =>
      cases σ' with
      | nil =>
          cases σ with
          | nil =>
              refine ⟨rfl, ?_⟩
              intro i t ht
              exact absurd ht (by simp [List.getElem?_nil])
          | cons b m => exact absurd h.1 (by simp)
      | cons a t' =>
          cases σ with
          | nil => exact absurd h.1 (by simp)
          | cons b m =>
              simp only [List.take]
              exact stackLe_cons_le (ih (stackLe_cons h).1) (stackLe_cons h).2

theorem mem_getElem?_lt {l : List Ty} {i : Nat} {a : Ty} (h : a ∈ l[i]?) :
    i < l.length := by
  by_cases hlt : i < l.length
  · exact hlt
  · exfalso
    have hn : l[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    rw [hn] at h
    exact absurd h (by simp)

theorem stackLe_reverse {σ' σ : List Ty} (h : stackLe σ' σ) :
    stackLe σ'.reverse σ.reverse := by
  obtain ⟨hlen, hcov⟩ := h
  refine ⟨by simp [hlen], ?_⟩
  intro i t ht u hu
  have hb : i < σ'.length := by
    have := mem_getElem?_lt (l := σ'.reverse) ht
    simpa using this
  have ht2 : t ∈ σ'[σ'.length - 1 - i]? := by
    rw [← List.getElem?_reverse hb]
    exact ht
  have hu2 : u ∈ σ[σ'.length - 1 - i]? := by
    rw [hlen]
    have hbs : i < σ.length := by omega
    rw [← List.getElem?_reverse hbs]
    exact hu
  exact hcov _ t ht2 u hu2

theorem leTy_of_stackLe {l₁ l₂ : List Ty} (h : stackLe l₁ l₂) : leTy l₁ l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => rfl
      | cons b m => exact absurd h.1 (by simp)
  | cons a t ih =>
      cases l₂ with
      | nil => exact absurd h.1 (by simp)
      | cons b m =>
          rw [leTy, Bool.and_eq_true]
          exact ⟨(stackLe_cons h).2, ih (stackLe_cons h).1⟩

theorem leTy_mono {ts' ts ps : List Ty} (h₁ : leTy ts' ts) (h₂ : leTy ts ps) :
    leTy ts' ps := by
  induction ts' generalizing ts ps with
  | nil =>
      cases ts with
      | nil => cases ps with
        | nil => rfl
        | cons p ps' => simp [leTy] at h₂
      | cons t ts' => simp [leTy] at h₁
  | cons a t' ih =>
      cases ts with
      | nil => simp [leTy] at h₁
      | cons b ts' =>
          cases ps with
          | nil => simp [leTy] at h₂
          | cons p ps' =>
              simp only [leTy, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂ ⊢
              refine ⟨tmoves_subj_mono h₁.1 h₂.1, ih h₁.2 h₂.2⟩

theorem popArgs_mono {ps σ' σ : List Ty}
    (hcov : stackLe σ' σ) (h : popArgs ps σ = Bool.true) :
    popArgs ps σ' = Bool.true := by
  unfold popArgs at h ⊢
  have hlen : σ'.length = σ.length := hcov.1
  rw [hlen]
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  refine ⟨h.1, ?_⟩
  have hcover : stackLe (σ'.take ps.length).reverse (σ.take ps.length).reverse :=
    stackLe_reverse (stackLe_take hcov ps.length)
  exact leTy_mono (leTy_of_stackLe hcover) h.2

/- ## Proof layer XII: step1_mono (the per-world static step) -/

theorem pendLe_refl (p : Option Pending) : pendLe p p := by
  cases p with
  | none => trivial
  | some q =>
      cases q with
      | normal t => exact tmoves_refl t
      | throw => trivial

theorem pendLe_none {p' p : Option Pending} (h : pendLe p' p) (hp : p = none) :
    p' = none := by
  cases p' with
  | none => rfl
  | some q =>
      cases p with
      | none => exact absurd (h) (by simp [pendLe] at *)
      | some q₂ => exact absurd hp (by simp)

theorem parkPending_some (p : Pending) (w : World) (hp : w.pending = none) :
    parkPending p w = some { w with pending := some p } := by
  rw [parkPending, hp]

theorem step1_prim_mono {sigs : SigTable} {p : Prim} {w' w : World}
    (hle : worldLe w' w) {ws₂ : Worlds} (hst : step1 sigs (.kPrim1 p) w = some ws₂) :
    ∃ ws₂', step1 sigs (.kPrim1 p) w' = some ws₂' ∧ worldsLe ws₂' ws₂ := by
  obtain ⟨hΓ, hσ, hp⟩ := hle
  cases p with

      | pWrapC =>
          simp only [step1] at hst
          cases hsl : w.σ with
          | nil => rw [hsl] at hst; dsimp only at hst; cases hst
          | cons t σ₁ =>
              rw [hsl] at hst
              cases hpn : w.pending with
              | some q => rw [hpn] at hst; cases hst
              | none =>
                  rw [hpn] at hst
                  simp only [parkPending] at hst
                  cases hst
                  have hp' : w'.pending = none := pendLe_none hp hpn
                  rw [hsl] at hσ
                  cases hs : w'.σ with
                  | nil => rw [hs] at hσ; exact absurd hσ.1 (by simp)
                  | cons t' σ₁' =>
                      rw [hs] at hσ
                      obtain ⟨hrest, hhead⟩ := stackLe_cons hσ
                      refine ⟨[{ w' with σ := σ₁', pending := some (.normal t') }],
                        by simp only [step1, hs, hp', parkPending_some, Option.map_some], ?_⟩
                      intro u hu
                      simp only [List.mem_singleton] at hu
                      subst u
                      exact ⟨_, List.Mem.head _, hΓ, hrest, hhead⟩
      | pThrowC =>
          simp only [step1] at hst
          cases hsl : w.σ with
          | nil => rw [hsl] at hst; dsimp only at hst; cases hst
          | cons t σ₁ =>
              rw [hsl] at hst
              cases hpn : w.pending with
              | some q => rw [hpn] at hst; cases hst
              | none =>
                  rw [hpn] at hst
                  simp only [parkPending] at hst
                  cases hst
                  have hp' : w'.pending = none := pendLe_none hp hpn
                  rw [hsl] at hσ
                  cases hs : w'.σ with
                  | nil => rw [hs] at hσ; exact absurd hσ.1 (by simp)
                  | cons t' σ₁' =>
                      rw [hs] at hσ
                      obtain ⟨hrest, _⟩ := stackLe_cons hσ
                      refine ⟨[{ w' with σ := σ₁', pending := some .throw }],
                        by simp only [step1, hs, hp', parkPending_some, Option.map_some], ?_⟩
                      intro u hu
                      simp only [List.mem_singleton] at hu
                      subst u
                      refine ⟨_, List.Mem.head _, hΓ, hrest, by trivial⟩
      | pPred f b =>
          simp only [step1, primTys] at hst
          cases hst
          exact ⟨[w'], by simp [step1, primTys], by
            intro u hu
            simp only [List.mem_singleton] at hu
            subst hu
            exact ⟨w, List.Mem.head _, hΓ, hσ, hp⟩⟩
      | pIsObj | pIsNotObj | pIsNotU | pHasCall | pHasCtor | pIsU
      | pIsTrue | pIsFalse | pNullOrUnd | pIsNull | pIsType s | pHasField s
      | pIsStr s =>
          -- primTys = (anyT, [.anyValue .bool]): pop any, push the
          -- boolean union (EQUAL on both sides)
          simp only [step1, primTys] at hst
          cases hpn : w.pending with
          | some q => rw [hpn] at hst; cases hst
          | none =>
              have hp' : w'.pending = none := pendLe_none hp hpn
              rw [hpn] at hst
              try dsimp only at hst
              cases hpop : popTy anyT w.σ with
              | none => rw [hpop] at hst; cases hst
              | some σ₂ =>
                  rw [hpop] at hst
                  cases hst
                  obtain ⟨σ₂', hpop', hc₂⟩ := popTy_mono hσ hpop
                  refine ⟨[{ w' with σ := [.anyValue .bool] :: σ₂' }], by
                    simp only [step1, primTys, hp', hpop'], ?_⟩
                  intro u hu
                  simp only [List.mem_singleton] at hu
                  subst u
                  exact ⟨{ w with σ := [.anyValue .bool] :: σ₂, pending := none },
                    List.Mem.head _, hΓ, stackLe_cons_same hc₂, by rw [hp']; exact pendLe_refl _⟩
      | pDescField s =>
          -- tout depends on s; mono only needs tin/tout EQUAL on both
          -- sides, so abstract over the primTys decomposition
          simp only [step1] at hst
          generalize hpt : primTys (Prim.pDescField s) = pr at hst
          cases pr with
          | none =>
              exfalso
              dsimp only at hst
              cases hst
              match hs : s with
              | "GetPrototypeOf" | "Value" | "Getter" | "Setter"
              | "Writable" | "Enumerable" | "Configurable" =>
                  simp [primTys] at hpt
              | _ => simp [primTys] at hpt
          | some pr₂ =>
              obtain ⟨tin, tout⟩ := pr₂
              dsimp only at hst
              cases hpn : w.pending with
              | some q => rw [hpn] at hst; cases hst
              | none =>
                  have hp' : w'.pending = none := pendLe_none hp hpn
                  rw [hpn] at hst
                  cases hpop : popTy tin w.σ with
                  | none => rw [hpop] at hst; cases hst
                  | some σ₂ =>
                      rw [hpop] at hst
                      cases hst
                      obtain ⟨σ₂', hpop', hc₂⟩ := popTy_mono hσ hpop
                      refine ⟨[{ w' with σ := tout :: σ₂' }], by
                        simp only [step1, hpt, hp', hpop'], ?_⟩
                      intro u hu
                      simp only [List.mem_singleton] at hu
                      subst u
                      exact ⟨{ w with σ := tout :: σ₂, pending := none },
                        List.Mem.head _, hΓ, stackLe_cons_same hc₂,
                        by rw [hp']; exact pendLe_refl _⟩

theorem step1_mono {sigs : SigTable} {i : Instr} {w' w : World}
    (hle : worldLe w' w) {ws₂ : Worlds} (hst : step1 sigs i w = some ws₂) :
    ∃ ws₂', step1 sigs i w' = some ws₂' ∧ worldsLe ws₂' ws₂ := by
  obtain ⟨hΓ, hσ, hp⟩ := hle
  cases i with
  | kEval e | kIte t e | kAssert | kRet | kRepeatWhile c body
  | kRepeatTest c body | kForStart x body | kForBody x vs body
  | kTestVar x p =>
      simp only [step1] at hst
      cases hst
      exact ⟨[w'], by simp [step1], by
        intro u hu
        simp only [List.mem_singleton] at hu
        subst hu
        exact ⟨w, List.Mem.head _, hΓ, hσ, hp⟩⟩
  | kPrim1 p => exact step1_prim_mono ⟨hΓ, hσ, hp⟩ hst
  | kSet x =>
      simp only [step1] at hst
      cases hpn : w.pending with
      | some q => rw [hpn] at hst; cases hst
      | none =>
          have hp' : w'.pending = none := pendLe_none hp hpn
          rw [hpn] at hst
          cases hsl : w.σ with
          | nil => rw [hsl] at hst; cases hst
          | cons t σ₁ =>
              rw [hsl] at hst
              cases hst
              rw [hsl] at hσ
              cases hs : w'.σ with
              | nil => rw [hs] at hσ; exact absurd hσ.1 (by simp)
              | cons t' σ₁' =>
                  rw [hs] at hσ
                  obtain ⟨hrest, hhead⟩ := stackLe_cons hσ
                  refine ⟨[{ w' with Γ := (x, t') :: w'.Γ, σ := σ₁' }],
                    by simp only [step1, hp', hs], ?_⟩
                  intro u hu
                  simp only [List.mem_singleton] at hu
                  subst u
                  exact ⟨_, List.Mem.head _,
                    envLe_cons hhead hΓ, hrest, by rw [hp']; exact pendLe_refl _⟩
  | kPop =>
      simp only [step1] at hst
      cases hpn : w.pending with
      | some q => rw [hpn] at hst; cases hst
      | none =>
          have hp' : w'.pending = none := pendLe_none hp hpn
          rw [hpn] at hst
          cases hsl : w.σ with
          | nil => rw [hsl] at hst; cases hst
          | cons t σ₁ =>
              rw [hsl] at hst
              cases hst
              rw [hsl] at hσ
              cases hs : w'.σ with
              | nil => rw [hs] at hσ; exact absurd hσ.1 (by simp)
              | cons t' σ₁' =>
                  rw [hs] at hσ
                  obtain ⟨hrest, _⟩ := stackLe_cons hσ
                  refine ⟨[{ w' with σ := σ₁' }],
                    by simp only [step1, hp', hs], ?_⟩
                  intro u hu
                  simp only [List.mem_singleton] at hu
                  subst u
                  exact ⟨_, List.Mem.head _, hΓ, hrest, by rw [hp']; exact pendLe_refl _⟩
  | kTest =>
      simp only [step1] at hst
      cases hpn : w.pending with
      | none => rw [hpn] at hst; cases hst
      | some q =>
          cases q with
          | normal t =>
              rw [show w.pending = some (.normal t) from hpn] at hst
              cases hst
              cases hpn' : w'.pending with
              | none =>
                  rw [hpn'] at hp
                  rw [hpn] at hp
                  exact absurd hp (by simp [pendLe])
              | some q' =>
                  cases q' with
                  | normal t' =>
                      refine ⟨[{ w' with σ := [.isValue (.boolean Bool.false)] :: w'.σ }],
                        by simp only [step1, hpn'], ?_⟩
                      intro u hu
                      simp only [List.mem_singleton] at hu
                      subst u
                      exact ⟨_, List.Mem.head _, hΓ, stackLe_cons_same hσ,
                        by rw [hpn] at hp; exact hp⟩
                  | throw =>
                      rw [hpn'] at hp
                      rw [hpn] at hp
                      exact absurd hp (by simp [pendLe])
          | throw =>
              rw [show w.pending = some Pending.throw from hpn] at hst
              cases hst
              cases hpn' : w'.pending with
              | none =>
                  rw [hpn'] at hp
                  rw [hpn] at hp
                  exact absurd hp (by simp [pendLe])
              | some q' =>
                  cases q' with
                  | normal t' =>
                      rw [hpn'] at hp
                      rw [hpn] at hp
                      exact absurd hp (by simp [pendLe])
                  | throw =>
                      refine ⟨[{ w' with σ := [.isValue (.boolean Bool.true)] :: w'.σ }],
                        by simp only [step1, hpn'], ?_⟩
                      intro u hu
                      simp only [List.mem_singleton] at hu
                      subst u
                      exact ⟨_, List.Mem.head _, hΓ, stackLe_cons_same hσ,
                        by rw [hpn] at hp; exact hp⟩
  | kUnwrap =>
      simp only [step1] at hst
      cases hpn : w.pending with
      | none => rw [hpn] at hst; cases hst
      | some q =>
          cases q with
          | normal t =>
              rw [show w.pending = some (.normal t) from hpn] at hst
              cases hst
              cases hpn' : w'.pending with
              | none =>
                  rw [hpn'] at hp
                  rw [hpn] at hp
                  exact absurd hp (by simp [pendLe])
              | some q' =>
                  cases q' with
                  | normal t' =>
                      refine ⟨[{ w' with σ := t' :: w'.σ, pending := none }],
                        by simp only [step1, hpn'], ?_⟩
                      intro u hu
                      simp only [List.mem_singleton] at hu
                      subst u
                      have hpp : pendLe w'.pending w.pending := hp
                      rw [hpn'] at hpp
                      rw [hpn] at hpp
                      exact ⟨_, List.Mem.head _, hΓ, stackLe_cons_le hσ hpp, by trivial⟩
                  | throw =>
                      rw [hpn'] at hp
                      rw [hpn] at hp
                      exact absurd hp (by simp [pendLe])
          | throw =>
              rw [show w.pending = some Pending.throw from hpn] at hst
              cases hst
              cases hpn' : w'.pending with
              | none =>
                  rw [hpn'] at hp
                  rw [hpn] at hp
                  exact absurd hp (by simp [pendLe])
              | some q' =>
                  cases q' with
                  | normal t' =>
                      rw [hpn'] at hp
                      rw [hpn] at hp
                      exact absurd hp (by simp [pendLe])
                  | throw =>
                      refine ⟨[{ w' with σ := anyT :: w'.σ, pending := none }],
                        by simp only [step1, hpn'], ?_⟩
                      intro u hu
                      simp only [List.mem_singleton] at hu
                      subst u
                      exact ⟨_, List.Mem.head _, hΓ, stackLe_cons_same hσ, by trivial⟩
  | kMkList n =>
      simp only [step1] at hst
      cases hpn : w.pending with
      | some q => rw [hpn] at hst; cases hst
      | none =>
          have hp' : w'.pending = none := pendLe_none hp hpn
          rw [hpn] at hst
          cases hpop : popTyN n anyT w.σ with
          | none => rw [hpop] at hst; cases hst
          | some σ₂ =>
              rw [hpop] at hst
              cases hst
              obtain ⟨σ₂', hpop', hc₂⟩ := popTyN_mono n hσ hpop
              refine ⟨[{ w' with σ := [.anyValue .list] :: σ₂' }],
                by simp only [step1, hp', hpop'], ?_⟩
              intro u hu
              simp only [List.mem_singleton] at hu
              subst u
              exact ⟨_, List.Mem.head _, hΓ, stackLe_cons_same hc₂,
                by rw [hp']; exact pendLe_refl _⟩
  | kNewSlot sn =>
      simp only [step1] at hst
      cases hslot : slotOfName sn with
      | none => rw [hslot] at hst; cases hst
      | some ord =>
          rw [hslot] at hst
          try dsimp only at hst
          cases hpn : w.pending with
          | some q => rw [hpn] at hst; cases hst
          | none =>
              have hp' : w'.pending = none := pendLe_none hp hpn
              rw [hpn] at hst
              cases hpop : popTy anyT w.σ with
              | none => rw [hpop] at hst; cases hst
              | some σ₂ =>
                  rw [hpop] at hst
                  cases hst
                  obtain ⟨σ₂', hpop', hc₂⟩ := popTy_mono hσ hpop
                  refine ⟨[{ w' with σ := [.anyValue .obj] :: σ₂' }],
                    by simp [step1, hslot, hp', hpop'], ?_⟩
                  intro u hu
                  simp only [List.mem_singleton] at hu
                  subst u
                  exact ⟨_, List.Mem.head _, hΓ, stackLe_cons_same hc₂,
                    by rw [hp']; exact pendLe_refl _⟩
  | kCall f n =>
      simp only [step1] at hst
      cases hsig : sigFind sigs f with
      | none => rw [hsig] at hst; cases hst
      | some pr =>
          obtain ⟨ps, retj⟩ := pr
          rw [hsig] at hst
          cases hpn : w.pending with
          | some q => rw [hpn] at hst; cases hst
          | none =>
              have hp' : w'.pending = none := pendLe_none hp hpn
              rw [hpn] at hst
              dsimp only at hst
              cases hlen' : (ps.length == n) || (ps.length == n + 1) with
              | false => rw [hlen'] at hst; cases hst
              | true =>
                  rw [hlen'] at hst
                  dsimp only at hst
                  cases hpop : popArgs (if ps.length == n then ps else ps.take n) w.σ with
                  | false => rw [hpop] at hst; cases hst
                  | true =>
                      rw [hpop] at hst
                      cases hst
                      have hpop' := popArgs_mono hσ hpop
                      refine ⟨(sigCompls sigs f).map (fun c =>
                          { w' with σ := w'.σ.drop n, pending := some c }), ?_, ?_⟩
                      · simp only [step1, hsig, hp', hlen', hpop']
                      · intro u hu
                        simp only [List.mem_map] at hu
                        obtain ⟨c, hc, rfl⟩ := hu
                        exact ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩,
                          hΓ, stackLe_drop hσ n, pendLe_refl _⟩
  | kIMeth nm n =>
      simp only [step1] at hst
      cases har : mopArity nm == some n with
      | false => rw [har] at hst; cases hst
      | true =>
          rw [har] at hst
          cases hpn : w.pending with
          | some q => rw [hpn] at hst; cases hst
          | none =>
              have hp' : w'.pending = none := pendLe_none hp hpn
              rw [hpn] at hst
              dsimp only at hst
              cases hpop1 : popTyN n anyT w.σ with
              | none => rw [hpop1] at hst; cases hst
              | some σ₁ =>
                  rw [hpop1] at hst
                  dsimp only at hst
                  cases hpop2 : popA (.anyValue .obj) σ₁ with
                  | none => rw [hpop2] at hst; cases hst
                  | some σ₂ =>
                      rw [hpop2] at hst
                      cases hst
                      obtain ⟨σ₁', hpop1', hc₁⟩ := popTyN_mono n hσ hpop1
                      obtain ⟨σ₂', hpop2', hc₂⟩ := popA_mono hc₁ hpop2
                      refine ⟨(mopResult nm).map (fun c =>
                          { w' with σ := σ₂', pending := some c }), ?_, ?_⟩
                      · simp only [step1, har, hp', hpop1', hpop2']
                      · intro u hu
                        simp only [List.mem_map] at hu
                        obtain ⟨c, hc, rfl⟩ := hu
                        exact ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩,
                          hΓ, hc₂, pendLe_refl _⟩

/- ## Proof layer XIII: stepWorlds_mono (the mapM lift) -/

theorem worldsLe_append {ws₁' ws₁ ws₂' ws₂ : Worlds}
    (h₁ : worldsLe ws₁' ws₁) (h₂ : worldsLe ws₂' ws₂) :
    worldsLe (ws₁' ++ ws₂') (ws₁ ++ ws₂) := by
  intro u hu
  simp only [List.mem_append] at hu ⊢
  cases hu with
  | inl hu => obtain ⟨w, hw, hle⟩ := h₁ u hu; exact ⟨w, Or.inl hw, hle⟩
  | inr hu => obtain ⟨w, hw, hle⟩ := h₂ u hu; exact ⟨w, Or.inr hw, hle⟩

theorem pendLe_trans {p₁ p₂ p₃ : Option Pending}
    (h₁ : pendLe p₁ p₂) (h₂ : pendLe p₂ p₃) : pendLe p₁ p₃ := by
  cases p₁ with
  | none =>
      cases p₂ with
      | none => cases p₃ with
        | none => trivial
        | some q => exact absurd h₂ (by simp [pendLe])
      | some q => exact absurd h₁ (by simp [pendLe])
  | some q =>
      cases q with
      | normal t =>
          cases p₂ with
          | none => exact absurd h₁ (by simp [pendLe])
          | some q₂ =>
              cases q₂ with
              | normal t₂ =>
                  cases p₃ with
                  | none => exact absurd h₂ (by simp [pendLe])
                  | some q₃ =>
                      cases q₃ with
                      | normal t₃ => exact tyLe_trans h₁ h₂
                      | throw => exact absurd h₂ (by simp [pendLe])
              | throw => exact absurd h₁ (by simp [pendLe])
      | throw =>
          cases p₂ with
          | none => exact absurd h₁ (by simp [pendLe])
          | some q₂ =>
              cases q₂ with
              | normal t₂ => exact absurd h₁ (by simp [pendLe])
              | throw =>
                  cases p₃ with
                  | none => exact absurd h₂ (by simp [pendLe])
                  | some q₃ =>
                      cases q₃ with
                      | normal t₃ => exact absurd h₂ (by simp [pendLe])
                      | throw => trivial

theorem worldsLe_trans {ws₁ ws₂ ws₃ : Worlds}
    (h₁ : worldsLe ws₁ ws₂) (h₂ : worldsLe ws₂ ws₃) : worldsLe ws₁ ws₃ := by
  intro u hu
  obtain ⟨v, hv, hΓ₁, hσ₁, hp₁⟩ := h₁ u hu
  obtain ⟨x, hx, hΓ₂, hσ₂, hp₂⟩ := h₂ v hv
  refine ⟨x, hx, ?_, ?_, pendLe_trans hp₁ hp₂⟩
  · intro y t ht
    obtain ⟨u₁, hu₁, htu⟩ := hΓ₁ y t ht
    obtain ⟨u₂, hu₂, htu₂⟩ := hΓ₂ y u₁ hu₁
    exact ⟨u₂, hu₂, tyLe_trans htu htu₂⟩
  · have hlen : u.σ.length = x.σ.length := hσ₁.1.trans hσ₂.1
    refine ⟨hlen, ?_⟩
    intro j a ha b hb
    obtain ⟨m, hm⟩ : ∃ m, m ∈ v.σ[j]? := by
      have hu₁ : j < u.σ.length := mem_getElem?_lt ha
      have hlen1 : u.σ.length = v.σ.length := hσ₁.1
      cases hv : v.σ[j]? with
      | none =>
          have hvle : v.σ.length ≤ j :=
            List.getElem?_eq_none_iff.mp hv
          omega
      | some m => exact ⟨m, by simp [hv]⟩
    exact tyLe_trans (hσ₁.2 j a ha m hm) (hσ₂.2 j m hm b hb)


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
    {env : Env} {eval : List JSValue} {ret : «String»} {pend : Option PendV}
    (h : frameOk sigs none ⟨.kIte t e :: rest, env, .boolean b :: eval, ret, pend⟩) :
    frameOk sigs none ⟨(if b then t else e) ++ rest, env, eval, ret, pend⟩ := by
  obtain ⟨-, hchk⟩ := h
  rw [frameChecks] at hchk
  simp only [List.map_cons] at hchk
  cases hb : b with
  | true =>
      rw [hb] at hchk
      have hslot : [typeOfV (JSValue.boolean Bool.true)] = [VTy.isValue (JSValue.boolean Bool.true)] := rfl
      rw [hslot] at hchk
      have hid : checkSeq sigs (sigRetTy sigs ret)
          { Γ := envTyOf env, σ := [VTy.isValue (JSValue.boolean Bool.true)] :: eval.map (fun v => [typeOfV v]), pending := pendAbstr pend } (.kIte t e :: rest)
          = mergeTC vacOk (checkSeq sigs (sigRetTy sigs ret)
              { Γ := envTyOf env, σ := eval.map (fun v => [typeOfV v]), pending := pendAbstr pend } (t ++ rest)) :=
        checkSeq_kIte_true rfl
      rw [hid] at hchk
      cases hres : checkSeq sigs (sigRetTy sigs ret)
          { Γ := envTyOf env, σ := eval.map (fun v => [typeOfV v]), pending := pendAbstr pend } (t ++ rest) with
      | reject s w =>
          rw [hres] at hchk
          have hrej : mergeTC vacOk (TCResult.reject s w) = TCResult.reject s w := rfl
          rw [hrej] at hchk
          exact hchk.elim
      | flows fbr =>
          cases hm : mergeTC vacOk (checkSeq sigs (sigRetTy sigs ret)
              { Γ := envTyOf env, σ := eval.map (fun v => [typeOfV v]), pending := pendAbstr pend } (t ++ rest)) with
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
                  { Γ := envTyOf env, σ := eval.map (fun v => [typeOfV v]), pending := pendAbstr pend } (t ++ rest) with
                  | .flows fb => terminal fb = Bool.true | _ => False)
              rw [hres]
              exact htr
  | false =>
      rw [hb] at hchk
      have hslot : [typeOfV (JSValue.boolean Bool.false)] = [VTy.isValue (JSValue.boolean Bool.false)] := rfl
      rw [hslot] at hchk
      have hid : checkSeq sigs (sigRetTy sigs ret)
          { Γ := envTyOf env, σ := [VTy.isValue (JSValue.boolean Bool.false)] :: eval.map (fun v => [typeOfV v]), pending := pendAbstr pend } (.kIte t e :: rest)
          = mergeTC vacOk (checkSeq sigs (sigRetTy sigs ret)
              { Γ := envTyOf env, σ := eval.map (fun v => [typeOfV v]), pending := pendAbstr pend } (e ++ rest)) :=
        checkSeq_kIte_false rfl
      rw [hid] at hchk
      cases hres : checkSeq sigs (sigRetTy sigs ret)
          { Γ := envTyOf env, σ := eval.map (fun v => [typeOfV v]), pending := pendAbstr pend } (e ++ rest) with
      | reject s w =>
          rw [hres] at hchk
          have hrej : mergeTC vacOk (TCResult.reject s w) = TCResult.reject s w := rfl
          rw [hrej] at hchk
          exact hchk.elim
      | flows fbr =>
          cases hm : mergeTC vacOk (checkSeq sigs (sigRetTy sigs ret)
              { Γ := envTyOf env, σ := eval.map (fun v => [typeOfV v]), pending := pendAbstr pend } (e ++ rest)) with
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
    {env : Env} {eval : List JSValue} {ret : «String»} {pend : Option PendV} {v : JSValue}
    (hv : ∀ b, v ≠ JSValue.boolean b)
    (h : frameOk sigs none ⟨.kIte t e :: rest, env, v :: eval, ret, pend⟩) : False := by
  obtain ⟨-, hchk⟩ := h
  rw [frameChecks] at hchk
  simp only [List.map_cons] at hchk
  have hrej : checkSeq sigs (sigRetTy sigs ret)
      { Γ := envTyOf env, σ := [typeOfV v] :: eval.map (fun v => [typeOfV v]),
        pending := pendAbstr pend } (.kIte t e :: rest)
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
    | compl b pv => simp only [checkSeq, typeOfV, List.foldl, vacOk, mergeTC]
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
