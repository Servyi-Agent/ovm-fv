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

def isCompl : JSValue → Bool
  | .compl _ _ => Bool.true
  | _ => Bool.false

def envTyOf : Env → TyEnv := fun env =>
  env.map (fun (n, v) => (n, [typeOfV v]))

/-- Split the runtime eval stack into (σ, pending): values become
    singleton slots; the single completion (if any) parks. none =
    more than one completion (not certifiable). -/
def splitStack : List JSValue → Option (List Ty × Option Pending)
  | [] => some ([], none)
  | v :: rest =>
      match splitStack rest with
      | none => none
      | some (σ, p) =>
          match v with
          | .compl Bool.false pv =>
              if p.isSome then none
              else some (σ, some (.normal [typeOfV pv]))
          | .compl Bool.true _ =>
              if p.isSome then none
              else some (σ, some .throw)
          | _ => some ([typeOfV v] :: σ, p)

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
    will test does not exist yet: it is inside the callee frame
    above. The judgment anticipates BOTH deliveries — a normal
    payload TYPED by the callee's destiny (the frame above knows its
    AO name, hence its declared return type), and a throw. Each
    delivery must check; the throw side exits at the self-test's
    kRet (exempt), the normal side continues through kUnwrap. -/

def selfTestHead : List Instr → Bool
  | .kTest :: .kIte [.kRet] [.kUnwrap] :: _ => Bool.true
  | _ => Bool.false

/- ## Frame and state typing -/

/-- The frame's check from a given abstract stack + parked
    (or anticipated) completion. -/
def frameChecks (sigs : SigTable) (f : Fr) (p : Option Pending) : Prop :=
  match splitStack f.eval with
  | none => True   -- guarded by the outer conjunct
  | some (σ, _) =>
      match checkSeq sigs (sigRetTy sigs f.ret)
        [{ Γ := envTyOf f.env, σ := σ, pending := p }] (normL f.stmts) with
      | .flows fb => terminal fb = Bool.true  -- every world returns
      | _ => False

def frameOk (sigs : SigTable) (above : Option «String») (f : Fr) : Prop :=
  -- a frame under a callee MUST be waiting at the self-test idiom:
  -- the delivery assumption of kRet
  (above.isNone ∨ selfTestHead f.stmts = Bool.true)
    ∧ (f.env.all (fun (_n, v) => !isCompl v))
    ∧ (match splitStack f.eval with
       | none => False
       | some (σ, p) =>
           -- anticipate exactly the callee's declared alternatives
           match above with
           | some n => ∀ c ∈ sigCompls sigs n, frameChecks sigs f (some c)
           | none => frameChecks sigs f p)

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
      -- the final value: normal compl-wrapped payload ⊑ r, or a throw
      match v with
      | .compl Bool.false pv => tmoves [typeOfV pv] r = Bool.true
      | .compl Bool.true _ => True
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
      [{ Γ := zipTy ps ts, σ := [], pending := none }] (normL (compileSteps prog)) with
  | .flows fb =>
      terminal fb = Bool.true
        ∧ (fb.throws = Bool.true → complCanThrow (sigCompls sigs name) = Bool.true)
  | _ => False

theorem certifies_flows_elim {sigs : SigTable} {name : «String»}
    {ps : List «String»} {ts : List Ty} {prog : Prog}
    (h : certifies sigs name ps ts prog) :
    ∃ fb, checkSeq sigs (sigRetTy sigs name)
        [{ Γ := zipTy ps ts, σ := [], pending := none }] (normL (compileSteps prog))
        = TCResult.flows fb ∧ terminal fb = Bool.true
        ∧ (fb.throws = Bool.true
            → complCanThrow (sigCompls sigs name) = Bool.true) := by
  cases hb : checkSeq sigs (sigRetTy sigs name)
      [{ Γ := zipTy ps ts, σ := [], pending := none }] (normL (compileSteps prog)) with
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

/-- Pointwise refinement of type environments (first-match lookup). -/
def envLe (Γ Δ : TyEnv) : Prop :=
  ∀ x, ∀ t ∈ tyLookup Γ x, ∀ u ∈ tyLookup Δ x, tyLe t u

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

theorem splitStack_cons_val (v : JSValue) (σ : List Ty) (p : Option Pending)
    (eval : List JSValue) (hv : isCompl v = Bool.false)
    (h : splitStack eval = some (σ, p)) :
    splitStack (v :: eval) = some ([typeOfV v] :: σ, p) := by
  simp only [splitStack, h]
  cases v with
  | compl b pv => simp [isCompl] at hv
  | undefined => rfl
  | null => rfl
  | boolean b => rfl
  | number n => rfl
  | str s => rfl
  | obj l => rfl
  | listV vs => rfl
  | descV d => rfl

theorem splitStack_cons_compl_normal (pv : JSValue) (σ : List Ty) (p : Option Pending)
    (eval : List JSValue) (hp : p = none)
    (h : splitStack eval = some (σ, p)) :
    splitStack (.compl Bool.false pv :: eval)
      = some (σ, some (.normal [typeOfV pv])) := by
  simp only [splitStack, h, hp]
  simp

theorem splitStack_cons_compl_throw (pv : JSValue) (σ : List Ty) (p : Option Pending)
    (eval : List JSValue) (hp : p = none)
    (h : splitStack eval = some (σ, p)) :
    splitStack (.compl Bool.true pv :: eval) = some (σ, some Pending.throw) := by
  simp only [splitStack, h, hp]
  simp

theorem splitStack_cons_nil : splitStack [] = some ([], none) := rfl

/-- kTest's peek: verdict above the parked completion. -/
theorem splitStack_kTest (abrupt : Bool) (pv : JSValue) (σ : List Ty)
    (p : Option Pending) (eval : List JSValue)
    (h : splitStack (.compl abrupt pv :: eval) = some (σ, p)) :
    splitStack (.boolean abrupt :: .compl abrupt pv :: eval)
      = some ([.isValue (.boolean abrupt)] :: σ, p) := by
  rw [splitStack_cons_val (.boolean abrupt) σ p (.compl abrupt pv :: eval)
        (by simp [isCompl]) h]
  rfl

/-- kUnwrap: the payload takes the completion's place. -/


/- ## Proof layer III: absorbing masters -/

theorem type_safety_fdone {sigs : SigTable} {reg : AOReg} {r : Ty} {v : JSValue}
    {fs heap nl n} (h : stateOk sigs r (.fdone v fs heap nl n)) :
    stateOk sigs r (fstep reg (.fdone v fs heap nl n)) := h

theorem type_safety_fell {sigs : SigTable} {reg : AOReg} {r : Ty} {fs heap nl n}
    (h : stateOk sigs r (.fell fs heap nl n)) :
    stateOk sigs r (fstep reg (.fell fs heap nl n)) := h.elim

theorem type_safety_frames_nil {sigs : SigTable} {reg : AOReg} {r : Ty} {heap nl}
    (h : stateOk sigs r (.frames [] heap nl)) :
    stateOk sigs r (fstep reg (.frames [] heap nl)) := by
  unfold stateOk at h
  simp only at h
  exact absurd h.1 (by simp)

theorem type_safety_frames_nil_stmts {sigs : SigTable} {reg : AOReg} {r : Ty}
    {f : Fr} {fs : List Fr} {heap nl}
    (h : stateOk sigs r (.frames (f :: fs) heap nl))
    (hnil : f.stmts = []) :
    stateOk sigs r (fstep reg (.frames (f :: fs) heap nl)) := by
  unfold stateOk at h
  simp only at h
  have hfr := h.2.1
  unfold framesOk framesOkFrom at hfr
  obtain ⟨hf, -⟩ := hfr
  obtain ⟨-, -, hchk⟩ := hf
  simp only [frameChecks] at hchk
  rw [hnil] at hchk
  cases hse : splitStack f.eval with
  | none => rw [hse] at hchk; exact hchk.elim
  | some sp =>
      rw [hse] at hchk
      simp only [frameChecks, normL, checkSeq, terminal] at hchk
      exact absurd hchk (by simp)

/- ## Proof layer IV: checkSeq step identities (exact matches)

    Each machine push lands EXACTLY on the static push: consuming
    the instruction statically IS stepping the abstract world. -/

theorem normL_cons (i : Instr) (rest : List Instr) :
    normL (i :: rest) = normI i ++ normL rest := by rw [normL]

theorem mapM_singleton {α β : Type} {f : α → Option β} (a : α) :
    List.mapM f [a] = (f a).map (fun b => [b]) := by
  simp only [List.mapM, List.mapM.loop]
  cases f a <;> rfl

/-- markThrow is the identity when the expression cannot throw. -/
theorem markThrow_nothrow {sigs : SigTable} {ex : Expr}
    (hex : exprCanThrow sigs ex = Bool.false)
    (res : TCResult) : markThrow sigs ex res = res := by
  cases res with
  | flows fb => simp [markThrow, hex]
  | reject s w => rfl

/-- kEval of a non-completion const: push its canonical singleton. -/
theorem checkSeq_kEval_const {sigs : SigTable} {r : Ty} {W : World} {v : JSValue}
    {rest : List Instr} (hv : isCompl v = Bool.false) :
    checkSeq sigs r [W] (normL (.kEval (.const v) :: rest))
      = checkSeq sigs r [{ W with σ := [typeOfV v] :: W.σ }] (normL rest) := by
  cases v with
  | compl b pv => simp [isCompl] at hv
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _ | descV _ =>
      rw [normL_cons]
      simp only [normI, checkSeq, typeOfE, typeOfV, mapM_singleton,
                 List.cons_append, List.nil_append, Option.map]
      rw [markThrow_nothrow (by simp [exprCanThrow])]

/-- kEval of a nat literal: push the singleton number. -/
theorem checkSeq_kEval_nat {sigs : SigTable} {r : Ty} {W : World} {n : Nat}
    {rest : List Instr} :
    checkSeq sigs r [W] (normL (.kEval (.nat n) :: rest))
      = checkSeq sigs r
          [{ W with σ := [VTy.isValue (.number (↑n : Int))] :: W.σ }]
          (normL rest) := by
  rw [normL_cons]
  simp only [normI, checkSeq, typeOfE, mapM_singleton, Option.map,
             List.cons_append, List.nil_append]
  rw [markThrow_nothrow (by simp [exprCanThrow])]

/-- kEval of a bound variable: push the looked-up (canonical) type. -/
theorem checkSeq_kEval_nv {sigs : SigTable} {r : Ty} {W : World} {x : «String»}
    {v : JSValue} {rest : List Instr}
    (hΓ : tyLookup W.Γ x = some [typeOfV v]) :
    checkSeq sigs r [W] (normL (.kEval (.nv x) :: rest))
      = checkSeq sigs r [{ W with σ := [typeOfV v] :: W.σ }] (normL rest) := by
  rw [normL_cons]
  simp only [normI, checkSeq, typeOfE, hΓ, mapM_singleton, Option.map,
             List.cons_append, List.nil_append]
  rw [markThrow_nothrow (by simp [exprCanThrow])]

/-- kPop: drop the top slot (the machine fells on an empty stack -
    those states are ill-typed and never reach this lemma). -/
theorem checkSeq_kPop {sigs : SigTable} {r : Ty} {W : World} {ts : Ty} {σ' : List Ty}
    {rest : List Instr} (hσ : W.σ = ts :: σ') :
    checkSeq sigs r [W] (normL (.kPop :: rest))
      = checkSeq sigs r [{ W with σ := σ' }] (normL rest) := by
  rw [normL_cons]
  simp [normI, checkSeq, stepWorlds, hσ, mapM_singleton, Option.map,
        List.cons_append, List.nil_append]

/-- kSet: bind the top slot into Γ. -/
theorem checkSeq_kSet {sigs : SigTable} {r : Ty} {W : World} {x : «String»}
    {ts : Ty} {σ' : List Ty} {rest : List Instr} (hσ : W.σ = ts :: σ') :
    checkSeq sigs r [W] (normL (.kSet x :: rest))
      = checkSeq sigs r [{ Γ := (x, ts) :: W.Γ, σ := σ', pending := W.pending }]
          (normL rest) := by
  rw [normL_cons]
  simp [normI, checkSeq, stepWorlds, hσ, mapM_singleton, Option.map,
        List.cons_append, List.nil_append]
