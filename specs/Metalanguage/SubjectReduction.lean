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
