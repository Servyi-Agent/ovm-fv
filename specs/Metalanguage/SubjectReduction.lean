import Metalanguage.Grammar
import Metalanguage.Semantics
import Metalanguage.Typecheck

/- # Subject reduction: fstep preserves typing.

   A frame TYPES AS P: `checkSeq` of its remaining instructions,
   started from the canonically-abstracted runtime stack (plus one
   anticipated in-flight completion when a callee sits directly
   above), falls through to an eval stack of shape P — or exits via
   kRet. Each machine step preserves the judgment: the same P is
   re-derived from the new state, never recomputed from scratch.

   Two facts make the agreement between static and runtime intrinsic:
   - the abstract stack/type-env are DERIVED from the runtime values
     (`stackTyOf`, `envTyOf`), and the canonical value types track
     exactly the machine-invariant distinctions (compl, boolean, obj,
     list, any) — so runtime pushes land EXACTLY on the static types;
   - branches and loop bodies are stack-neutral (enforced by the
     checker's join rule), so P is a function of the frame, not of
     the moment. -/

/- Runtime-value <-> static-type agreement is definitional: -/

def stackTyOf : List JSValue → List STy := fun eval => eval.map typeOfV

def envTyOf : Env → TyEnv := fun env => env.map (fun (n, v) => (n, typeOfV v))

/- The canonical abstractions commute with the frame's own operations:

   lookup into the runtime env agrees with tyLookup into its
   abstraction (both first-match, so shadowing behaves identically). -/
theorem envTyOf_lookup (env : Env) (x : «String») :
    (lookup env x).map typeOfV = tyLookup (envTyOf env) x := by
  induction env with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨n, v⟩ := hd
      by_cases h : n == x
      · simp [lookup, tyLookup, envTyOf, h]
      · simp [lookup, tyLookup, envTyOf, h, ih]

/- Pushing a value extends the abstract stack canonically. -/
theorem stackTyOf_cons (v : JSValue) (eval : List JSValue) :
    stackTyOf (v :: eval) = typeOfV v :: stackTyOf eval := rfl

/- Binding a value extends the abstract type-env canonically. -/
theorem envTyOf_cons (n : «String») (v : JSValue) (env : Env) :
    envTyOf ((n, v) :: env) = (n, typeOfV v) :: envTyOf env := rfl

/- ## The in-flight completion.

   After kCall / kIMeth-"Get" fire, the caller's instructions are
   `kTest :: kIte [kRet] [kUnwrap] :: rest` and the completion it will
   test does not exist yet: it is inside the callee frame above. The
   judgment anticipates exactly one delivery — TYPED by the callee's
   destiny: the frame above knows its AO name, hence its declared
   return type. -/

def selfTestHead : List Instr → Bool
  | .kTest :: .kIte [.kRet] [.kUnwrap] :: _ => Bool.true
  | _ => Bool.false

def inflight (sigs : SigTable) (above : Option «String») : List STy :=
  match above with
  | some n => [STy.complN (sigRetTy sigs n)]
  | none => []

def absStack (sigs : SigTable) (above : Option «String») (f : Fr) : List STy :=
  inflight sigs above ++ stackTyOf f.eval

/- ## Frame and state typing -/

def frameOk (sigs : SigTable) (above : Option «String») (f : Fr) : Prop :=
  -- a frame under a callee MUST be waiting at the self-test idiom:
  -- the delivery assumption of kRet
  (above.isNone ∨ selfTestHead f.stmts = Bool.true)
    ∧ (match checkSeq sigs (sigRetTy sigs f.ret)
                [{ Γ := envTyOf f.env, σ := absStack sigs above f }] f.stmts with
       | .flows fb => terminal fb = Bool.true  -- every world returns
       | _ => False)

def isComplV : JSValue → Bool
  | .compl _ _ => Bool.true
  | _ => Bool.false

/-- Each frame is checked at its own destiny (its AO's declared
   return type), anticipating a delivery TYPED by the frame directly
   above. -/
def framesOkFrom : SigTable → Option «String» → List Fr → Prop
  | _, _, [] => True
  | sigs, above, f :: fs =>
      frameOk sigs above f ∧ framesOkFrom sigs f.ret fs

def framesOk (sigs : SigTable) (fs : List Fr) : Prop :=
  framesOkFrom sigs none fs

def stateOk (sigs : SigTable) (m : FM) : Prop :=
  match m with
  | .frames fs _ _ => framesOk sigs fs
  | .fdone v _ _ _ _ => isComplV v = Bool.true
  | .fell _ _ _ _ => True

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

/-- Heap agreement: every object reference in any frame's eval stack
   or environment resolves in the heap. -/
def heapOk (heap : Heap) : List Fr → Prop
  | [] => True
  | f :: fs =>
      (∀ l ∈ (f.eval.flatMap locsOf ++ (f.env.map Prod.snd).flatMap locsOf),
        (heap l).isSome)
      ∧ heapOk heap fs

/- The machine's return type is the BOTTOM frame's destiny (stable:
   only that frame popping turns the state into fdone). -/
def machineRet (sigs : SigTable) (fs : List Fr) : STy :=
  match fs.getLast? with
  | some f => sigRetTy sigs f.ret
  | none => .val anyV

/- ## State typing, indexed by the machine's answer type r.

   fell is ILL-TYPED: with this definition, preservation alone
   already implies progress. -/
def stateOkR (sigs : SigTable) (r : STy) (m : FM) : Prop :=
  match m with
  | .frames fs heap _ =>
      fs.isEmpty = Bool.false
      ∧ framesOk sigs fs ∧ heapOk heap fs
      ∧ machineRet sigs fs = r
  | .fdone v _ _ _ _ =>
      -- the final value: normal compl-wrapped payload ⊑ r, or a throw
      match typeOfV v with
      | .complN p => tmoves p r = Bool.true
      | .complT => True
      | _ => False
  | .fell _ _ _ _ => False

/- Registry coverage (existence): every name the checker may call is
   answered by the registry or natively; the MOP-Get dispatch target
   exists. -/
def closedRegistry (sigs : SigTable) (reg : AOReg) : Prop :=
  (∀ n _ps _ret, sigFind sigs n = some (_ps, _ret) →
      (findAO reg n).isSome = Bool.true ∨ nativeOps.contains n = Bool.true)
  ∧ (findAO reg "OrdinaryGet").isSome = Bool.true

/- ## The target statement (proof in progress, bottom-up):

   theorem type_safety (sigs : SigTable) (reg : AOReg)
       (hreg : registryCertified sigs reg)
       (hcover : closedRegistry sigs reg)
       (m : FM) (h : stateOkR sigs r m) :
       stateOkR sigs r (fstep reg m)

   Preservation alone suffices: fell is ill-typed in stateOkR. -/

/- ## Registry certification

   kCall pushes the callee's compiled body with a fresh env made from
   the ACTUAL argument values. Nothing about the caller can make that
   frame well-typed, so subject reduction is relative to a registry
   certified at every argument typing that satisfies the signature
   (pointwise: equal, or the parameter is `any`). -/

def registryCertified (sigs : SigTable) (reg : AOReg) : Prop :=
  ∀ name ps prog, (name, (ps, prog)) ∈ reg →
    ∀ ts, leList ts (sigParams sigs name) →
      (match checkSeq sigs (sigRetTy sigs name)
              [{ Γ := zipTy ps ts, σ := [] }] (compileSteps prog) with
       | .flows fb => terminal fb = Bool.true
       | _ => False)


/- The subtype-transitivity and stack-subtyping lemmas are re-queued
   for the monotonicity push: STy is now a nested inductive (union /
   oneOf), so the induction needs a custom well-founded recursion;
   they land together with the refinement-monotonicity lemma. -/
