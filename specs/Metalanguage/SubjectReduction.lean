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
   judgment anticipates exactly one delivery. -/

def selfTestHead : List Instr → Bool
  | .kTest :: .kIte [.kRet] [.kUnwrap] :: _ => Bool.true
  | _ => Bool.false

def inflight (calleeAbove : Bool) (f : Fr) : List STy :=
  if calleeAbove && selfTestHead f.stmts then [STy.compl] else []

def absStack (calleeAbove : Bool) (f : Fr) : List STy :=
  inflight calleeAbove f ++ stackTyOf f.eval

/- ## Frame and state typing -/

def frameOk (sigs : SigTable) (calleeAbove : Bool) (f : Fr) : Prop :=
  isOk (checkSeq sigs (envTyOf f.env) f.stmts (absStack calleeAbove f)) = Bool.true

def isComplV : JSValue → Bool
  | .compl _ _ => Bool.true
  | _ => Bool.false

/-- Non-top frames anticipate a delivery; the top frame does not. -/
def framesOk : SigTable → List Fr → Prop
  | _, [] => True
  | sigs, [f] => frameOk sigs Bool.false f
  | sigs, f :: fs@(_ :: _) =>
      frameOk sigs Bool.true f ∧ framesOk sigs fs

def stateOk (sigs : SigTable) (m : FM) : Prop :=
  match m with
  | .frames fs _ _ => framesOk sigs fs
  | .fdone v _ _ _ _ => isComplV v = Bool.true
  | .fell _ _ _ _ => True

/- ## Registry certification

   kCall pushes the callee's compiled body with a fresh env made from
   the ACTUAL argument values. Nothing about the caller can make that
   frame well-typed, so subject reduction is relative to a registry
   certified at every argument typing that satisfies the signature
   (pointwise: equal, or the parameter is `any`). -/

def sigParams (sigs : SigTable) (name : «String») : List STy :=
  match sigFind sigs name with
  | some (ps, _) => ps
  | none => []

def registryCertified (sigs : SigTable) (reg : AOReg) : Prop :=
  ∀ name ps prog, (name, (ps, prog)) ∈ reg →
    ∀ ts, leList ts (sigParams sigs name) →
      isOk (checkSeq sigs (zipTy ps ts) (compileSteps prog) []) = Bool.true

/- ## Unfolding equalities: one machine step of each value instruction
   is exactly one step of the checker. -/

theorem checkSeq_kEval_const (sigs : SigTable) (Γ : TyEnv)
    (v : JSValue) (rest : List Instr) (σ : List STy) :
    checkSeq sigs Γ (.kEval (.const v) :: rest) σ
      = checkSeq sigs Γ rest (typeOfV v :: σ) := by
  simp [checkSeq, typeOfE]

theorem checkSeq_kEval_nat (sigs : SigTable) (Γ : TyEnv)
    (n : Nat) (rest : List Instr) (σ : List STy) :
    checkSeq sigs Γ (.kEval (.nat n) :: rest) σ
      = checkSeq sigs Γ rest (STy.any :: σ) := by
  simp [checkSeq, typeOfE]

theorem checkSeq_kEval_nv {sigs : SigTable} {env : Env} {x : «String»}
    (h : lookup env x = some v) (rest : List Instr) (σ : List STy) :
    checkSeq sigs (envTyOf env) (.kEval (.nv x) :: rest) σ
      = checkSeq sigs (envTyOf env) rest (typeOfV v :: σ) := by
  simp only [checkSeq, typeOfE]
  rw [← envTyOf_lookup, h]
  rfl

/- ## Entry refinement — see checkSeq_mono below. -/

def stackSub : List STy → List STy → Bool
  | [], [] => Bool.true
  | t :: σ₁, t' :: σ₂ => tmoves t t' && stackSub σ₁ σ₂
  | _, _ => Bool.false

theorem tmoves_trans (t₁ t₂ t₃ : STy) (h₁ : tmoves t₁ t₂ = Bool.true)
    (h₂ : tmoves t₂ t₃ = Bool.true) : tmoves t₁ t₃ = Bool.true := by
  unfold tmoves at h₁ h₂ ⊢
  cases t₁ <;> cases t₂ <;> cases t₃ <;>
    simp_all only [decide_eq_true_eq] <;>
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> simp_all

theorem popTy_sub {t σ₁ σ₂'} (hsub : stackSub σ₁ σ₂ = Bool.true)
    (h : popTy t σ₂ = some σ₂') :
    ∃ σ₁', popTy t σ₁ = some σ₁' ∧ stackSub σ₁' σ₂' = Bool.true := by
  match σ₁, σ₂ with
  | [], [] => simp [popTy] at h
  | t₁ :: l₁, t₂ :: l₂ =>
      have hs : tmoves t₁ t₂ = Bool.true ∧ stackSub l₁ l₂ = Bool.true := by
        simpa [stackSub, Bool.and_eq_true] using hsub
      simp only [popTy] at h
      cases hh : tmoves t₂ t with
      | false => rw [hh] at h; simp at h
      | true =>
          rw [hh] at h
          cases h
          have h₃ : tmoves t₁ t = Bool.true := tmoves_trans t₁ t₂ t hs.1 hh
          refine ⟨l₁, ?_, hs.2⟩
          show (if tmoves t₁ t = Bool.true then some l₁ else none) = some l₁
          rw [h₃]; rfl
  | [], _ :: _ => simp [stackSub] at hsub
  | _ :: _, [] => simp [stackSub] at hsub
