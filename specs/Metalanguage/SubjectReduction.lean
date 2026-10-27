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

/- ## Keystone lemmas -/

/- Subtype transitivity (set inclusion; covariant under complN). -/
theorem tmoves_trans (t₂ : STy) :
    ∀ t₁ t₃, tmoves t₁ t₂ = Bool.true → tmoves t₂ t₃ = Bool.true →
      tmoves t₁ t₃ = Bool.true := by
  induction t₂ with
  | val b =>
      intro t₁ t₃ h₁ h₂
      cases t₁ with
      | val a =>
          cases t₃ with
          | val c =>
              have h₁' : a - (a &&& b) = 0 := by
                simp only [tmoves] at h₁; exact of_decide_eq_true h₁
              have h₂' : b - (b &&& c) = 0 := by
                simp only [tmoves] at h₂; exact of_decide_eq_true h₂
              have l1 : a &&& b ≤ a := Nat.and_le_left
              have l2 : b &&& c ≤ b := Nat.and_le_left
              have hab : a = a &&& b := by omega
              have hbc : b = b &&& c := by omega
              have h6 : a &&& c = a := by
                calc a &&& c = (a &&& b) &&& c := by
                      conv => lhs; arg 1; rw [hab]
                  _ = a &&& (b &&& c) := Nat.and_assoc a b c
                  _ = a &&& b := by rw [← hbc]
                  _ = a := hab.symm
              have key : a - (a &&& c) = 0 := by omega
              simp only [tmoves]
              exact decide_eq_true key
          | complT => simp only [tmoves] at h₂; exact Bool.noConfusion h₂
          | complN _ => simp only [tmoves] at h₂; exact Bool.noConfusion h₂
      | complT => simp only [tmoves] at h₁; exact Bool.noConfusion h₁
      | complN _ => simp only [tmoves] at h₁; exact Bool.noConfusion h₁
  | complN b ih =>
      intro t₁ t₃ h₁ h₂
      cases t₁ with
      | complN a =>
          cases t₃ with
          | complN c =>
              simp only [tmoves] at h₁ h₂ ⊢
              exact ih a c h₁ h₂
          | complT => simp only [tmoves] at h₂; exact Bool.noConfusion h₂
          | val => simp only [tmoves] at h₂; exact Bool.noConfusion h₂
      | complT => simp only [tmoves] at h₁; exact Bool.noConfusion h₁
      | val => simp only [tmoves] at h₁; exact Bool.noConfusion h₁
  | complT =>
      intro t₁ t₃ h₁ h₂
      cases t₁ with
      | complT =>
          cases t₃ with
          | complT => rfl
          | val => simp only [tmoves] at h₂; exact Bool.noConfusion h₂
          | complN _ => simp only [tmoves] at h₂; exact Bool.noConfusion h₂
      | val => simp only [tmoves] at h₁; exact Bool.noConfusion h₁
      | complN _ => simp only [tmoves] at h₁; exact Bool.noConfusion h₁

def stackSub : List STy → List STy → Bool
  | [], [] => Bool.true
  | t :: σ₁, t' :: σ₂ => tmoves t t' && stackSub σ₁ σ₂
  | _, _ => Bool.false

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
          have h₃ : tmoves t₁ t = Bool.true := tmoves_trans t₂ t₁ t hs.1 hh
          exact ⟨l₁, by simp [popTy, h₃], hs.2⟩
  | [], _ :: _ => simp [stackSub] at hsub
  | _ :: _, [] => simp [stackSub] at hsub
