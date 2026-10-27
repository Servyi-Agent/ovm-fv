import Metalanguage.Grammar
import Metalanguage.Semantics
import Metalanguage.Typecheck

/- # Subject reduction: fstep preserves typing.

   Canonical abstractions make agreement intrinsic: a frame's abstract
   stack/type environment are derived FROM its runtime values, so the
   theorem is purely about checkSeq accepting the instruction stream
   after each machine transition. -/

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
