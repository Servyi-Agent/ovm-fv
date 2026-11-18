import Metalanguage.SubjectReduction

theorem applyPrim_pPred_callable (heap : Heap) (b : Bool) (v : JSValue) :
    applyPrim heap (.pPred "IsCallable" b) v
      = .boolean (b == hasCallV heap v) := by
  cases v with
  | obj loc =>
      cases hobj : heap loc with
      | none => simp [applyPrim, hasCallV, hobj]
      | some o =>
          cases o.kind <;> simp [applyPrim, hasCallV, hobj]
  | undefined | null | boolean _ | number _ | str _ | listV _ | descV _
    | compl _ _ =>
      simp [applyPrim, hasCallV]

theorem splitP1_pPred_callable_machine (heap : Heap) (b : Bool)
    {Γ : TyEnv} {x : «String»} {v : JSValue} {σ : List Ty}
    (hΓ : tyLookup Γ x = some [typeOfV v]) :
    { Γ := (x, [typeOfV v]) :: Γ,
      σ := [.isValue (.boolean (b == hasCallV heap v))] :: σ }
      ∈ splitP1 x (fun a => (isCallableAtom a).map (fun bv => bv == b))
        { Γ := Γ, σ := σ } := by
  cases v with
  | obj loc =>
      have hv : typeOfV (JSValue.obj loc) = .isValue (JSValue.obj loc) := rfl
      cases hb : b == hasCallV heap (JSValue.obj loc) <;>
        simp [splitP1, splitP1At, hΓ, typeOfV, isCallableAtom, hb]
  | compl abrupt w =>
      cases abrupt <;> cases b <;>
        simp [splitP1, splitP1At, hΓ, typeOfV, isCallableAtom, hasCallV]
  | undefined | null | boolean _ | number _ | str _ | listV _ | descV _ =>
      cases b <;>
        simp [splitP1, splitP1At, hΓ, typeOfV, isCallableAtom, hasCallV]

theorem frameTyped_kTestVar_pPred_callable_present {sigs : SigTable}
    {r : Ty} {heap : Heap} {b : Bool} {x : «String»} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    {hsc : sigParamsClosed sigs}
    (hΓ : tyLookup (envTyOf env) x = some [typeOfV v])
    (h : frameTyped sigs r ⟨.kTestVar x (.pPred "IsCallable" b) :: rest,
        env, eval, ret⟩) :
    frameTyped sigs r ⟨rest, env, .boolean (b == hasCallV heap v) :: eval,
        ret⟩ :=
  frameTyped_kTestVar_pPred_present (hsc := hsc)
    (f := "IsCallable") (b := b) (dec := isCallableAtom)
    (g := fun y => b == hasCallV heap y) (x := x) (v := v)
    (rest := rest) (env := env) (eval := eval) (ret := ret) rfl
    (fun Γ σ hlookup => splitP1_pPred_callable_machine heap b hlookup) hΓ h

theorem frameTyped_kTestVar_pPred_callable_reject_unbound {sigs : SigTable}
    {r : Ty} {b : Bool} {x : «String»} {rest : List Instr} {env : Env}
    {eval : List JSValue} {ret : «String»}
    (hΓ : tyLookup (envTyOf env) x = none) :
    frameTyped sigs r ⟨.kTestVar x (.pPred "IsCallable" b) :: rest,
        env, eval, ret⟩ = False := by
  simp [frameTyped, frameWorld, checkSeq, predDecide, splitP1, hΓ, forkTC]

theorem SR_kTestVar_pPred_callable (sigs : SigTable) (reg : AOReg)
    (b : Bool) (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kTestVar x (.pPred "IsCallable" b)) s r := by
  intro _ _ hsc hpre
  cases s with
  | fdone => exact hpre
  | fell => exact hpre
  | frames fs heap nl =>
      cases fs with
      | nil => exact hpre
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases hl : lookup env x with
          | none =>
              have hΓ : tyLookup (envTyOf env) x = none := by
                have hbridge := envTyOf_lookup env x
                simp only [hl, Option.map_none] at hbridge
                exact hbridge.symm
              exfalso
              have h1 : frameTyped sigs (sigRetTy sigs ret)
                  ⟨.kTestVar x (.pPred "IsCallable" b) :: stmts, env, eval,
                      ret⟩ := hpre.1.1
              rw [frameTyped_kTestVar_pPred_callable_reject_unbound hΓ] at h1
              exact h1.elim
          | some v =>
              have hΓ : tyLookup (envTyOf env) x = some [typeOfV v] := by
                have hbridge := envTyOf_lookup env x
                simp only [hl, Option.map_some] at hbridge
                exact hbridge.symm
              simp only [fstep, hl] at ⊢
              rw [applyPrim_pPred_callable heap b v]
              refine ⟨⟨frameTyped_kTestVar_pPred_callable_present
                  (hsc := hsc) hΓ hpre.1.1, hpre.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2