import Metalanguage.SubjectReduction

theorem frameTyped_kTestVar_plainBool {sigs : SigTable} {r : Ty}
    {p : Prim} {x : «String»} {b : Bool}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    {hsc : sigParamsClosed sigs}
    (hstep : checkSeq sigs r
      { Γ := envTyOf env, σ := eval.map (fun y => [typeOfV y]) }
      (.kTestVar x p :: rest)
      = checkSeq sigs r
        { Γ := envTyOf env,
          σ := [.anyValue .bool] :: eval.map (fun y => [typeOfV y]) }
        rest)
    (h : frameTyped sigs r ⟨.kTestVar x p :: rest, env, eval, ret⟩) :
    frameTyped sigs r ⟨rest, env, .boolean b :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  rw [hstep] at h
  exact frameTyped_pushRefine (ret := ret) hsc (slotLe_bool_result b) h

theorem SR_kTestVar_plainBool (sigs : SigTable) (reg : AOReg)
    (p : Prim) (x : «String») (s : FM) (r : Ty)
    (hsome : ∀ (rd : Ty) (v : JSValue) (env : Env) (eval : List JSValue)
        (rest : List Instr),
      tyLookup (envTyOf env) x = some [typeOfV v] →
      checkSeq sigs rd
        { Γ := envTyOf env, σ := eval.map (fun y => [typeOfV y]) }
        (.kTestVar x p :: rest)
      = checkSeq sigs rd
        { Γ := envTyOf env,
          σ := [.anyValue .bool] :: eval.map (fun y => [typeOfV y]) }
        rest)
    (hnone : ∀ (rd : Ty) (env : Env) (eval : List JSValue)
        (rest : List Instr),
      tyLookup (envTyOf env) x = none →
      checkSeq sigs rd
        { Γ := envTyOf env, σ := eval.map (fun y => [typeOfV y]) }
        (.kTestVar x p :: rest)
      = TCResult.reject (.kTestVar x p) "unbound variable")
    (hrun : ∀ (heap : Heap) (v : JSValue),
      ∃ b, applyPrim heap p v = JSValue.boolean b) :
    SR_arm sigs reg (.kTestVar x p) s r := by
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
                  ⟨.kTestVar x p :: stmts, env, eval, ret⟩ := hpre.1.1
              simp only [frameTyped, frameWorld] at h1
              rw [hnone (sigRetTy sigs ret) env eval stmts hΓ] at h1
              exact h1.elim
          | some v =>
              have hΓ : tyLookup (envTyOf env) x = some [typeOfV v] := by
                have hbridge := envTyOf_lookup env x
                simp only [hl, Option.map_some] at hbridge
                exact hbridge.symm
              obtain ⟨b, hb⟩ := hrun heap v
              simp only [fstep, hl] at ⊢
              rw [hb]
              refine ⟨⟨frameTyped_kTestVar_plainBool (hsc := hsc)
                  (hstep := hsome (sigRetTy sigs ret) v env eval stmts hΓ)
                  hpre.1.1, hpre.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2

theorem SR_kTestVar_pHasCall (sigs : SigTable) (reg : AOReg)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kTestVar x .pHasCall) s r :=
  SR_kTestVar_plainBool sigs reg .pHasCall x s r
    (fun _ _ _ _ _ hΓ => by simp [checkSeq, testTypeP, hΓ])
    (fun _ _ _ _ hΓ => by simp [checkSeq, testTypeP, hΓ])
    (fun heap v => ⟨hasCallV heap v, by simp [applyPrim]⟩)

theorem SR_kTestVar_pHasCtor (sigs : SigTable) (reg : AOReg)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kTestVar x .pHasCtor) s r :=
  SR_kTestVar_plainBool sigs reg .pHasCtor x s r
    (fun _ _ _ _ _ hΓ => by simp [checkSeq, testTypeP, hΓ])
    (fun _ _ _ _ hΓ => by simp [checkSeq, testTypeP, hΓ])
    (fun heap v => ⟨hasCtorV heap v, by simp [applyPrim]⟩)

theorem SR_kTestVar_pHasField (sigs : SigTable) (reg : AOReg)
    (nm : «String») (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kTestVar x (.pHasField nm)) s r :=
  SR_kTestVar_plainBool sigs reg (.pHasField nm) x s r
    (fun _ _ _ _ _ hΓ => by simp [checkSeq, testTypeP, hΓ])
    (fun _ _ _ _ hΓ => by simp [checkSeq, testTypeP, hΓ])
    (fun _ v => by cases v <;> simp [applyPrim])

theorem SR_kTestVar_pPred_unknown (sigs : SigTable) (reg : AOReg)
    (f : «String») (b : Bool) (x : «String») (s : FM) (r : Ty)
    (hf : predDecide f = none) :
    SR_arm sigs reg (.kTestVar x (.pPred f b)) s r :=
  SR_kTestVar_plainBool sigs reg (.pPred f b) x s r
    (fun _ _ _ _ _ hΓ => by simp [checkSeq, hf, hΓ])
    (fun _ _ _ _ hΓ => by simp [checkSeq, hf, hΓ])
    (fun _ v => by
      by_cases h1 : f = "IsDataDescriptor"
      · subst h1; simp [predDecide] at hf
      · by_cases h2 : f = "IsAccessorDescriptor"
        · subst h2; simp [predDecide] at hf
        · by_cases h3 : f = "IsCallable"
          · subst h3; simp [predDecide] at hf
          · simp [applyPrim, h1, h2, h3])