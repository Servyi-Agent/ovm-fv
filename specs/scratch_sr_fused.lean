import Metalanguage.SubjectReduction

theorem frameTyped_kEval_fused {sigs : SigTable} {r : Ty} {e : Expr}
    {x : «String»} {p : Prim} {rest : List Instr} {env : Env}
    {eval : List JSValue} {ret : «String»}
    (hchk : checkSeq sigs r
      { Γ := envTyOf env, σ := eval.map (fun v => [typeOfV v]) }
      (.kEval e :: rest)
      = checkSeq sigs r
        { Γ := envTyOf env, σ := eval.map (fun v => [typeOfV v]) }
        (.kTestVar x p :: rest))
    (h : frameTyped sigs r ⟨.kEval e :: rest, env, eval, ret⟩) :
    frameTyped sigs r ⟨.kTestVar x p :: rest, env, eval, ret⟩ := by
  simp only [frameTyped, frameWorld] at h ⊢
  rw [hchk] at h
  exact h

theorem SR_kEval_isObject_nv (sigs : SigTable) (reg : AOReg)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kEval (.isObject (.nv x))) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact hpre
  | fell => exact hpre
  | frames fs heap nl =>
      cases fs with
      | nil => exact hpre
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          simp only [fstep] at ⊢
          refine ⟨⟨frameTyped_kEval_fused (x := x) (p := .pIsObj)
            (by simp [checkSeq]) hpre.1.1, hpre.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2

theorem SR_kEval_isNotObject_nv (sigs : SigTable) (reg : AOReg)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kEval (.isNotObject (.nv x))) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact hpre
  | fell => exact hpre
  | frames fs heap nl =>
      cases fs with
      | nil => exact hpre
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          simp only [fstep] at ⊢
          refine ⟨⟨frameTyped_kEval_fused (x := x) (p := .pIsNotObj)
            (by simp [checkSeq]) hpre.1.1, hpre.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2

theorem SR_kEval_isNotUndefined_nv (sigs : SigTable) (reg : AOReg)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kEval (.isNotUndefined (.nv x))) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact hpre
  | fell => exact hpre
  | frames fs heap nl =>
      cases fs with
      | nil => exact hpre
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          simp only [fstep] at ⊢
          refine ⟨⟨frameTyped_kEval_fused (x := x) (p := .pIsNotU)
            (by simp [checkSeq]) hpre.1.1, hpre.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2

theorem SR_kEval_isU_nv (sigs : SigTable) (reg : AOReg)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kEval (.isU (.nv x))) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact hpre
  | fell => exact hpre
  | frames fs heap nl =>
      cases fs with
      | nil => exact hpre
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          simp only [fstep] at ⊢
          refine ⟨⟨frameTyped_kEval_fused (x := x) (p := .pIsU)
            (by simp [checkSeq]) hpre.1.1, hpre.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2

theorem SR_kEval_hasCall_nv (sigs : SigTable) (reg : AOReg)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kEval (.hasCall (.nv x))) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact hpre
  | fell => exact hpre
  | frames fs heap nl =>
      cases fs with
      | nil => exact hpre
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          simp only [fstep] at ⊢
          refine ⟨⟨frameTyped_kEval_fused (x := x) (p := .pHasCall)
            (by simp [checkSeq]) hpre.1.1, hpre.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2

theorem SR_kEval_hasCtor_nv (sigs : SigTable) (reg : AOReg)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kEval (.hasCtor (.nv x))) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact hpre
  | fell => exact hpre
  | frames fs heap nl =>
      cases fs with
      | nil => exact hpre
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          simp only [fstep] at ⊢
          refine ⟨⟨frameTyped_kEval_fused (x := x) (p := .pHasCtor)
            (by simp [checkSeq]) hpre.1.1, hpre.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2

theorem SR_kEval_isBoolVal_nv (sigs : SigTable) (reg : AOReg)
    (b : Bool) (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kEval (.isBoolVal b (.nv x))) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact hpre
  | fell => exact hpre
  | frames fs heap nl =>
      cases fs with
      | nil => exact hpre
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          simp only [fstep] at ⊢
          refine ⟨⟨frameTyped_kEval_fused (x := x)
            (p := if b then .pIsTrue else .pIsFalse)
            (by cases b <;> simp [checkSeq]) hpre.1.1, hpre.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2

theorem SR_kEval_isStrVal_nv (sigs : SigTable) (reg : AOReg)
    (sv : «String») (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kEval (.isStrVal sv (.nv x))) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact hpre
  | fell => exact hpre
  | frames fs heap nl =>
      cases fs with
      | nil => exact hpre
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          simp only [fstep] at ⊢
          refine ⟨⟨frameTyped_kEval_fused (x := x) (p := .pIsStr sv)
            (by simp [checkSeq]) hpre.1.1, hpre.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2

theorem SR_kEval_hasField_nv (sigs : SigTable) (reg : AOReg)
    (nm : «String») (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kEval (.hasField nm (.nv x))) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact hpre
  | fell => exact hpre
  | frames fs heap nl =>
      cases fs with
      | nil => exact hpre
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          simp only [fstep] at ⊢
          refine ⟨⟨frameTyped_kEval_fused (x := x) (p := .pHasField nm)
            (by simp [checkSeq]) hpre.1.1, hpre.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2

theorem SR_kEval_isNullOrUnd_nv (sigs : SigTable) (reg : AOReg)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kEval (.isNullOrUnd (.nv x))) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact hpre
  | fell => exact hpre
  | frames fs heap nl =>
      cases fs with
      | nil => exact hpre
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          simp only [fstep] at ⊢
          refine ⟨⟨frameTyped_kEval_fused (x := x) (p := .pNullOrUnd)
            (by simp [checkSeq]) hpre.1.1, hpre.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2

theorem SR_kEval_isBoolVal_call_nv_fused (sigs : SigTable) (reg : AOReg)
    (b : Bool) (f : «String») (x : «String») (s : FM) (r : Ty)
    (hf : fusedPred f = Bool.true) :
    SR_arm sigs reg (.kEval (.isBoolVal b (.call f [.nv x]))) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact hpre
  | fell => exact hpre
  | frames fs heap nl =>
      cases fs with
      | nil => exact hpre
      | cons f' fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f'
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          have hcond : ((f == "IsDataDescriptor" || f == "IsAccessorDescriptor")
              || f == "IsCallable") = Bool.true := hf
          simp only [fstep, hcond] at ⊢
          refine ⟨⟨frameTyped_kEval_fused (x := x) (p := .pPred f b)
            (by simp [checkSeq, hf]) hpre.1.1, hpre.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2