import Metalanguage.SubjectReduction

theorem SR_kEval_fused_step (sigs : SigTable) (reg : AOReg)
    (e : Expr) (x : «String») (p : Prim) (s : FM) (r : Ty)
    (hstep : ∀ (stmts : List Instr) (env : Env) (eval : List JSValue)
        (ret : «String») (fs : List Fr) (heap : Heap) (nl : Nat),
      fstep reg (FM.frames
          (⟨.kEval e :: stmts, env, eval, ret⟩ :: fs) heap nl)
        = FM.frames (⟨.kTestVar x p :: stmts, env, eval, ret⟩ :: fs) heap nl)
    (hchk : ∀ (rd : Ty) (rest : List Instr) (Γ : TyEnv) (σ : List Ty),
      checkSeq sigs rd { Γ := Γ, σ := σ } (.kEval e :: rest)
        = checkSeq sigs rd { Γ := Γ, σ := σ } (.kTestVar x p :: rest)) :
    SR_arm sigs reg (.kEval e) s r := by
  intro _ _ _ hpre
  cases s with
  | fdone => exact hpre
  | fell => exact hpre
  | frames fs heap nl =>
      cases fs with
      | nil => exact hpre
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead] at hpre ⊢
          rw [hstep stmts env eval ret fs' heap nl]
          simp only [stateTyped, framesTypedFrom] at hpre ⊢
          refine ⟨⟨frameTyped_kEval_fused (hchk _ _ _ _) hpre.1.1,
            hpre.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2

theorem SR_kEval_isNull_nv (sigs : SigTable) (reg : AOReg)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kEval (.isNull (.nv x))) s r :=
  SR_kEval_fused_step sigs reg (.isNull (.nv x)) x .pIsNull s r
    (by intro _ _ _ _ _ _ _; rfl)
    (by intro _ _ _ _; simp [checkSeq])

theorem SR_kEval_isNormalC_nv (sigs : SigTable) (reg : AOReg)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kEval (.isNormalC (.nv x))) s r :=
  SR_kEval_fused_step sigs reg (.isNormalC (.nv x)) x .pIsNormalC s r
    (by intro _ _ _ _ _ _ _; rfl)
    (by intro _ _ _ _; simp [checkSeq])

theorem SR_kEval_isThrowC_nv (sigs : SigTable) (reg : AOReg)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kEval (.isThrowC (.nv x))) s r :=
  SR_kEval_fused_step sigs reg (.isThrowC (.nv x)) x .pIsThrowC s r
    (by intro _ _ _ _ _ _ _; rfl)
    (by intro _ _ _ _; simp [checkSeq])

theorem SR_kEval_isCompletion_nv (sigs : SigTable) (reg : AOReg)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kEval (.isCompletion (.nv x))) s r :=
  SR_kEval_fused_step sigs reg (.isCompletion (.nv x)) x .pIsCompletion s r
    (by intro _ _ _ _ _ _ _; rfl)
    (by intro _ _ _ _; simp [checkSeq])

theorem SR_kEval_isType_nv (sigs : SigTable) (reg : AOReg)
    (ty : «String») (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kEval (.isType ty (.nv x))) s r :=
  SR_kEval_fused_step sigs reg (.isType ty (.nv x)) x (.pIsType ty) s r
    (by intro _ _ _ _ _ _ _; rfl)
    (by intro _ _ _ _; simp [checkSeq])