import Metalanguage.SubjectReduction

theorem frameTyped_pThrowC {sigs : SigTable} {r : Ty} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameTyped sigs r ⟨.kPrim1 .pThrowC :: rest, env, v :: eval, ret⟩) :
    frameTyped sigs r ⟨rest, env, .compl Bool.true v :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  rw [checkSeq_pThrowC rfl] at h
  exact h

theorem frameTyped_pThrowC_reject_nil {sigs : SigTable} {r : Ty}
    {rest : List Instr} {env : Env} {ret : «String»} :
    frameTyped sigs r ⟨.kPrim1 .pThrowC :: rest, env, [], ret⟩ = False := by
  simp [frameTyped, frameWorld, checkSeq, step1]

theorem SR_kPrim1_pThrowC (sigs : SigTable) (reg : AOReg) (s : FM) (r : Ty) :
    SR_arm sigs reg (.kPrim1 .pThrowC) s r := by
  intro _ _ hpre
  cases s with
  | fdone v fs heap nl n => exact hpre
  | fell fs heap nl n => exact hpre
  | frames fs heap nl =>
      cases fs with
      | nil => exact hpre
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases eval with
          | nil =>
              have h1 : frameTyped sigs (sigRetTy sigs ret)
                  ⟨.kPrim1 .pThrowC :: stmts, env, [], ret⟩ := hpre.1.1
              rw [frameTyped_pThrowC_reject_nil] at h1
              exact h1.elim
          | cons v eval' =>
              refine ⟨⟨frameTyped_pThrowC hpre.1.1, hpre.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2

theorem frameTyped_pWrapC_bare {sigs : SigTable} {r : Ty} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    (hbar : isBareVTy (typeOfV v) = Bool.true)
    (h : frameTyped sigs r ⟨.kPrim1 .pWrapC :: rest, env, v :: eval, ret⟩) :
    frameTyped sigs r ⟨rest, env, .compl Bool.false v :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  rw [checkSeq_pWrapC rfl hbar] at h
  exact h

theorem frameTyped_pWrapC_compl {sigs : SigTable} {r : Ty} {b : Bool} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameTyped sigs r ⟨.kPrim1 .pWrapC :: rest, env, .compl b v :: eval, ret⟩) :
    frameTyped sigs r ⟨rest, env, .compl b v :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  cases b <;> simp [checkSeq, step1, complOnly, typeOfV, forkTC, mergeTC_noFlows] at h ⊢ <;> exact h

theorem frameTyped_pWrapC_reject_nil {sigs : SigTable} {r : Ty}
    {rest : List Instr} {env : Env} {ret : «String»} :
    frameTyped sigs r ⟨.kPrim1 .pWrapC :: rest, env, [], ret⟩ = False := by
  simp [frameTyped, frameWorld, checkSeq, step1]

theorem SR_kPrim1_pWrapC (sigs : SigTable) (reg : AOReg) (s : FM) (r : Ty) :
    SR_arm sigs reg (.kPrim1 .pWrapC) s r := by
  intro _ _ hpre
  cases s with
  | fdone v fs heap nl n => exact hpre
  | fell fs heap nl n => exact hpre
  | frames fs heap nl =>
      cases fs with
      | nil => exact hpre
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases eval with
          | nil =>
              have h1 : frameTyped sigs (sigRetTy sigs ret)
                  ⟨.kPrim1 .pWrapC :: stmts, env, [], ret⟩ := hpre.1.1
              rw [frameTyped_pWrapC_reject_nil] at h1
              exact h1.elim
          | cons v eval' =>
              cases v with
              | compl b w =>
                  refine ⟨⟨frameTyped_pWrapC_compl (r := sigRetTy sigs ret) hpre.1.1, hpre.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2
              | undefined =>
                  refine ⟨⟨frameTyped_pWrapC_bare (v := JSValue.undefined) (by simp [isBareVTy, typeOfV]) hpre.1.1, hpre.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2
              | null =>
                  refine ⟨⟨frameTyped_pWrapC_bare (v := JSValue.null) (by simp [isBareVTy, typeOfV]) hpre.1.1, hpre.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2
              | boolean b =>
                  refine ⟨⟨frameTyped_pWrapC_bare (v := JSValue.boolean b) (by simp [isBareVTy, typeOfV]) hpre.1.1, hpre.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2
              | number n =>
                  refine ⟨⟨frameTyped_pWrapC_bare (v := JSValue.number n) (by simp [isBareVTy, typeOfV]) hpre.1.1, hpre.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2
              | str s =>
                  refine ⟨⟨frameTyped_pWrapC_bare (v := JSValue.str s) (by simp [isBareVTy, typeOfV]) hpre.1.1, hpre.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2
              | obj a =>
                  refine ⟨⟨frameTyped_pWrapC_bare (v := JSValue.obj a) (by simp [isBareVTy, typeOfV]) hpre.1.1, hpre.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2
              | listV xs =>
                  refine ⟨⟨frameTyped_pWrapC_bare (v := JSValue.listV xs) (by simp [isBareVTy, typeOfV]) hpre.1.1, hpre.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2
              | descV d =>
                  refine ⟨⟨frameTyped_pWrapC_bare (v := JSValue.descV d) (by simp [isBareVTy, typeOfV]) hpre.1.1, hpre.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2