import Metalanguage.SubjectReduction

theorem checkSeq_kPrim1_bool {sigs : SigTable} {r : Ty} {p : Prim}
    {Γ : TyEnv} {σ' : List Ty} {rest : List Instr} {v : JSValue}
    (hp : primTys p = some (anyT, [.anyValue .bool]))
    (htop : tmoves [typeOfV v] anyT = Bool.true) :
    checkSeq sigs r { Γ := Γ, σ := [typeOfV v] :: σ' } (.kPrim1 p :: rest)
      = checkSeq sigs r { Γ := Γ, σ := [.anyValue .bool] :: σ' } rest := by
  have htop' : tmoves [typeOfV v]
      [.anyValue .undef, .anyValue .null, .anyValue .bool, .anyValue .num,
        .anyValue .str, .anyValue .obj, .anyValue .list, .anyValue .desc] = Bool.true := by
    simpa [anyT, anyTags, langTags, anyOf] using htop
  cases p <;> simp [checkSeq, step1, primTys, popTy, htop', forkTC, List.foldl,
    mergeTC_noFlows, anyT, anyTags, langTags, anyOf] at hp ⊢

theorem tyLe_typeOfV_anyT_of_not_compl {v : JSValue}
    (hv : ¬ ∃ b w, v = JSValue.compl b w) :
    tyLe [typeOfV v] anyT := by
  apply tyLe_of_atom_cov
  intro a' ha'
  simp only [List.mem_singleton] at ha'
  subst a'
  cases v with
  | compl b w => exact False.elim (hv ⟨b, w, rfl⟩)
  | undefined =>
      exact ⟨.anyValue .undef, by simp [anyT, anyTags, langTags, anyOf], by simp [typeOfV, tmovesV, tagOf]⟩
  | null =>
      exact ⟨.anyValue .null, by simp [anyT, anyTags, langTags, anyOf], by simp [typeOfV, tmovesV, tagOf]⟩
  | boolean b =>
      exact ⟨.anyValue .bool, by simp [anyT, anyTags, langTags, anyOf], by simp [typeOfV, tmovesV, tagOf]⟩
  | number n =>
      exact ⟨.anyValue .num, by simp [anyT, anyTags, langTags, anyOf], by simp [typeOfV, tmovesV, tagOf]⟩
  | str s =>
      exact ⟨.anyValue .str, by simp [anyT, anyTags, langTags, anyOf], by simp [typeOfV, tmovesV, tagOf]⟩
  | obj a =>
      exact ⟨.anyValue .obj, by simp [anyT, anyTags, langTags, anyOf], by simp [typeOfV, tmovesV, tagOf]⟩
  | listV xs =>
      exact ⟨.anyValue .list, by simp [anyT, anyTags, langTags, anyOf], by simp [typeOfV, tmovesV, tagOf]⟩
  | descV d =>
      exact ⟨.anyValue .desc, by simp [anyT, anyTags, langTags, anyOf], by simp [typeOfV, tmovesV]⟩

theorem typeOfV_le_anyT_of_not_compl {v : JSValue}
    (hv : ¬ ∃ b w, v = JSValue.compl b w) :
    tmoves [typeOfV v] anyT = Bool.true :=
  tyLe_typeOfV_anyT_of_not_compl hv

theorem slotLe_bool_result (b : Bool) :
    slotLe [typeOfV (JSValue.boolean b)] [.anyValue .bool] := by
  constructor
  · apply tyLe_of_atom_cov
    intro a' ha'
    simp only [List.mem_singleton] at ha'
    subst a'
    refine ⟨.anyValue .bool, by simp, ?_⟩
    cases b <;> simp [typeOfV, tmovesV, tagOf]
  · simp

theorem frameTyped_prim_bool_bare {sigs : SigTable} {r : Ty} {p : Prim}
    {v : JSValue} {b : Bool} {rest : List Instr}
    {env : Env} {eval' : List JSValue} {ret : «String»}
    (hp : primTys p = some (anyT, [.anyValue .bool]))
    (hsc : sigParamsClosed sigs)
    (hv : ¬ ∃ c w, v = JSValue.compl c w)
    (h : frameTyped sigs r ⟨.kPrim1 p :: rest, env, v :: eval', ret⟩) :
    frameTyped sigs r ⟨rest, env, JSValue.boolean b :: eval', ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  rw [checkSeq_kPrim1_bool hp (typeOfV_le_anyT_of_not_compl hv)] at h
  exact frameTyped_pushRefine (ret := ret) hsc (slotLe_bool_result b) h

theorem frameTyped_prim_bool_reject_compl {sigs : SigTable} {r : Ty} {p : Prim}
    {rest : List Instr} {env : Env} {eval' : List JSValue} {ret : «String»}
    (hp : primTys p = some (anyT, [.anyValue .bool])) (b : Bool) (v : JSValue) :
    frameTyped sigs r ⟨.kPrim1 p :: rest, env, .compl b v :: eval', ret⟩ = False := by
  cases b <;> cases p <;>
    simp [frameTyped, frameWorld, checkSeq, step1, primTys, popTy, anyT, anyTags,
      langTags, anyOf, tmoves, tmovesV, typeOfV] at hp ⊢

theorem applyPrim_bool_of_primTys_bool (p : Prim)
    (hp : primTys p = some (anyT, [.anyValue .bool])) :
    ∀ (heap : Heap) (v : JSValue), ∃ b, applyPrim heap p v = JSValue.boolean b := by
  cases p <;> simp [primTys, applyPrim, anyT, anyTags, langTags, anyOf] at hp ⊢

theorem SR_kPrim1_bool (sigs : SigTable) (reg : AOReg) (p : Prim)
    (s : FM) (r : Ty)
    (hp : primTys p = some (anyT, [.anyValue .bool])) :
    SR_arm sigs reg (.kPrim1 p) s r := by
  intro _ _ hsc hpre
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
              exfalso
              have h1 : frameTyped sigs (sigRetTy sigs ret)
                  ⟨.kPrim1 p :: stmts, env, [], ret⟩ := hpre.1.1
              cases p <;> simp [primTys] at hp <;>
                simp [frameTyped, frameWorld, checkSeq, step1, primTys, popTy,
                  anyT, anyTags, langTags, anyOf] at h1
          | cons v eval' =>
              by_cases hv : ∃ c w, v = JSValue.compl c w
              · rcases hv with ⟨c, w, rfl⟩
                exfalso
                have h1 : frameTyped sigs (sigRetTy sigs ret)
                    ⟨.kPrim1 p :: stmts, env, .compl c w :: eval', ret⟩ := hpre.1.1
                rw [frameTyped_prim_bool_reject_compl (p := p) hp] at h1
                exact h1.elim
              · obtain ⟨b, hb⟩ := applyPrim_bool_of_primTys_bool p hp heap v
                refine ⟨⟨?_, hpre.1.2⟩, ?_⟩
                · rw [hb]
                  exact frameTyped_prim_bool_bare (p := p) hp (b := b) hsc hv hpre.1.1
                · rw [machineRet_head_swap]
                  exact hpre.2

theorem SR_kPrim1_pIsObj (sigs : SigTable) (reg : AOReg) (s : FM) (r : Ty) :
    SR_arm sigs reg (.kPrim1 .pIsObj) s r :=
  SR_kPrim1_bool sigs reg .pIsObj s r (by simp [primTys])