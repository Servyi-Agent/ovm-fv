import Metalanguage.SubjectReduction

theorem frameTyped_kEval_nat {sigs : SigTable} {r : Ty} {n : Nat} {rest : List Instr}
    {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameTyped sigs r ⟨.kEval (.nat n) :: rest, env, eval, ret⟩) :
    frameTyped sigs r ⟨rest, env, .number (↑n : Int) :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  rw [checkSeq_kEval_nat] at h
  exact h

theorem SR_kEval_nat (sigs : SigTable) (reg : AOReg) (n : Nat) (s : FM) (r : Ty) :
    SR_arm sigs reg (.kEval (.nat n)) s r := by
  intro _ _ hpre
  cases s with
  | fdone v fs heap nl n' => exact hpre
  | fell fs heap nl n' => exact hpre
  | frames fs heap nl =>
      cases fs with
      | nil => exact hpre
      | cons f fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          refine ⟨⟨frameTyped_kEval_nat hpre.1.1, hpre.1.2⟩, ?_⟩
          rw [machineRet_head_swap]
          exact hpre.2

theorem frameTyped_kEval_nv {sigs : SigTable} {r : Ty} {x : «String»} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    (hΓ : tyLookup (envTyOf env) x = some [typeOfV v])
    (h : frameTyped sigs r ⟨.kEval (.nv x) :: rest, env, eval, ret⟩) :
    frameTyped sigs r ⟨rest, env, v :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  rw [checkSeq_kEval_nv hΓ] at h
  exact h

theorem frameTyped_kEval_nv_reject_unbound {sigs : SigTable} {r : Ty} {x : «String»}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    (hx : lookup env x = none) :
    frameTyped sigs r ⟨.kEval (.nv x) :: rest, env, eval, ret⟩ = False := by
  have hΓ : tyLookup (envTyOf env) x = none := by
    have hbridge := envTyOf_lookup env x
    simp only [hx, Option.map_none] at hbridge
    exact hbridge.symm
  simp only [frameTyped, frameWorld]
  simp only [checkSeq, typeOfE, hΓ]

theorem SR_kEval_nv (sigs : SigTable) (reg : AOReg) (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kEval (.nv x)) s r := by
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
          cases hl : lookup env x with
          | none =>
              have h1 : frameTyped sigs (sigRetTy sigs ret)
                  ⟨.kEval (.nv x) :: stmts, env, eval, ret⟩ := hpre.1.1
              rw [frameTyped_kEval_nv_reject_unbound hl] at h1
              exact h1.elim
          | some v =>
              simp only [fstep, hl]
              have hΓ : tyLookup (envTyOf env) x = some [typeOfV v] := by
                have hbridge := envTyOf_lookup env x
                simp only [hl, Option.map_some] at hbridge
                exact hbridge.symm
              refine ⟨⟨frameTyped_kEval_nv hΓ hpre.1.1, hpre.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2

theorem frameTyped_kTest_normal {sigs : SigTable} {r : Ty} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameTyped sigs r ⟨.kTest :: rest, env, .compl Bool.false v :: eval, ret⟩) :
    frameTyped sigs r ⟨rest, env, .boolean Bool.false :: .compl Bool.false v :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  rw [checkSeq_kTest_normal (p := typeOfV v) rfl] at h
  exact h

theorem frameTyped_kTest_throw {sigs : SigTable} {r : Ty} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameTyped sigs r ⟨.kTest :: rest, env, .compl Bool.true v :: eval, ret⟩) :
    frameTyped sigs r ⟨rest, env, .boolean Bool.true :: .compl Bool.true v :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  rw [checkSeq_kTest_throw rfl] at h
  exact h

theorem frameTyped_kTest_reject_nil {sigs : SigTable} {r : Ty}
    {rest : List Instr} {env : Env} {ret : «String»} :
    frameTyped sigs r ⟨.kTest :: rest, env, [], ret⟩ = False := by
  simp [frameTyped, frameWorld, checkSeq, step1]

theorem frameTyped_kTest_reject {sigs : SigTable} {r : Ty} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    (hv : ∀ b w, v ≠ JSValue.compl b w) :
    frameTyped sigs r ⟨.kTest :: rest, env, v :: eval, ret⟩ = False := by
  cases v with
  | compl b w => exact absurd rfl (hv b w)
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _ | descV _ =>
      simp [frameTyped, frameWorld, checkSeq, step1, complOnly, typeOfV]

theorem SR_kTest (sigs : SigTable) (reg : AOReg) (s : FM) (r : Ty) :
    SR_arm sigs reg .kTest s r := by
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
                  ⟨.kTest :: stmts, env, [], ret⟩ := hpre.1.1
              rw [frameTyped_kTest_reject_nil] at h1
              exact h1.elim
          | cons v eval' =>
              by_cases hv : ∃ b w, v = JSValue.compl b w
              · rcases hv with ⟨b, w, rfl⟩
                cases b
                · refine ⟨⟨frameTyped_kTest_normal (r := sigRetTy sigs ret) hpre.1.1, hpre.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2
                · refine ⟨⟨frameTyped_kTest_throw (r := sigRetTy sigs ret) hpre.1.1, hpre.1.2⟩, ?_⟩
                  rw [machineRet_head_swap]
                  exact hpre.2
              · exfalso
                have h1 : frameTyped sigs (sigRetTy sigs ret)
                    ⟨.kTest :: stmts, env, v :: eval', ret⟩ := hpre.1.1
                rw [frameTyped_kTest_reject (v := v) (by
                  intro b w h
                  exact hv ⟨b, w, h⟩)] at h1
                exact h1.elim

theorem frameTyped_kUnwrap {sigs : SigTable} {r : Ty} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    (h : frameTyped sigs r ⟨.kUnwrap :: rest, env, .compl Bool.false v :: eval, ret⟩) :
    frameTyped sigs r ⟨rest, env, v :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  rw [checkSeq_kUnwrap (p := typeOfV v) rfl] at h
  exact h

theorem frameTyped_kUnwrap_reject_nil {sigs : SigTable} {r : Ty}
    {rest : List Instr} {env : Env} {ret : «String»} :
    frameTyped sigs r ⟨.kUnwrap :: rest, env, [], ret⟩ = False := by
  simp [frameTyped, frameWorld, checkSeq, step1]

theorem frameTyped_kUnwrap_reject {sigs : SigTable} {r : Ty} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    (hv : ∀ w, v ≠ JSValue.compl Bool.false w) :
    frameTyped sigs r ⟨.kUnwrap :: rest, env, v :: eval, ret⟩ = False := by
  cases v with
  | compl b w =>
      cases b
      · exact absurd rfl (hv w)
      · simp [frameTyped, frameWorld, checkSeq, step1, unwrapSlot, typeOfV]
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _ | descV _ =>
      simp [frameTyped, frameWorld, checkSeq, step1, unwrapSlot, typeOfV]

theorem SR_kUnwrap (sigs : SigTable) (reg : AOReg) (s : FM) (r : Ty) :
    SR_arm sigs reg .kUnwrap s r := by
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
                  ⟨.kUnwrap :: stmts, env, [], ret⟩ := hpre.1.1
              rw [frameTyped_kUnwrap_reject_nil] at h1
              exact h1.elim
          | cons v eval' =>
              by_cases hv : ∃ w, v = JSValue.compl Bool.false w
              · rcases hv with ⟨w, rfl⟩
                refine ⟨⟨frameTyped_kUnwrap (r := sigRetTy sigs ret) hpre.1.1, hpre.1.2⟩, ?_⟩
                rw [machineRet_head_swap]
                exact hpre.2
              · exfalso
                have h1 : frameTyped sigs (sigRetTy sigs ret)
                    ⟨.kUnwrap :: stmts, env, v :: eval', ret⟩ := hpre.1.1
                rw [frameTyped_kUnwrap_reject (v := v) (by
                  intro w h
                  exact hv ⟨w, h⟩)] at h1
                exact h1.elim