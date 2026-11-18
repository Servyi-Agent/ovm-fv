import Metalanguage.SubjectReduction

theorem split1_pIsObj_singleton {Γ : TyEnv} {x : «String»} {v : JSValue}
    {σ : List Ty}
    (hΓ : tyLookup Γ x = some [typeOfV v]) :
    split1 x [.anyValue .obj] { Γ := Γ, σ := σ }
      = [{ Γ := (x, [typeOfV v]) :: Γ,
           σ := [.isValue (.boolean (isObjV v))] :: σ }] := by
  cases v with
  | compl b w =>
      cases b <;> cases w <;> simp [split1, hΓ, typeOfV, meetTy, meetAtom,
        removeTy, removeAtom, tmovesV, isObjV, tagOf, isBoolClass, isBoolSing]
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _ | descV _ =>
      simp [split1, hΓ, typeOfV, meetTy, meetAtom, removeTy, removeAtom,
        tmovesV, isObjV, tagOf, isBoolClass, isBoolSing]

theorem frameTyped_kTestVar_pIsObj_present {sigs : SigTable} {r : Ty}
    {x : «String»} {v : JSValue} {rest : List Instr} {env : Env}
    {eval : List JSValue} {ret : «String»} {hsc : sigParamsClosed sigs}
    (hΓ : tyLookup (envTyOf env) x = some [typeOfV v])
    (h : frameTyped sigs r ⟨.kTestVar x .pIsObj :: rest, env, eval, ret⟩) :
    frameTyped sigs r ⟨rest, env, .boolean (isObjV v) :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  simp only [checkSeq, testTypeP, split1_pIsObj_singleton hΓ, forkTC, List.foldl,
    mergeTC_noFlows] at h
  have hres : ∃ fb, checkSeq sigs r
      { Γ := (x, [typeOfV v]) :: envTyOf env,
        σ := [.isValue (.boolean (isObjV v))] :: eval.map (fun y => [typeOfV y]) }
      rest = TCResult.flows fb ∧ terminal fb = Bool.true := by
    cases hres : checkSeq sigs r
        { Γ := (x, [typeOfV v]) :: envTyOf env,
          σ := [.isValue (.boolean (isObjV v))] :: eval.map (fun y => [typeOfV y]) }
        rest with
    | flows fb => exact ⟨fb, rfl, by rw [hres] at h; exact h⟩
    | reject s why => rw [hres] at h; exact h.elim
  obtain ⟨fb, hchk, hterm⟩ := hres
  have hle : worldLe
      { Γ := envTyOf env,
        σ := [typeOfV (JSValue.boolean (isObjV v))] :: eval.map (fun y => [typeOfV y]) }
      { Γ := (x, [typeOfV v]) :: envTyOf env,
        σ := [.isValue (.boolean (isObjV v))] :: eval.map (fun y => [typeOfV y]) } :=
    ⟨envLe_shadow_same hΓ, stackLe_refl _⟩
  obtain ⟨fb', hchk', hterm'⟩ :=
    checkSeq_specialize_terminal sigs r _ _ rest hsc hle hchk hterm
  rw [hchk']
  exact hterm'

theorem frameTyped_kTestVar_pIsObj_reject_unbound {sigs : SigTable} {r : Ty}
    {x : «String»} {rest : List Instr} {env : Env} {eval : List JSValue}
    {ret : «String»}
    (hΓ : tyLookup (envTyOf env) x = none) :
    frameTyped sigs r ⟨.kTestVar x .pIsObj :: rest, env, eval, ret⟩ = False := by
  simp [frameTyped, frameWorld, checkSeq, testTypeP, split1, hΓ, forkTC]

theorem SR_kTestVar_pIsObj (sigs : SigTable) (reg : AOReg)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kTestVar x .pIsObj) s r := by
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
              have h1 : frameTyped sigs (sigRetTy sigs ret)
                  ⟨.kTestVar x .pIsObj :: stmts, env, eval, ret⟩ := hpre.1.1
              rw [frameTyped_kTestVar_pIsObj_reject_unbound hΓ] at h1
              exact h1.elim
          | some v =>
              have hΓ : tyLookup (envTyOf env) x = some [typeOfV v] := by
                have hbridge := envTyOf_lookup env x
                simp only [hl, Option.map_some] at hbridge
                exact hbridge.symm
              simp only [fstep, hl] at ⊢
              refine ⟨⟨frameTyped_kTestVar_pIsObj_present (hsc := hsc) hΓ
                  hpre.1.1, hpre.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2