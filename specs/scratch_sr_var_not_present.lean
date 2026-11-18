import Metalanguage.SubjectReduction

theorem meetTy_typeOfV_notPresent (v : JSValue) :
    meetTy [typeOfV v] [.notPresent] = [] := by
  cases v with
  | compl b w => cases b <;> simp [typeOfV, meetTy, meetAtom]
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _ | descV _ =>
      simp [typeOfV, meetTy, meetAtom]

theorem removeTy_typeOfV_notPresent (v : JSValue) :
    removeTy [typeOfV v] [.notPresent] = [typeOfV v] := by
  cases v with
  | compl b w => cases b <;> simp [typeOfV, removeTy, removeAtom, tmovesV,
      isBoolClass, isBoolSing]
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _ | descV _ =>
      simp [typeOfV, removeTy, removeAtom, tmovesV, isBoolClass, isBoolSing]

theorem envLe_shadow_same {Γ : TyEnv} {x : «String»} {t : Ty}
    (h : tyLookup Γ x = some t) : envLe Γ ((x, t) :: Γ) := by
  refine ⟨fun y => ?_, fun y s' hs' => ?_, fun y s hs hne => ?_⟩
  all_goals
    by_cases hxy : x = y <;> simp_all [tyLookup, tyLe] <;>
      first
        | exact tmoves_refl _
        | (intro a ha; exact ⟨a, ha, tmovesV_refl a⟩)

theorem frameTyped_kEval_varNotPresent_absent {sigs : SigTable} {r : Ty}
    {x : «String»} {rest : List Instr} {env : Env} {eval : List JSValue}
    {ret : «String»}
    (hΓ : tyLookup (envTyOf env) x = none)
    (h : frameTyped sigs r ⟨.kEval (.varNotPresent x) :: rest, env, eval, ret⟩) :
    frameTyped sigs r ⟨rest, env, .boolean Bool.true :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  simp only [checkSeq, hΓ] at h
  exact h

theorem frameTyped_kEval_varNotPresent_present {sigs : SigTable} {r : Ty}
    {x : «String»} {v : JSValue} {rest : List Instr} {env : Env}
    {eval : List JSValue} {ret : «String»} {hsc : sigParamsClosed sigs}
    (hΓ : tyLookup (envTyOf env) x = some [typeOfV v])
    (h : frameTyped sigs r ⟨.kEval (.varNotPresent x) :: rest, env, eval, ret⟩) :
    frameTyped sigs r ⟨rest, env, .boolean Bool.false :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  have hstep : checkSeq sigs r
      { Γ := envTyOf env, σ := eval.map (fun y => [typeOfV y]) }
      (.kEval (.varNotPresent x) :: rest)
      = checkSeq sigs r
        { Γ := (x, [typeOfV v]) :: envTyOf env,
          σ := [.isValue (.boolean Bool.false)] :: eval.map (fun y => [typeOfV y]) }
        rest := by
    simp [checkSeq, hΓ, split1, meetTy_typeOfV_notPresent,
      removeTy_typeOfV_notPresent, forkTC, mergeTC_noFlows]
  rw [hstep] at h
  have hres : ∃ fb, checkSeq sigs r
      { Γ := (x, [typeOfV v]) :: envTyOf env,
        σ := [.isValue (.boolean Bool.false)] :: eval.map (fun y => [typeOfV y]) }
      rest = TCResult.flows fb ∧ terminal fb = Bool.true := by
    cases hres : checkSeq sigs r
        { Γ := (x, [typeOfV v]) :: envTyOf env,
          σ := [.isValue (.boolean Bool.false)] :: eval.map (fun y => [typeOfV y]) }
        rest with
    | flows fb => exact ⟨fb, rfl, by rw [hres] at h; exact h⟩
    | reject s why => rw [hres] at h; exact h.elim
  obtain ⟨fb, hchk, hterm⟩ := hres
  have hle : worldLe
      { Γ := envTyOf env,
        σ := [.isValue (.boolean Bool.false)] :: eval.map (fun y => [typeOfV y]) }
      { Γ := (x, [typeOfV v]) :: envTyOf env,
        σ := [.isValue (.boolean Bool.false)] :: eval.map (fun y => [typeOfV y]) } :=
    ⟨envLe_shadow_same hΓ, stackLe_refl _⟩
  obtain ⟨fb', hchk', hterm'⟩ :=
    checkSeq_specialize_terminal sigs r _ _ rest hsc hle hchk hterm
  simp only [typeOfV] at hchk' ⊢
  rw [hchk']
  exact hterm'

theorem SR_kEval_varNotPresent (sigs : SigTable) (reg : AOReg)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kEval (.varNotPresent x)) s r := by
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
          cases hl : lookup env x with
          | none =>
              have hΓ : tyLookup (envTyOf env) x = none := by
                have hbridge := envTyOf_lookup env x
                simp only [hl, Option.map_none] at hbridge
                exact hbridge.symm
              simp only [fstep, hl]
              refine ⟨⟨frameTyped_kEval_varNotPresent_absent hΓ hpre.1.1,
                hpre.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2
          | some v =>
              have hΓ : tyLookup (envTyOf env) x = some [typeOfV v] := by
                have hbridge := envTyOf_lookup env x
                simp only [hl, Option.map_some] at hbridge
                exact hbridge.symm
              simp only [fstep, hl]
              refine ⟨⟨frameTyped_kEval_varNotPresent_present (hsc := hsc) hΓ
                  hpre.1.1, hpre.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2