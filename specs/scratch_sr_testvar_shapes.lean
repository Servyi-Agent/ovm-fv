import Metalanguage.SubjectReduction

theorem frameTyped_kTestVar_shape_present {sigs : SigTable} {r : Ty}
    {p : Prim} {T : Ty} {f : JSValue → Bool} {x : «String»} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    {hsc : sigParamsClosed sigs}
    (hT : testTypeP p = some T)
    (hsplit : ∀ (Γ : TyEnv) (σ : List Ty), tyLookup Γ x = some [typeOfV v] →
      split1 x T { Γ := Γ, σ := σ }
        = [{ Γ := (x, [typeOfV v]) :: Γ,
             σ := [.isValue (.boolean (f v))] :: σ }])
    (hΓ : tyLookup (envTyOf env) x = some [typeOfV v])
    (h : frameTyped sigs r ⟨.kTestVar x p :: rest, env, eval, ret⟩) :
    frameTyped sigs r ⟨rest, env, .boolean (f v) :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  have hstep : checkSeq sigs r
      { Γ := envTyOf env, σ := eval.map (fun y => [typeOfV y]) }
      (.kTestVar x p :: rest)
      = checkSeq sigs r
        { Γ := (x, [typeOfV v]) :: envTyOf env,
          σ := [.isValue (.boolean (f v))] :: eval.map (fun y => [typeOfV y]) }
        rest := by
    cases p <;> simp only [testTypeP] at hT <;> cases hT <;>
      simp [checkSeq, testTypeP, hsplit _ _ hΓ, forkTC, List.foldl,
        mergeTC_noFlows]
  rw [hstep] at h
  have hres : ∃ fb, checkSeq sigs r
      { Γ := (x, [typeOfV v]) :: envTyOf env,
        σ := [.isValue (.boolean (f v))] :: eval.map (fun y => [typeOfV y]) }
      rest = TCResult.flows fb ∧ terminal fb = Bool.true := by
    cases hres : checkSeq sigs r
        { Γ := (x, [typeOfV v]) :: envTyOf env,
          σ := [.isValue (.boolean (f v))] :: eval.map (fun y => [typeOfV y]) }
        rest with
    | flows fb => exact ⟨fb, rfl, by rw [hres] at h; exact h⟩
    | reject s why => rw [hres] at h; exact h.elim
  obtain ⟨fb, hchk, hterm⟩ := hres
  have hle : worldLe
      { Γ := envTyOf env,
        σ := [typeOfV (JSValue.boolean (f v))] :: eval.map (fun y => [typeOfV y]) }
      { Γ := (x, [typeOfV v]) :: envTyOf env,
        σ := [.isValue (.boolean (f v))] :: eval.map (fun y => [typeOfV y]) } :=
    ⟨envLe_shadow_same hΓ, stackLe_refl _⟩
  obtain ⟨fb', hchk', hterm'⟩ :=
    checkSeq_specialize_terminal sigs r _ _ rest hsc hle hchk hterm
  rw [hchk']
  exact hterm'

theorem frameTyped_kTestVar_shape_reject_unbound {sigs : SigTable} {r : Ty}
    {p : Prim} {T : Ty} {x : «String»} {rest : List Instr} {env : Env}
    {eval : List JSValue} {ret : «String»}
    (hT : testTypeP p = some T)
    (hΓ : tyLookup (envTyOf env) x = none) :
    frameTyped sigs r ⟨.kTestVar x p :: rest, env, eval, ret⟩ = False := by
  cases p <;> simp only [testTypeP] at hT <;> cases hT <;>
    simp [frameTyped, frameWorld, checkSeq, testTypeP, split1, hΓ, forkTC]

theorem SR_kTestVar_shape (sigs : SigTable) (reg : AOReg)
    (p : Prim) (T : Ty) (f : JSValue → Bool) (x : «String») (s : FM) (r : Ty)
    (hT : testTypeP p = some T)
    (hsplit : ∀ (v : JSValue) (Γ : TyEnv) (σ : List Ty),
      tyLookup Γ x = some [typeOfV v] →
      split1 x T { Γ := Γ, σ := σ }
        = [{ Γ := (x, [typeOfV v]) :: Γ,
             σ := [.isValue (.boolean (f v))] :: σ }])
    (hrun : ∀ (heap : Heap) (v : JSValue), applyPrim heap p v = JSValue.boolean (f v)) :
    SR_arm sigs reg (.kTestVar x p) s r := by
  intro _ _ hsc hpre
  cases s with
  | fdone => exact hpre
  | fell => exact hpre
  | frames fs heap nl =>
      cases fs with
      | nil => exact hpre
      | cons f' fs' =>
          obtain ⟨stmts, env, eval, ret⟩ := f'
          simp only [withHead, stateTyped, framesTypedFrom] at hpre ⊢
          cases hl : lookup env x with
          | none =>
              have hΓ : tyLookup (envTyOf env) x = none := by
                have hbridge := envTyOf_lookup env x
                simp only [hl, Option.map_none] at hbridge
                exact hbridge.symm
              have h1 : frameTyped sigs (sigRetTy sigs ret)
                  ⟨.kTestVar x p :: stmts, env, eval, ret⟩ := hpre.1.1
              rw [frameTyped_kTestVar_shape_reject_unbound hT hΓ] at h1
              exact h1.elim
          | some v =>
              have hΓ : tyLookup (envTyOf env) x = some [typeOfV v] := by
                have hbridge := envTyOf_lookup env x
                simp only [hl, Option.map_some] at hbridge
                exact hbridge.symm
              simp only [fstep, hl] at ⊢
              rw [hrun heap v]
              refine ⟨⟨frameTyped_kTestVar_shape_present (hsc := hsc) hT
                  (hsplit v) hΓ hpre.1.1, hpre.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2

theorem SR_kTestVar_pIsU (sigs : SigTable) (reg : AOReg)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kTestVar x .pIsU) s r :=
  SR_kTestVar_shape sigs reg .pIsU [.anyValue .undef] isUndV x s r
    (by simp [testTypeP])
    (fun v Γ σ hΓ => by
      cases v with
      | compl b w => cases b <;> simp [split1, hΓ, typeOfV, meetTy, meetAtom,
          removeTy, removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing, isUndV]
      | undefined | null | boolean _ | number _ | str _ | obj _ | listV _
        | descV _ =>
          simp [split1, hΓ, typeOfV, meetTy, meetAtom, removeTy, removeAtom,
            tmovesV, tagOf, isBoolClass, isBoolSing, isUndV])
    (by simp [applyPrim])

theorem SR_kTestVar_pIsNull (sigs : SigTable) (reg : AOReg)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kTestVar x .pIsNull) s r :=
  SR_kTestVar_shape sigs reg .pIsNull [.anyValue .null] isNullV x s r
    (by simp [testTypeP])
    (fun v Γ σ hΓ => by
      cases v with
      | compl b w => cases b <;> simp [split1, hΓ, typeOfV, meetTy, meetAtom,
          removeTy, removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing, isNullV]
      | undefined | null | boolean _ | number _ | str _ | obj _ | listV _
        | descV _ =>
          simp [split1, hΓ, typeOfV, meetTy, meetAtom, removeTy, removeAtom,
            tmovesV, tagOf, isBoolClass, isBoolSing, isNullV])
    (by simp [applyPrim])

theorem SR_kTestVar_pNullOrUnd (sigs : SigTable) (reg : AOReg)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kTestVar x .pNullOrUnd) s r :=
  SR_kTestVar_shape sigs reg .pNullOrUnd
    [.anyValue .undef, .anyValue .null]
    (fun v => isUndV v || isNullV v) x s r
    (by simp [testTypeP])
    (fun v Γ σ hΓ => by
      cases v with
      | compl b w => cases b <;> simp [split1, hΓ, typeOfV, meetTy, meetAtom,
          removeTy, removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing,
          isUndV, isNullV]
      | undefined | null | boolean _ | number _ | str _ | obj _ | listV _
        | descV _ =>
          simp [split1, hΓ, typeOfV, meetTy, meetAtom, removeTy, removeAtom,
            tmovesV, tagOf, isBoolClass, isBoolSing, isUndV, isNullV])
    (by simp [applyPrim])

theorem SR_kTestVar_pIsTrue (sigs : SigTable) (reg : AOReg)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kTestVar x .pIsTrue) s r :=
  SR_kTestVar_shape sigs reg .pIsTrue [.isValue (.boolean Bool.true)]
    (fun v => v == JSValue.boolean Bool.true) x s r
    (by simp [testTypeP])
    (fun v Γ σ hΓ => by
      cases v with
      | compl b w => cases b <;> simp [split1, hΓ, typeOfV, meetTy, meetAtom,
          removeTy, removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing]
      | boolean b =>
          cases b <;> simp [split1, hΓ, typeOfV, meetTy, meetAtom, removeTy,
            removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing]
      | undefined | null | number _ | str _ | obj _ | listV _ | descV _ =>
          simp [split1, hΓ, typeOfV, meetTy, meetAtom, removeTy, removeAtom,
            tmovesV, tagOf, isBoolClass, isBoolSing])
    (by simp [applyPrim])

theorem SR_kTestVar_pIsFalse (sigs : SigTable) (reg : AOReg)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kTestVar x .pIsFalse) s r :=
  SR_kTestVar_shape sigs reg .pIsFalse [.isValue (.boolean Bool.false)]
    (fun v => v == JSValue.boolean Bool.false) x s r
    (by simp [testTypeP])
    (fun v Γ σ hΓ => by
      cases v with
      | compl b w => cases b <;> simp [split1, hΓ, typeOfV, meetTy, meetAtom,
          removeTy, removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing]
      | boolean b =>
          cases b <;> simp [split1, hΓ, typeOfV, meetTy, meetAtom, removeTy,
            removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing]
      | undefined | null | number _ | str _ | obj _ | listV _ | descV _ =>
          simp [split1, hΓ, typeOfV, meetTy, meetAtom, removeTy, removeAtom,
            tmovesV, tagOf, isBoolClass, isBoolSing])
    (by simp [applyPrim])

theorem SR_kTestVar_pIsStr (sigs : SigTable) (reg : AOReg)
    (sv : «String») (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kTestVar x (.pIsStr sv)) s r :=
  SR_kTestVar_shape sigs reg (.pIsStr sv) [.isValue (.str sv)]
    (fun v => v == JSValue.str sv) x s r
    (by simp [testTypeP])
    (fun v Γ σ hΓ => by
      cases v with
      | compl b w => cases b <;> simp [split1, hΓ, typeOfV, meetTy, meetAtom,
          removeTy, removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing]
      | str y =>
          by_cases hy : y = sv <;>
            simp [split1, hΓ, typeOfV, meetTy, meetAtom, removeTy, removeAtom,
              tmovesV, tagOf, isBoolClass, isBoolSing, hy]
      | undefined | null | boolean _ | number _ | obj _ | listV _ | descV _ =>
          simp [split1, hΓ, typeOfV, meetTy, meetAtom, removeTy, removeAtom,
            tmovesV, tagOf, isBoolClass, isBoolSing])
    (by simp [applyPrim])