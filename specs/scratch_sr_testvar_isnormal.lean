import Metalanguage.SubjectReduction

def normalResult (v : JSValue) : Bool :=
  match v with
  | .compl Bool.false _ => Bool.true
  | _ => Bool.false

def normalDec : VTy → Option Bool :=
  fun a =>
    match a with
    | .complN _ => some Bool.true
    | .complT => some Bool.false
    | _ => none

theorem primDecide_pIsNormalC_eq :
    primDecide .pIsNormalC = some normalDec := rfl

theorem applyPrim_pIsNormalC_eq (heap : Heap) (v : JSValue) :
    applyPrim heap .pIsNormalC v = .boolean (normalResult v) := by
  cases v with
  | compl b w => cases b <;> simp [applyPrim, normalResult]
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _ | descV _ =>
      simp [applyPrim, normalResult]

theorem splitP1_pIsNormal_machine {Γ : TyEnv} {x : «String»} {v : JSValue}
    {σ : List Ty}
    (hΓ : tyLookup Γ x = some [typeOfV v]) :
    { Γ := (x, [typeOfV v]) :: Γ,
      σ := [.isValue (.boolean (normalResult v))] :: σ }
      ∈ splitP1 x normalDec { Γ := Γ, σ := σ } := by
  cases v with
  | compl b w =>
      cases b <;> simp [splitP1, splitP1At, hΓ, typeOfV, normalDec,
        normalResult]
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _
    | descV _ =>
      simp [splitP1, splitP1At, hΓ, typeOfV, normalDec, normalResult]

theorem frameTyped_kTestVar_pIsNormalC_present {sigs : SigTable} {r : Ty}
    {x : «String»} {v : JSValue} {rest : List Instr} {env : Env}
    {eval : List JSValue} {ret : «String»} {hsc : sigParamsClosed sigs}
    (hΓ : tyLookup (envTyOf env) x = some [typeOfV v])
    (h : frameTyped sigs r ⟨.kTestVar x .pIsNormalC :: rest, env, eval, ret⟩) :
    frameTyped sigs r ⟨rest, env, .boolean (normalResult v) :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  simp only [checkSeq, primDecide_pIsNormalC_eq] at h
  have hmem := splitP1_pIsNormal_machine (Γ := envTyOf env)
    (σ := eval.map (fun y => [typeOfV y])) hΓ
  have hne : splitP1 x normalDec
      { Γ := envTyOf env, σ := eval.map (fun y => [typeOfV y]) } ≠ [] := by
    intro hnil
    rw [hnil] at hmem
    cases hmem
  cases hfork : forkTC (Instr.kTestVar x Prim.pIsNormalC)
      (splitP1 x normalDec
        { Γ := envTyOf env, σ := eval.map (fun y => [typeOfV y]) })
      (fun u => checkSeq sigs r u rest) with
  | flows fb =>
      have hterm0 : terminal fb = Bool.true := by
        rw [hfork] at h; exact h
      cases hws : splitP1 x normalDec
          { Γ := envTyOf env, σ := eval.map (fun y => [typeOfV y]) } with
      | nil => exact absurd hws hne
      | cons u0 us =>
          rw [hws] at hfork hmem
          have hfold : (u0 :: us).foldl
              (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows
            = TCResult.flows fb := by
            simpa [forkTC] using hfork
          obtain ⟨fbm, hchk⟩ :=
            fold_all_flows (J := fun u => checkSeq sigs r u rest) (u0 :: us) fb
              hfold
              { Γ := (x, [typeOfV v]) :: envTyOf env,
                σ := [.isValue (.boolean (normalResult v))]
                  :: eval.map (fun y => [typeOfV y]) }
              hmem
          have hfall : fbm.falls = [] :=
            fold_terminal_falls_nil (J := fun u => checkSeq sigs r u rest)
              (u0 :: us) fb hfold hterm0
              { Γ := (x, [typeOfV v]) :: envTyOf env,
                σ := [.isValue (.boolean (normalResult v))]
                  :: eval.map (fun y => [typeOfV y]) }
              hmem fbm hchk
          have hexit : fbm.exits = Bool.true :=
            checkSeq_exits sigs r
              { Γ := (x, [typeOfV v]) :: envTyOf env,
                σ := [.isValue (.boolean (normalResult v))]
                  :: eval.map (fun y => [typeOfV y]) }
              rest fbm hchk hfall
          have htermm : terminal fbm = Bool.true := by
            simp [terminal, hfall, hexit]
          have hle : worldLe
              { Γ := envTyOf env,
                σ := [typeOfV (JSValue.boolean (normalResult v))]
                  :: eval.map (fun y => [typeOfV y]) }
              { Γ := (x, [typeOfV v]) :: envTyOf env,
                σ := [.isValue (.boolean (normalResult v))]
                  :: eval.map (fun y => [typeOfV y]) } :=
            ⟨envLe_shadow_same hΓ, stackLe_refl _⟩
          obtain ⟨fb', hchk', hterm'⟩ :=
            checkSeq_specialize_terminal sigs r _ _ rest hsc hle hchk htermm
          simp only [typeOfV] at hchk' ⊢
          rw [hchk']
          exact hterm'
  | reject s why => rw [hfork] at h; exact h.elim

theorem frameTyped_kTestVar_pIsNormalC_reject_unbound {sigs : SigTable}
    {r : Ty} {x : «String»} {rest : List Instr} {env : Env}
    {eval : List JSValue} {ret : «String»}
    (hΓ : tyLookup (envTyOf env) x = none) :
    frameTyped sigs r ⟨.kTestVar x .pIsNormalC :: rest, env, eval, ret⟩
      = False := by
  simp [frameTyped, frameWorld, checkSeq, primDecide_pIsNormalC_eq, splitP1,
    hΓ, forkTC]

theorem SR_kTestVar_pIsNormalC (sigs : SigTable) (reg : AOReg)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kTestVar x .pIsNormalC) s r := by
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
                  ⟨.kTestVar x .pIsNormalC :: stmts, env, eval, ret⟩ :=
                hpre.1.1
              rw [frameTyped_kTestVar_pIsNormalC_reject_unbound hΓ] at h1
              exact h1.elim
          | some v =>
              have hΓ : tyLookup (envTyOf env) x = some [typeOfV v] := by
                have hbridge := envTyOf_lookup env x
                simp only [hl, Option.map_some] at hbridge
                exact hbridge.symm
              simp only [fstep, hl] at ⊢
              rw [applyPrim_pIsNormalC_eq heap v]
              refine ⟨⟨frameTyped_kTestVar_pIsNormalC_present (hsc := hsc) hΓ
                  hpre.1.1, hpre.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2