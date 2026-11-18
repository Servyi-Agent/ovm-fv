import Metalanguage.SubjectReduction

def isCompletionResult (v : JSValue) : Bool :=
  match v with
  | .compl _ _ => Bool.true
  | _ => Bool.false

theorem applyPrim_pIsCompletion_eq (heap : Heap) (v : JSValue) :
    applyPrim heap .pIsCompletion v = .boolean (isCompletionResult v) := by
  cases v <;> simp [applyPrim, isCompletionResult]

theorem frameTyped_kTestVar_pIsCompletion_present {sigs : SigTable} {r : Ty}
    {x : «String»} {v : JSValue} {rest : List Instr} {env : Env}
    {eval : List JSValue} {ret : «String»} {hsc : sigParamsClosed sigs}
    (hΓ : tyLookup (envTyOf env) x = some [typeOfV v])
    (h : frameTyped sigs r ⟨.kTestVar x .pIsCompletion :: rest, env, eval, ret⟩) :
    frameTyped sigs r ⟨rest, env, .boolean (isCompletionResult v) :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  simp only [checkSeq, testTypeP, hΓ] at h
  exact frameTyped_pushRefine (ret := ret) hsc (slotLe_bool_result _) h

theorem frameTyped_kTestVar_pIsCompletion_reject_unbound {sigs : SigTable}
    {r : Ty} {x : «String»} {rest : List Instr} {env : Env}
    {eval : List JSValue} {ret : «String»}
    (hΓ : tyLookup (envTyOf env) x = none) :
    frameTyped sigs r ⟨.kTestVar x .pIsCompletion :: rest, env, eval, ret⟩
      = False := by
  simp [frameTyped, frameWorld, checkSeq, testTypeP, hΓ]

theorem SR_kTestVar_pIsCompletion (sigs : SigTable) (reg : AOReg)
    (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kTestVar x .pIsCompletion) s r := by
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
                  ⟨.kTestVar x .pIsCompletion :: stmts, env, eval, ret⟩ :=
                hpre.1.1
              rw [frameTyped_kTestVar_pIsCompletion_reject_unbound hΓ] at h1
              exact h1.elim
          | some v =>
              have hΓ : tyLookup (envTyOf env) x = some [typeOfV v] := by
                have hbridge := envTyOf_lookup env x
                simp only [hl, Option.map_some] at hbridge
                exact hbridge.symm
              simp only [fstep, hl] at ⊢
              rw [applyPrim_pIsCompletion_eq heap v]
              refine ⟨⟨frameTyped_kTestVar_pIsCompletion_present (hsc := hsc) hΓ
                  hpre.1.1, hpre.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2