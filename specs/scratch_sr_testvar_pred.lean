import Metalanguage.SubjectReduction

theorem frameTyped_kTestVar_pPred_present {sigs : SigTable} {r : Ty}
    {f : «String»} {b : Bool} {dec : VTy → Option Bool}
    {g : JSValue → Bool} {x : «String»} {v : JSValue}
    {rest : List Instr} {env : Env} {eval : List JSValue} {ret : «String»}
    {hsc : sigParamsClosed sigs}
    (hdec : predDecide f = some dec)
    (hmem : ∀ (Γ : TyEnv) (σ : List Ty), tyLookup Γ x = some [typeOfV v] →
      { Γ := (x, [typeOfV v]) :: Γ,
        σ := [.isValue (.boolean (g v))] :: σ }
      ∈ splitP1 x (fun a => (dec a).map (fun bv => bv == b))
        { Γ := Γ, σ := σ })
    (hΓ : tyLookup (envTyOf env) x = some [typeOfV v])
    (h : frameTyped sigs r ⟨.kTestVar x (.pPred f b) :: rest, env, eval, ret⟩) :
    frameTyped sigs r ⟨rest, env, .boolean (g v) :: eval, ret⟩ := by
  simp only [frameTyped, frameWorld, List.map_cons] at h ⊢
  simp only [checkSeq, hdec] at h
  have hmem0 := hmem (Γ := envTyOf env)
    (σ := eval.map (fun y => [typeOfV y])) hΓ
  have hne : splitP1 x (fun a => (dec a).map (fun bv => bv == b))
      { Γ := envTyOf env, σ := eval.map (fun y => [typeOfV y]) } ≠ [] := by
    intro hnil
    rw [hnil] at hmem0
    cases hmem0
  cases hfork : forkTC (Instr.kTestVar x (Prim.pPred f b))
      (splitP1 x (fun a => (dec a).map (fun bv => bv == b))
        { Γ := envTyOf env, σ := eval.map (fun y => [typeOfV y]) })
      (fun u => checkSeq sigs r u rest) with
  | flows fb =>
      have hterm0 : terminal fb = Bool.true := by
        rw [hfork] at h; exact h
      cases hws : splitP1 x (fun a => (dec a).map (fun bv => bv == b))
          { Γ := envTyOf env, σ := eval.map (fun y => [typeOfV y]) } with
      | nil => exact absurd hws hne
      | cons u0 us =>
          rw [hws] at hfork hmem0
          have hfold : (u0 :: us).foldl
              (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows
            = TCResult.flows fb := by
            simpa [forkTC] using hfork
          obtain ⟨fbm, hchk⟩ :=
            fold_all_flows (J := fun u => checkSeq sigs r u rest) (u0 :: us) fb
              hfold
              { Γ := (x, [typeOfV v]) :: envTyOf env,
                σ := [.isValue (.boolean (g v))]
                  :: eval.map (fun y => [typeOfV y]) }
              hmem0
          have hfall : fbm.falls = [] :=
            fold_terminal_falls_nil (J := fun u => checkSeq sigs r u rest)
              (u0 :: us) fb hfold hterm0
              { Γ := (x, [typeOfV v]) :: envTyOf env,
                σ := [.isValue (.boolean (g v))]
                  :: eval.map (fun y => [typeOfV y]) }
              hmem0 fbm hchk
          have hexit : fbm.exits = Bool.true :=
            checkSeq_exits sigs r
              { Γ := (x, [typeOfV v]) :: envTyOf env,
                σ := [.isValue (.boolean (g v))]
                  :: eval.map (fun y => [typeOfV y]) }
              rest fbm hchk hfall
          have htermm : terminal fbm = Bool.true := by
            simp [terminal, hfall, hexit]
          have hle : worldLe
              { Γ := envTyOf env,
                σ := [typeOfV (JSValue.boolean (g v))]
                  :: eval.map (fun y => [typeOfV y]) }
              { Γ := (x, [typeOfV v]) :: envTyOf env,
                σ := [.isValue (.boolean (g v))]
                  :: eval.map (fun y => [typeOfV y]) } :=
            ⟨envLe_shadow_same hΓ, stackLe_refl _⟩
          obtain ⟨fb', hchk', hterm'⟩ :=
            checkSeq_specialize_terminal sigs r _ _ rest hsc hle hchk htermm
          simp only [typeOfV] at hchk' ⊢
          rw [hchk']
          exact hterm'
  | reject s why => rw [hfork] at h; exact h.elim

theorem SR_kTestVar_pPred_split (sigs : SigTable) (reg : AOReg)
    (f : «String») (b : Bool) (dec : VTy → Option Bool)
    (g : JSValue → Bool) (x : «String») (s : FM) (r : Ty)
    (hdec : predDecide f = some dec)
    (hmem : ∀ (v : JSValue) (Γ : TyEnv) (σ : List Ty),
      tyLookup Γ x = some [typeOfV v] →
      { Γ := (x, [typeOfV v]) :: Γ,
        σ := [.isValue (.boolean (g v))] :: σ }
      ∈ splitP1 x (fun a => (dec a).map (fun bv => bv == b))
        { Γ := Γ, σ := σ })
    (hrun : ∀ (heap : Heap) (v : JSValue),
      applyPrim heap (.pPred f b) v = JSValue.boolean (g v)) :
    SR_arm sigs reg (.kTestVar x (.pPred f b)) s r := by
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
              exfalso
              have h1 : frameTyped sigs (sigRetTy sigs ret)
                  ⟨.kTestVar x (.pPred f b) :: stmts, env, eval, ret⟩ :=
                hpre.1.1
              simp only [frameTyped, frameWorld, checkSeq, hdec, splitP1,
                hΓ, forkTC] at h1
          | some v =>
              have hΓ : tyLookup (envTyOf env) x = some [typeOfV v] := by
                have hbridge := envTyOf_lookup env x
                simp only [hl, Option.map_some] at hbridge
                exact hbridge.symm
              simp only [fstep, hl] at ⊢
              rw [hrun heap v]
              refine ⟨⟨frameTyped_kTestVar_pPred_present (hsc := hsc) hdec
                  (hmem v) hΓ hpre.1.1, hpre.1.2⟩, ?_⟩
              rw [machineRet_head_swap]
              exact hpre.2

def dataPredResult (v : JSValue) : Bool :=
  match v with
  | .descV (.mk value writable _ _ _ _) =>
      value.isSome || writable.isSome
  | _ => Bool.false

def dataPredDec : VTy → Option Bool :=
  fun a =>
    match a with
    | .desc fs => some (fs.any (fun fld => fData.contains fld))
    | _ => none

theorem predDecide_data :
    predDecide "IsDataDescriptor" = some dataPredDec := rfl

theorem applyPrim_pPred_data (heap : Heap) (b : Bool) (v : JSValue) :
    applyPrim heap (.pPred "IsDataDescriptor" b) v
      = .boolean (b == dataPredResult v) := by
  cases v with
  | compl abrupt w =>
      cases abrupt <;> cases b <;> simp [applyPrim, dataPredResult]
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _ =>
      cases b <;> simp [applyPrim, dataPredResult]
  | descV d =>
      cases d with
      | mk value writable getter setter enumerable configurable =>
          cases b <;> simp [applyPrim, dataPredResult]

theorem field_value_eq_self :
    (Field.value == Field.value) = Bool.true := rfl
theorem field_writable_eq_self :
    (Field.writable == Field.writable) = Bool.true := rfl

theorem field_getter_ne_value :
    (Field.getter == Field.value) = Bool.false := rfl
theorem field_getter_ne_writable :
    (Field.getter == Field.writable) = Bool.false := rfl
theorem field_setter_ne_value :
    (Field.setter == Field.value) = Bool.false := rfl
theorem field_setter_ne_writable :
    (Field.setter == Field.writable) = Bool.false := rfl
theorem field_enumerable_ne_value :
    (Field.enumerable == Field.value) = Bool.false := rfl
theorem field_enumerable_ne_writable :
    (Field.enumerable == Field.writable) = Bool.false := rfl
theorem field_configurable_ne_value :
    (Field.configurable == Field.value) = Bool.false := rfl
theorem field_configurable_ne_writable :
    (Field.configurable == Field.writable) = Bool.false := rfl

theorem fieldsOf_data_eq (value : Option JSValue)
    (writable enumerable configurable : Option Bool)
    (getter setter : Option Nat) :
    (fieldsOf (Descriptor.mk value writable getter setter enumerable
        configurable)).any (fun fld => fData.contains fld)
      = (value.isSome || writable.isSome) := by
  cases value <;> cases writable <;> cases getter <;> cases setter <;>
    cases enumerable <;> cases configurable <;>
      simp [fieldsOf, fData, field_value_eq_self,
        field_writable_eq_self, field_getter_ne_value,
        field_getter_ne_writable, field_setter_ne_value,
        field_setter_ne_writable, field_enumerable_ne_value,
        field_enumerable_ne_writable, field_configurable_ne_value,
        field_configurable_ne_writable]

theorem splitP1_pPred_data_machine (b : Bool) {Γ : TyEnv} {x : «String»}
    {v : JSValue} {σ : List Ty}
    (hΓ : tyLookup Γ x = some [typeOfV v]) :
    { Γ := (x, [typeOfV v]) :: Γ,
      σ := [.isValue (.boolean (b == dataPredResult v))] :: σ }
      ∈ splitP1 x (fun a => (dataPredDec a).map (fun bv => bv == b))
        { Γ := Γ, σ := σ } := by
  cases v with
  | compl b' w =>
      cases b' <;> cases b <;>
        simp [splitP1, splitP1At, hΓ, typeOfV, dataPredDec, dataPredResult]
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _ =>
      cases b <;>
        simp [splitP1, splitP1At, hΓ, typeOfV, dataPredDec, dataPredResult]
  | descV d =>
      cases d with
      | mk value writable getter setter enumerable configurable =>
          simp only [splitP1, splitP1At, hΓ, typeOfV, dataPredDec,
            dataPredResult]
          have hd := fieldsOf_data_eq value writable enumerable configurable
            getter setter
          simp [List.flatMap, splitP1At, hd]
          cases value <;> cases writable <;> cases b <;> simp

theorem SR_kTestVar_pPred_data (sigs : SigTable) (reg : AOReg)
    (b : Bool) (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kTestVar x (.pPred "IsDataDescriptor" b)) s r :=
  SR_kTestVar_pPred_split sigs reg "IsDataDescriptor" b dataPredDec
    (fun v => b == dataPredResult v) x s r
    predDecide_data
    (fun _ Γ σ hΓ => splitP1_pPred_data_machine b hΓ)
    (fun heap v => applyPrim_pPred_data heap b v)

def accPredResult (v : JSValue) : Bool :=
  match v with
  | .descV (.mk _ _ getter setter _ _) =>
      getter.isSome || setter.isSome
  | _ => Bool.false

def accPredDec : VTy → Option Bool :=
  fun a =>
    match a with
    | .desc fs => some (fs.any (fun fld => fAcc.contains fld))
    | _ => none

theorem predDecide_acc :
    predDecide "IsAccessorDescriptor" = some accPredDec := rfl

theorem applyPrim_pPred_acc (heap : Heap) (b : Bool) (v : JSValue) :
    applyPrim heap (.pPred "IsAccessorDescriptor" b) v
      = .boolean (b == accPredResult v) := by
  cases v with
  | compl abrupt w =>
      cases abrupt <;> cases b <;> simp [applyPrim, accPredResult]
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _ =>
      cases b <;> simp [applyPrim, accPredResult]
  | descV d =>
      cases d with
      | mk value writable getter setter enumerable configurable =>
          cases b <;> simp [applyPrim, accPredResult]

theorem field_getter_eq_self :
    (Field.getter == Field.getter) = Bool.true := rfl
theorem field_setter_eq_self :
    (Field.setter == Field.setter) = Bool.true := rfl

theorem field_value_ne_getter :
    (Field.value == Field.getter) = Bool.false := rfl
theorem field_value_ne_setter :
    (Field.value == Field.setter) = Bool.false := rfl
theorem field_writable_ne_getter :
    (Field.writable == Field.getter) = Bool.false := rfl
theorem field_writable_ne_setter :
    (Field.writable == Field.setter) = Bool.false := rfl
theorem field_enumerable_ne_getter :
    (Field.enumerable == Field.getter) = Bool.false := rfl
theorem field_enumerable_ne_setter :
    (Field.enumerable == Field.setter) = Bool.false := rfl
theorem field_configurable_ne_getter :
    (Field.configurable == Field.getter) = Bool.false := rfl
theorem field_configurable_ne_setter :
    (Field.configurable == Field.setter) = Bool.false := rfl

theorem fieldsOf_acc_eq (value : Option JSValue)
    (writable enumerable configurable : Option Bool)
    (getter setter : Option Nat) :
    (fieldsOf (Descriptor.mk value writable getter setter enumerable
        configurable)).any (fun fld => fAcc.contains fld)
      = (getter.isSome || setter.isSome) := by
  cases value <;> cases writable <;> cases getter <;> cases setter <;>
    cases enumerable <;> cases configurable <;>
      simp [fieldsOf, fAcc, field_getter_eq_self,
        field_setter_eq_self, field_value_ne_getter,
        field_value_ne_setter, field_writable_ne_getter,
        field_writable_ne_setter, field_enumerable_ne_getter,
        field_enumerable_ne_setter, field_configurable_ne_getter,
        field_configurable_ne_setter]

theorem splitP1_pPred_acc_machine (b : Bool) {Γ : TyEnv} {x : «String»}
    {v : JSValue} {σ : List Ty}
    (hΓ : tyLookup Γ x = some [typeOfV v]) :
    { Γ := (x, [typeOfV v]) :: Γ,
      σ := [.isValue (.boolean (b == accPredResult v))] :: σ }
      ∈ splitP1 x (fun a => (accPredDec a).map (fun bv => bv == b))
        { Γ := Γ, σ := σ } := by
  cases v with
  | compl b' w =>
      cases b' <;> cases b <;>
        simp [splitP1, splitP1At, hΓ, typeOfV, accPredDec, accPredResult]
  | undefined | null | boolean _ | number _ | str _ | obj _ | listV _ =>
      cases b <;>
        simp [splitP1, splitP1At, hΓ, typeOfV, accPredDec, accPredResult]
  | descV d =>
      cases d with
      | mk value writable getter setter enumerable configurable =>
          simp only [splitP1, splitP1At, hΓ, typeOfV, accPredDec,
            accPredResult]
          have hd := fieldsOf_acc_eq value writable enumerable configurable
            getter setter
          simp [List.flatMap, splitP1At, hd]
          cases getter <;> cases setter <;> cases b <;> simp

theorem SR_kTestVar_pPred_acc (sigs : SigTable) (reg : AOReg)
    (b : Bool) (x : «String») (s : FM) (r : Ty) :
    SR_arm sigs reg (.kTestVar x (.pPred "IsAccessorDescriptor" b)) s r :=
  SR_kTestVar_pPred_split sigs reg "IsAccessorDescriptor" b accPredDec
    (fun v => b == accPredResult v) x s r
    predDecide_acc
    (fun _ Γ σ hΓ => splitP1_pPred_acc_machine b hΓ)
    (fun heap v => applyPrim_pPred_acc heap b v)