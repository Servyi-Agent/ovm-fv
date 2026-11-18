import Metalanguage.SubjectReduction

def isTypeResult (s : «String») (v : JSValue) : Bool :=
  if s = "Boolean" then
    match v with
    | .boolean _ => Bool.true
    | _ => Bool.false
  else if s = "Number" then
    match v with
    | .number _ => Bool.true
    | _ => Bool.false
  else if s = "String" then
    match v with
    | .str _ => Bool.true
    | _ => Bool.false
  else Bool.false

theorem split1_pIsType_singleton (s : «String») (v : JSValue)
    (Γ : TyEnv) (σ : List Ty) (x : «String»)
    (hΓ : tyLookup Γ x = some [typeOfV v]) :
    split1 x (typeMask s) { Γ := Γ, σ := σ }
      = [{ Γ := (x, [typeOfV v]) :: Γ,
           σ := [.isValue (.boolean (isTypeResult s v))] :: σ }] := by
  by_cases h1 : s = "Boolean"
  · subst h1
    cases v with
    | compl b w => cases b <;> simp [split1, hΓ, typeOfV, typeMask, meetTy,
        meetAtom, removeTy, removeAtom, tmovesV, tagOf, isBoolClass,
        isBoolSing, isTypeResult]
    | undefined | null | number _ | str _ | obj _ | listV _ | descV _ =>
        simp [split1, hΓ, typeOfV, typeMask, meetTy, meetAtom, removeTy,
          removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing, isTypeResult]
    | boolean b =>
        cases b <;> simp [split1, hΓ, typeOfV, typeMask, meetTy, meetAtom,
          removeTy, removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing,
          isTypeResult]
  · by_cases h2 : s = "Number"
    · subst h2
      cases v with
      | compl b w => cases b <;> simp [split1, hΓ, typeOfV, typeMask, meetTy,
          meetAtom, removeTy, removeAtom, tmovesV, tagOf, isBoolClass,
          isBoolSing, isTypeResult]
      | undefined | null | boolean _ | str _ | obj _ | listV _ | descV _ =>
          simp [split1, hΓ, typeOfV, typeMask, meetTy, meetAtom, removeTy,
            removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing, isTypeResult]
      | number n =>
          simp [split1, hΓ, typeOfV, typeMask, meetTy, meetAtom, removeTy,
            removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing, isTypeResult]
    · by_cases h3 : s = "String"
      · subst h3
        cases v with
        | compl b w => cases b <;> simp [split1, hΓ, typeOfV, typeMask, meetTy,
            meetAtom, removeTy, removeAtom, tmovesV, tagOf, isBoolClass,
            isBoolSing, isTypeResult]
        | undefined | null | boolean _ | number _ | obj _ | listV _ | descV _ =>
            simp [split1, hΓ, typeOfV, typeMask, meetTy, meetAtom, removeTy,
              removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing, isTypeResult]
        | str y =>
            simp [split1, hΓ, typeOfV, typeMask, meetTy, meetAtom, removeTy,
              removeAtom, tmovesV, tagOf, isBoolClass, isBoolSing, isTypeResult]
      · cases v with
        | compl b w => cases b <;>
            simp [split1, hΓ, typeOfV, typeMask, meetTy, meetAtom, removeTy,
              removeAtom, tagOf, isBoolClass, isTypeResult, h1, h2, h3]
        | undefined | null | boolean _ | number _ | str _ | obj _ | listV _
          | descV _ =>
            simp [split1, hΓ, typeOfV, typeMask, meetTy, meetAtom, removeTy,
              removeAtom, tagOf, isBoolClass, isTypeResult, h1, h2, h3]

theorem applyPrim_pIsType_eq (s : «String») (heap : Heap) (v : JSValue) :
    applyPrim heap (.pIsType s) v = .boolean (isTypeResult s v) := by
  simp only [applyPrim]
  split <;> simp_all [isTypeResult] <;> try rfl

theorem SR_kTestVar_pIsType (sigs : SigTable) (reg : AOReg)
    (s : «String») (x : «String») (st : FM) (r : Ty) :
    SR_arm sigs reg (.kTestVar x (.pIsType s)) st r :=
  SR_kTestVar_shape sigs reg (.pIsType s) (typeMask s)
    (isTypeResult s) x st r
    (by simp [testTypeP])
    (fun v Γ σ hΓ => split1_pIsType_singleton s v Γ σ x hΓ)
    (applyPrim_pIsType_eq s)