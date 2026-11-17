import Metalanguage.SubjectReduction

theorem decMono_map {dec : VTy → Option Bool} (g : Bool → Bool) (hm : DecMono dec) :
    DecMono (fun a => (dec a).map g) := by
  intro a' a haa
  obtain ⟨hs, hn⟩ := hm a' a haa
  dsimp only
  constructor
  · intro b hb
    cases hd' : dec a' with
    | none => rw [hd'] at hb; cases hb
    | some bv =>
        rw [hd'] at hb
        simp only [Option.map_some, Option.some.injEq] at hb
        subst hb
        rcases hs bv hd' with hsame | hnone
        · rw [hsame]; simp
        · rw [hnone]; simp
  · intro hnone
    cases hd' : dec a' with
    | none => rw [hn hd']; simp
    | some bv => rw [hd'] at hnone; simp at hnone

theorem markDebt_specLe (why : «String») {r' r : TCResult}
    (h : specLe r' r) : specLe (markDebt why r') (markDebt why r) := by
  cases r with
  | reject s w => exact trivial
  | flows f =>
      obtain ⟨f', rfl, hcov⟩ := specLe_flows_elim h
      simpa [markDebt, specLe] using hcov

theorem anyOf_bare (cs : List Ctor) :
    ∀ b ∈ anyOf cs, isBareVTy b = Bool.true := by
  intro b hb
  simp only [anyOf, List.mem_map] at hb
  obtain ⟨c, hc, rfl⟩ := hb
  simp [isBareVTy]

theorem typeMask_bare (s : «String») :
    ∀ b ∈ typeMask s, isBareVTy b = Bool.true := by
  intro b hb
  unfold typeMask at hb
  split at hb <;> simp_all [isBareVTy]

theorem markDebt_specLe_left (why : «String») {r' r : TCResult}
    (h : specLe r' r) : specLe (markDebt why r') r := by
  cases r with
  | reject s w => exact trivial
  | flows f =>
      obtain ⟨f', rfl, hcov⟩ := specLe_flows_elim h
      simpa [markDebt, specLe] using hcov

theorem markDebt_specLe_right (why : «String») {r' r : TCResult}
    (h : specLe r' r) : specLe r' (markDebt why r) := by
  cases r with
  | reject s w => exact trivial
  | flows f =>
      obtain ⟨f', rfl, hcov⟩ := specLe_flows_elim h
      simpa [markDebt, specLe] using hcov

def assertVerdict (sigs : SigTable) (r : Ty) (rest : List Instr)
    (σ' : List Ty) (w : World) (a : VTy) : TCResult :=
  match a with
  | .isValue (.boolean Bool.true) => checkSeq sigs r { w with σ := σ' } rest
  | .isValue (.boolean Bool.false) | .anyValue .bool =>
      markDebt "assert obligation not discharged"
        (checkSeq sigs r { w with σ := σ' } rest)
  | _ => .reject .kAssert "assert: verdict is not boolean"

theorem assertVerdict_spec (sigs : SigTable) (r : Ty) (rest : List Instr)
    {w' w : World} {σr σc : List Ty}
    (h : specLe (checkSeq sigs r { w' with σ := σr } rest)
                (checkSeq sigs r { w with σ := σc } rest))
    {a' a : VTy} (hmv : tmovesV a' a = Bool.true) :
    specLe (assertVerdict sigs r rest σr w' a')
      (assertVerdict sigs r rest σc w a) := by
  cases a with
  | isValue v =>
      cases v with
      | boolean b => cases b <;> cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | number n => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | str st => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | listV l => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | compl ab vv => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | obj loc => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | descV d => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | undefined => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | null => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
  | anyValue c =>
      cases c with
      | bool =>
          cases a' with
          | isValue v => cases v <;> (first | (rename_i b; cases b) | skip) <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
          | _ => simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | undef => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | null => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | num => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | str => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | list => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | obj => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
      | desc => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
  | complN pp => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
  | complT => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
  | desc fs => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)
  | notPresent => cases a' <;> simp_all only [assertVerdict, tmovesV, tagOf, beq_iff_eq, decide_eq_true_eq] <;> try subst_vars <;> first | exact h | exact markDebt_specLe _ h | exact markDebt_specLe_left _ h | exact markDebt_specLe_right _ h | exact trivial | exact absurd hmv (by simp)

theorem testTypeP_bare (p : Prim) {T : Ty} (h : testTypeP p = some T) :
    ∀ b ∈ T, isBareVTy b = Bool.true := by
  cases p <;> simp only [testTypeP] at h
  all_goals
    cases h
    all_goals
      intro b hb
      first
      | exact anyOf_bare _ b hb
      | exact typeMask_bare _ b hb
      | (cases b <;> simp_all [isBareVTy])

theorem checkSeq_specialize (sigs : SigTable) (r : Ty) (w : World) (seq : List Instr) :
    ∀ (w' : World), worldLe w' w →
      specLe (checkSeq sigs r w' seq) (checkSeq sigs r w seq) := by
  induction sigs, r, w, seq using checkSeq.induct
  case case1 =>
    rename_i sigs r w
    intro w' h
    simp only [checkSeq]
    intro v hv
    simp only [List.mem_singleton] at hv
    subst hv
    exact ⟨w, List.mem_singleton.mpr rfl, h⟩
  case case2 =>
    rename_i sigs r w tail ts σ' hσ hle
    intro w' h
    obtain ⟨hΓ, hσle⟩ := h
    rw [hσ] at hσle
    cases hσ' : w'.σ with
    | nil => rw [hσ'] at hσle; cases hσle
    | cons t' σ'' =>
        rw [hσ'] at hσle
        obtain ⟨hslot, -⟩ := hσle
        have hle' : tmoves t' r = Bool.true := tmoves_trans hslot.1 hle
        simp [checkSeq, hσ, hσ', hle, hle', specLe]
  case case6 =>
    rename_i sigs r w t e rest ts σ' hσ ih2 ih1
    intro w' h
    obtain ⟨hΓ, hσle⟩ := h
    rw [hσ] at hσle
    cases hσ' : w'.σ with
    | nil => rw [hσ'] at hσle; cases hσle
    | cons t' σ'' =>
        rw [hσ'] at hσle
        obtain ⟨hslot, hσ''le⟩ := hσle
        have hbr : worldLe { w' with σ := σ'' } { w with σ := σ' } :=
          ⟨hΓ, hσ''le⟩
        have ht : specLe (checkSeq sigs r { w' with σ := σ'' } (t ++ rest))
            (checkSeq sigs r { w with σ := σ' } (t ++ rest)) := ih2 _ hbr
        have he : specLe (checkSeq sigs r { w' with σ := σ'' } (e ++ rest))
            (checkSeq sigs r { w with σ := σ' } (e ++ rest)) := ih1 _ hbr
        have hmate : ∀ b ∈ t', ∃ a ∈ ts, tmovesV b a = Bool.true :=
          tyLe_cov_atoms hslot.1
        cases hc : ts.foldl
            (fun acc a => mergeTC acc (iteVerdict sigs r t e rest σ' w a)) vacOk with
        | reject s why =>
            simp only [checkSeq, hσ, hσ']
            change specLe
              (t'.foldl (fun acc a =>
                mergeTC acc (iteVerdict sigs r t e rest σ'' w' a)) vacOk)
              (ts.foldl (fun acc a =>
                mergeTC acc (iteVerdict sigs r t e rest σ' w a)) vacOk)
            rw [hc]
            exact trivial
        | flows fr =>
            obtain ⟨fr', hfr', hcov⟩ :=
              fold_specLe_vac (J := fun a => iteVerdict sigs r t e rest σ' w a)
                (J' := fun a => iteVerdict sigs r t e rest σ'' w' a)
                (R := fun b a => tmovesV b a = Bool.true)
                ts t' fr hmate
                (fun b a hba => iteVerdict_spec ht he hba) hc
            simp only [checkSeq, hσ, hσ']
            change specLe
              (t'.foldl (fun acc a =>
                mergeTC acc (iteVerdict sigs r t e rest σ'' w' a)) vacOk)
              (ts.foldl (fun acc a =>
                mergeTC acc (iteVerdict sigs r t e rest σ' w a)) vacOk)
            rw [hfr', hc]
            exact hcov
  case case3 =>
    rename_i sigs r w tail ts σ' hσ hnt
    intro w' h
    simp only [checkSeq, hσ]
    rw [if_neg hnt]
    exact trivial
  case case4 =>
    rename_i sigs r w tail hσ
    intro w' h
    obtain ⟨hΓ, hσle⟩ := h
    rw [hσ] at hσle
    cases hσ' : w'.σ with
    | nil => simp only [checkSeq, hσ, hσ']; exact trivial
    | cons t' σ'' => rw [hσ'] at hσle; cases hσle
  case case5 =>
    rename_i sigs r w t e rest hσ
    intro w' h
    obtain ⟨hΓ, hσle⟩ := h
    rw [hσ] at hσle
    cases hσ' : w'.σ with
    | nil => simp only [checkSeq, hσ, hσ']; exact trivial
    | cons t' σ'' => rw [hσ'] at hσle; cases hσle
  case case7 =>
    rename_i sigs r w x rest hlook ih1
    intro w' h
    obtain ⟨hΓ, hσle⟩ := h
    have hlook' : tyLookup w'.Γ x = none := by
      have hex := hΓ.1 x
      rw [hlook] at hex
      cases hl : tyLookup w'.Γ x with
      | none => rfl
      | some S => rw [hl] at hex; simp at hex
    have hpush : worldLe { w' with σ := [.isValue (.boolean Bool.true)] :: w'.σ }
        { w with σ := [.isValue (.boolean Bool.true)] :: w.σ } :=
      ⟨hΓ, stackLe_cons_intro (slotLe_refl _) hσle⟩
    simp only [checkSeq, hlook, hlook']
    exact ih1 _ hpush
  case case8 =>
    rename_i sigs r w x rest S hlook ih1
    intro w' h
    have hΓ := h.1
    have hσle := h.2
    obtain ⟨S', hlook', -⟩ := envLe_lookup_cov_full hΓ hlook
    simp only [checkSeq, hlook, hlook']
    exact fork_specLe (fun v' hv' => split1_cov h hv')
      (fun hne => split1_ne_of_worldLe (T := [.notPresent])
        (by intro b hb; simp only [List.mem_singleton] at hb; subst hb; rfl) h hne)
      (fun u' u hu => ih1 u u' hu)
  case case9 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_5]
    exact ih1 w' h
  case case10 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_6]
    exact ih1 w' h
  case case11 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_7]
    exact ih1 w' h
  case case12 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_8]
    exact ih1 w' h
  case case13 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_9]
    exact ih1 w' h
  case case14 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_10]
    exact ih1 w' h
  case case15 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_11]
    exact ih1 w' h
  case case16 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_12]
    exact ih1 w' h
  case case17 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_13]
    exact ih1 w' h
  case case18 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_14]
    exact ih1 w' h
  case case19 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_15]
    exact ih1 w' h
  case case20 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_16]
    exact ih1 w' h
  case case21 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_17]
    exact ih1 w' h
  case case22 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_18]
    exact ih1 w' h
  case case23 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_19]
    exact ih1 w' h
  case case24 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_20]
    exact ih1 w' h
  case case25 =>
    rename_i sigs r w b f x rest hfused ih1
    intro w' h
    simp only [checkSeq.eq_21]
    simp only [if_pos hfused]
    exact ih1 w' h
  case case34 =>
    rename_i sigs r w x rest f b dec hdec ih1
    intro w' h
    simp only [checkSeq.eq_24, hdec]
    exact fork_specLe
      (fun v' hv' => splitP1_cov
        (decMono_map (fun bv => bv == b) (decMono_predDecide f dec hdec)) h hv')
      (fun hne => splitP1_ne_of_worldLe h hne) (fun u' u hu => ih1 u u' hu)
  case case35 =>
    rename_i sigs r w x rest f b hdec hlook
    intro w' h
    obtain ⟨hΓ, -⟩ := h
    have hlook' : tyLookup w'.Γ x = none := by
      have hex := hΓ.1 x
      rw [hlook] at hex
      cases hl : tyLookup w'.Γ x with
      | none => rfl
      | some S => rw [hl] at hex; simp at hex
    simp only [checkSeq.eq_24, hdec, hlook, hlook']
    exact trivial
  case case36 =>
    rename_i sigs r w x rest f b hdec S hlook ih1
    intro w' h
    obtain ⟨hΓ, hσle⟩ := h
    obtain ⟨S', hlook', -⟩ := envLe_lookup_cov_full hΓ hlook
    have hpush : worldLe { w' with σ := [.anyValue .bool] :: w'.σ }
        { w with σ := [.anyValue .bool] :: w.σ } :=
      ⟨hΓ, stackLe_cons_intro (slotLe_refl _) hσle⟩
    simp only [checkSeq.eq_24, hdec, hlook, hlook']
    exact ih1 _ hpush
  case case37 =>
    rename_i sigs r w x rest dec hdec ih1
    intro w' h
    simp only [checkSeq.eq_25, hdec]
    exact fork_specLe (fun v' hv' => splitP1_cov (decMono_primDecide _ _ hdec) h hv')
      (fun hne => splitP1_ne_of_worldLe h hne) (fun u' u hu => ih1 u u' hu)
  case case38 =>
    rename_i sigs r w x rest hdec hlook
    intro w' h
    exact absurd hlook (by simp [primDecide])
  case case39 =>
    rename_i sigs r w x rest hdec S hlook ih1
    intro w' h
    exact absurd hlook (by simp [primDecide])
  case case40 =>
    rename_i sigs r w x rest dec hdec ih1
    intro w' h
    simp only [checkSeq.eq_26, hdec]
    exact fork_specLe (fun v' hv' => splitP1_cov (decMono_primDecide _ _ hdec) h hv')
      (fun hne => splitP1_ne_of_worldLe h hne) (fun u' u hu => ih1 u u' hu)
  case case41 =>
    rename_i sigs r w x rest hdec hlook
    intro w' h
    exact absurd hlook (by simp [primDecide])
  case case42 =>
    rename_i sigs r w x rest hdec S hlook ih1
    intro w' h
    exact absurd hlook (by simp [primDecide])
  case case43 =>
    rename_i sigs r w x p rest ps hT hpred hn hc ih1
    intro w' h
    have hbare := testTypeP_bare p hT
    simp only [checkSeq, hpred, hn, hc, hT]
    exact fork_specLe (fun v' hv' => split1_cov h hv')
      (fun hne => split1_ne_of_worldLe hbare h hne)
      (fun u' u hu => ih1 u u' hu)
  case case44 =>
    rename_i sigs r w x p rest hT hlook hpred hn hc
    intro w' h
    obtain ⟨hΓ, -⟩ := h
    have hlook' : tyLookup w'.Γ x = none := by
      have hex := hΓ.1 x
      rw [hlook] at hex
      cases hl : tyLookup w'.Γ x with
      | none => rfl
      | some S => rw [hl] at hex; simp at hex
    simp only [checkSeq, hpred, hn, hc, hT, hlook, hlook']
    exact trivial
  case case45 =>
    rename_i sigs r w x p rest hT S hlook hpred hn hc ih1
    intro w' h
    obtain ⟨hΓ, hσle⟩ := h
    obtain ⟨S', hlook', -⟩ := envLe_lookup_cov_full hΓ hlook
    have hpush : worldLe { w' with σ := [.anyValue .bool] :: w'.σ }
        { w with σ := [.anyValue .bool] :: w.σ } :=
      ⟨hΓ, stackLe_cons_intro (slotLe_refl _) hσle⟩
    simp only [checkSeq, hpred, hn, hc, hT, hlook, hlook']
    exact ih1 _ hpush
  case case54 =>
    rename_i sigs r w rest hσ
    intro w' h
    obtain ⟨hΓ, hσle⟩ := h
    rw [hσ] at hσle
    cases hσ' : w'.σ with
    | nil => simp only [checkSeq, hσ, hσ']; exact trivial
    | cons t' σ'' => rw [hσ'] at hσle; cases hσle
  case case55 =>
    rename_i sigs r w rest ts σ' hσ ih1
    intro w' h
    obtain ⟨hΓ, hσle⟩ := h
    rw [hσ] at hσle
    cases hσ' : w'.σ with
    | nil => rw [hσ'] at hσle; cases hσle
    | cons t' σ'' =>
        rw [hσ'] at hσle
        obtain ⟨hslot, hσ''le⟩ := hσle
        have hbr : worldLe { w' with σ := σ'' } { w with σ := σ' } :=
          ⟨hΓ, hσ''le⟩
        have hpt : specLe (checkSeq sigs r { w' with σ := σ'' } rest)
            (checkSeq sigs r { w with σ := σ' } rest) := ih1 _ hbr
        have hmate : ∀ b ∈ t', ∃ a ∈ ts, tmovesV b a = Bool.true :=
          tyLe_cov_atoms hslot.1
        cases hc : ts.foldl
            (fun acc a => mergeTC acc (assertVerdict sigs r rest σ' w a)) vacOk with
        | reject s why =>
            simp only [checkSeq, hσ, hσ']
            change specLe
              (t'.foldl (fun acc a =>
                mergeTC acc (assertVerdict sigs r rest σ'' w' a)) vacOk)
              (ts.foldl (fun acc a =>
                mergeTC acc (assertVerdict sigs r rest σ' w a)) vacOk)
            rw [hc]
            exact trivial
        | flows fr =>
            obtain ⟨fr', hfr', hcov⟩ :=
              fold_specLe_vac (J := fun a => assertVerdict sigs r rest σ' w a)
                (J' := fun a => assertVerdict sigs r rest σ'' w' a)
                (R := fun b a => tmovesV b a = Bool.true)
                ts t' fr hmate
                (fun b a hba => assertVerdict_spec sigs r rest hpt hba) hc
            simp only [checkSeq, hσ, hσ']
            change specLe
              (t'.foldl (fun acc a =>
                mergeTC acc (assertVerdict sigs r rest σ'' w' a)) vacOk)
              (ts.foldl (fun acc a =>
                mergeTC acc (assertVerdict sigs r rest σ' w a)) vacOk)
            rw [hfr', hc]
            exact hcov
  all_goals sorry