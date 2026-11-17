import Metalanguage.SubjectReduction

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
  all_goals sorry