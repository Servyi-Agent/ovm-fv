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

def slotClosed (p : Ty) : Prop :=
  ∀ {t' t : Ty}, slotLe t' t → tmoves t' p = Bool.true → tmoves t p = Bool.true

theorem leTy_up_closed {ts' ts ps : List Ty} (hslots : slotsLe ts' ts)
    (hps : ∀ p ∈ ps, slotClosed p) (hle : leTy ts' ps = Bool.true) :
    leTy ts ps = Bool.true := by
  revert ps
  induction ts' generalizing ts with
  | nil =>
      intro ps hps hle
      cases ts with
      | nil => cases ps <;> simp [leTy] at hle ⊢
      | cons t ts => cases hslots
  | cons t' ts' ih =>
      intro ps hps hle
      cases ts with
      | nil => cases hslots
      | cons t ts =>
          obtain ⟨hslot, hslots'⟩ := hslots
          cases ps with
          | nil => simp [leTy] at hle
          | cons p ps =>
              simp only [leTy] at hle ⊢
              obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _) |>.mp hle
              have h1' : tmoves t p = Bool.true := hps p (by simp) hslot h1
              have h2' : leTy ts ps = Bool.true :=
                ih hslots' (fun q hq => hps q (by simp [hq])) h2
              exact (Bool.and_eq_true _ _) |>.mpr ⟨h1', h2'⟩

def sigParamsClosed (sigs : SigTable) : Prop :=
  ∀ n ps ret, sigFind sigs n = some (ps, ret) → ∀ p ∈ ps, slotClosed p

theorem markThrow_specLe (sigs : SigTable) (ex : Expr) {r' r : TCResult}
    (h : specLe r' r) : specLe (markThrow sigs ex r') (markThrow sigs ex r) := by
  cases r with
  | reject s w => exact trivial
  | flows f =>
      obtain ⟨f', rfl, hcov⟩ := specLe_flows_elim h
      simpa [markThrow, specLe] using hcov

theorem mem_dropLast_subset {α : Type} : ∀ (l : List α) {a : α}, a ∈ l.dropLast → a ∈ l
  | [], a, h => by simp at h
  | [_], a, h => by simp at h
  | x :: y :: ys, a, h => by
      simp only [List.dropLast_cons_cons] at h
      simp only [List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by simpa [List.mem_cons] using mem_dropLast_subset (y :: ys) h)

theorem popTy_some_nil_cov {T t' t : Ty} {σ' σ : List Ty}
    (hslot : slotLe t' t) (hrest : stackLe σ' σ)
    (hp : popTy T (t :: σ) = some []) :
    ∃ hnil : σ' = [], popTy T (t' :: σ') = some [] := by
  have hp0 := popTy_cov hslot hrest hp
  have hσnil : σ = [] := by
    simp only [popTy] at hp
    by_cases htm : tmoves t T = Bool.true
    · rw [if_pos htm] at hp
      injection hp with h
    · rw [if_neg htm] at hp
      cases hp
  subst σ
  have hσ'nil : σ' = [] := by
    cases σ' with
    | nil => rfl
    | cons u us => simp [stackLe] at hrest
  exact ⟨hσ'nil, by simpa [hσ'nil] using hp0⟩

theorem tmoves_class_down {t' t : Ty} {c : Ctor} (hslot : slotLe t' t)
    (hm : tmoves t [.anyValue c] = Bool.true) :
    tmoves t' [.anyValue c] = Bool.true := by
  unfold slotLe at hslot
  unfold tmoves at hm ⊢
  have hcov : tmoves t' t = Bool.true := hslot.1
  unfold tmoves at hcov
  simp only [List.all_eq_true] at hm ⊢ hcov
  intro a' ha'
  obtain ⟨a, ha, ha'a⟩ := List.any_eq_true.mp (hcov a' ha')
  obtain ⟨b, hb, hab⟩ := List.any_eq_true.mp (hm a ha)
  simp only [List.mem_singleton] at hb
  subst b
  exact List.any_eq_true.mpr ⟨VTy.anyValue c, by simp, tmovesV_trans ha'a hab⟩

theorem fold_worlds_specLe (sigs : SigTable) (r : Ty) (rest : List Instr)
    (hstep : ∀ u v : World, worldLe u v →
      specLe (checkSeq sigs r u rest) (checkSeq sigs r v rest)) :
    ∀ fs' fs : List World,
      (∀ u ∈ fs', ∃ v ∈ fs, worldLe u v) →
      specLe
        (fs'.foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows)
        (fs.foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows) := by
  intro fs' fs hcov
  cases hf : fs.foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows with
  | reject s why => exact trivial
  | flows fr =>
      obtain ⟨fr', hfr', hfrcov⟩ := fold_specLe fs fs' fr hcov hstep hf
      cases hf' : fs'.foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows with
      | reject s why =>
          rw [hf'] at hfr'
          cases hfr'
      | flows fr0 =>
          have hfr0 : fr0 = fr' := by
            injection (hf'.symm.trans hfr') with heq
          cases hfr0
          exact hfrcov

theorem checkSeq_specialize (sigs : SigTable) (r : Ty) (w : World) (seq : List Instr)
    (hsc : sigParamsClosed sigs) :
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
    have hworld : worldLe w' w := ⟨hΓ, hσle⟩
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
    have hworld : worldLe w' w := ⟨hΓ, hσle⟩
    rw [hσ] at hσle
    cases hσ' : w'.σ with
    | nil => rw [hσ'] at hσle; cases hσle
    | cons t' σ'' =>
        rw [hσ'] at hσle
        obtain ⟨hslot, hσ''le⟩ := hσle
        have hbr : worldLe { w' with σ := σ'' } { w with σ := σ' } :=
          ⟨hΓ, hσ''le⟩
        have ht : specLe (checkSeq sigs r { w' with σ := σ'' } (t ++ rest))
            (checkSeq sigs r { w with σ := σ' } (t ++ rest)) := ih2 hsc _ hbr
        have he : specLe (checkSeq sigs r { w' with σ := σ'' } (e ++ rest))
            (checkSeq sigs r { w with σ := σ' } (e ++ rest)) := ih1 hsc _ hbr
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
    have hworld : worldLe w' w := ⟨hΓ, hσle⟩
    rw [hσ] at hσle
    cases hσ' : w'.σ with
    | nil => simp only [checkSeq, hσ, hσ']; exact trivial
    | cons t' σ'' => rw [hσ'] at hσle; cases hσle
  case case5 =>
    rename_i sigs r w t e rest hσ
    intro w' h
    obtain ⟨hΓ, hσle⟩ := h
    have hworld : worldLe w' w := ⟨hΓ, hσle⟩
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
    exact ih1 hsc _ hpush
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
      (fun u' u hu => ih1 u hsc u' hu)
  case case9 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_5]
    exact ih1 hsc w' h
  case case10 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_6]
    exact ih1 hsc w' h
  case case11 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_7]
    exact ih1 hsc w' h
  case case12 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_8]
    exact ih1 hsc w' h
  case case13 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_9]
    exact ih1 hsc w' h
  case case14 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_10]
    exact ih1 hsc w' h
  case case15 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_11]
    exact ih1 hsc w' h
  case case16 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_12]
    exact ih1 hsc w' h
  case case17 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_13]
    exact ih1 hsc w' h
  case case18 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_14]
    exact ih1 hsc w' h
  case case19 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_15]
    exact ih1 hsc w' h
  case case20 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_16]
    exact ih1 hsc w' h
  case case21 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_17]
    exact ih1 hsc w' h
  case case22 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_18]
    exact ih1 hsc w' h
  case case23 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_19]
    exact ih1 hsc w' h
  case case24 =>
    rename_i sigs r w x rest ih1
    intro w' h
    simp only [checkSeq.eq_20]
    exact ih1 hsc w' h
  case case25 =>
    rename_i sigs r w b f x rest hfused ih1
    intro w' h
    simp only [checkSeq.eq_21]
    simp only [if_pos hfused]
    exact ih1 hsc w' h
  case case26 =>
    rename_i sigs r w b f x rest hf hnone
    intro w' h
    obtain ⟨hΓ, -⟩ := h
    cases hreff : typeOfE sigs w'.Γ
        (.isBoolVal b (.call f [.nv x])) with
    | none =>
        simp only [checkSeq.eq_21, if_neg hf, hnone, hreff]
        exact trivial
    | some t' =>
        exfalso
        cases hcall' : typeOfE sigs w'.Γ (.call f [.nv x]) with
        | none => simp [typeOfE, hcall'] at hreff
        | some tc' =>
            cases hl' : tyLookup w'.Γ x with
            | none =>
                have hn : typeOfE sigs w'.Γ (.call f [.nv x]) = none := by
                  cases hsf : sigFind sigs f <;> simp [typeOfE, typesOf, hl', hsf]
                rw [hn] at hcall'
                cases hcall'
            | some tl' =>
                have hpres := hΓ.1 x
                rw [hl'] at hpres
                cases hl : tyLookup w.Γ x with
                | none => simp [hl] at hpres
                | some tl =>
                    have hslot : slotLe tl' tl := by
                      refine ⟨?_, ?_⟩
                      · obtain ⟨u, hu, hule⟩ := hΓ.2.1 x tl' (by simp [hl'])
                        rw [hl] at hu
                        have htu : tl = u := by simpa using hu
                        subst u
                        exact hule
                      · intro hne hnil
                        obtain ⟨u, hu, hune, _⟩ := hΓ.2.2 x tl (by simp [hl]) hne
                        have hutl : u = tl' := by
                          rw [hl'] at hu
                          simpa using hu.symm
                        exact hune (by rw [hutl, hnil])
                    have hslots : slotsLe [tl'] [tl] := ⟨hslot, True.intro⟩
                    cases hsig : sigFind sigs f with
                    | none => simp [typeOfE, hsig] at hcall'
                    | some pair =>
                        obtain ⟨ps, retj⟩ := pair
                        simp only [typeOfE, hsig, typesOf, hl'] at hcall'
                        have hg' : (leTy [tl'] ps ||
                            [Expr.nv x].length == ps.length - 1 &&
                              leTy [tl'] ps.dropLast) = Bool.true := by
                          cases hg : (leTy [tl'] ps ||
                            [Expr.nv x].length == ps.length - 1 &&
                              leTy [tl'] ps.dropLast) with
                          | false =>
                              have hng : ¬(leTy [tl'] ps ||
                                  [Expr.nv x].length == ps.length - 1 &&
                                    leTy [tl'] ps.dropLast) = Bool.true := by
                                intro htrue
                                rw [hg] at htrue
                                cases htrue
                              rw [if_neg hng] at hcall'
                              cases hcall'
                          | true => rfl
                        have hgc : (leTy [tl] ps ||
                            ([Expr.nv x].length == ps.length - 1 &&
                              leTy [tl] ps.dropLast)) = Bool.true := by
                          rw [Bool.or_eq_true] at hg'
                          cases hg' with
                          | inl hA =>
                              have hA' : leTy [tl] ps = Bool.true :=
                                leTy_up_closed hslots
                                  (fun p hp => hsc f ps retj hsig p hp) hA
                              simp [hA']
                          | inr hB =>
                              obtain ⟨hlen, hdl⟩ := (Bool.and_eq_true _ _) |>.mp hB
                              have hdl' : leTy [tl] ps.dropLast = Bool.true :=
                                leTy_up_closed hslots
                                  (fun p hp => hsc f ps retj hsig p
                                    (mem_dropLast_subset ps hp)) hdl
                              rw [Bool.or_eq_true]
                              exact Or.inr (by
                                rw [Bool.and_eq_true]
                                exact ⟨hlen, hdl'⟩)
                        have hcoarse : typeOfE sigs w.Γ (.call f [.nv x]) =
                            some (complPayload retj) := by
                          simp only [typeOfE, hsig, typesOf, hl]
                          rw [if_pos hgc]
                        have hcoarseTop : typeOfE sigs w.Γ
                            (.isBoolVal b (.call f [.nv x])) =
                            some [.anyValue .bool] := by
                          simp [typeOfE, hcoarse]
                        rw [hcoarseTop] at hnone
                        cases hnone
  case case27 =>
    rename_i sigs r w b f x rest hf S hsome ih1
    intro w' h
    obtain ⟨hΓ, hσle⟩ := h
    obtain ⟨S', hsome', hslot⟩ := typeOfE_cov sigs w'.Γ w.Γ
      (.isBoolVal b (.call f [.nv x])) hΓ S hsome
    have hpush : worldLe { w' with σ := S' :: w'.σ }
        { w with σ := S :: w.σ } :=
      ⟨hΓ, stackLe_cons_intro hslot hσle⟩
    have hpt : specLe (checkSeq sigs r { w' with σ := S' :: w'.σ } rest)
        (checkSeq sigs r { w with σ := S :: w.σ } rest) := ih1 hsc _ hpush
    simp only [checkSeq.eq_21]
    simp only [if_neg hf]
    simp only [hsome, hsome']
    exact markThrow_specLe sigs _ hpt
  case case34 =>
    rename_i sigs r w x rest f b dec hdec ih1
    intro w' h
    simp only [checkSeq.eq_24, hdec]
    exact fork_specLe
      (fun v' hv' => splitP1_cov
        (decMono_map (fun bv => bv == b) (decMono_predDecide f dec hdec)) h hv')
      (fun hne => splitP1_ne_of_worldLe h hne) (fun u' u hu => ih1 u hsc u' hu)
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
    exact ih1 hsc _ hpush
  case case37 =>
    rename_i sigs r w x rest dec hdec ih1
    intro w' h
    simp only [checkSeq.eq_25, hdec]
    exact fork_specLe (fun v' hv' => splitP1_cov (decMono_primDecide _ _ hdec) h hv')
      (fun hne => splitP1_ne_of_worldLe h hne) (fun u' u hu => ih1 u hsc u' hu)
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
      (fun hne => splitP1_ne_of_worldLe h hne) (fun u' u hu => ih1 u hsc u' hu)
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
      (fun u' u hu => ih1 u hsc u' hu)
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
    exact ih1 hsc _ hpush
  case case54 =>
    rename_i sigs r w rest hσ
    intro w' h
    obtain ⟨hΓ, hσle⟩ := h
    have hworld : worldLe w' w := ⟨hΓ, hσle⟩
    rw [hσ] at hσle
    cases hσ' : w'.σ with
    | nil => simp only [checkSeq, hσ, hσ']; exact trivial
    | cons t' σ'' => rw [hσ'] at hσle; cases hσle
  case case55 =>
    rename_i sigs r w rest ts σ' hσ ih1
    intro w' h
    obtain ⟨hΓ, hσle⟩ := h
    have hworld : worldLe w' w := ⟨hΓ, hσle⟩
    rw [hσ] at hσle
    cases hσ' : w'.σ with
    | nil => rw [hσ'] at hσle; cases hσle
    | cons t' σ'' =>
        rw [hσ'] at hσle
        obtain ⟨hslot, hσ''le⟩ := hσle
        have hbr : worldLe { w' with σ := σ'' } { w with σ := σ' } :=
          ⟨hΓ, hσ''le⟩
        have hpt : specLe (checkSeq sigs r { w' with σ := σ'' } rest)
            (checkSeq sigs r { w with σ := σ' } rest) := ih1 hsc _ hbr
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
  case case28 =>
    rename_i sigs r w c body rest hσ ps hsome hbool ih2 ih1
    intro w' h
    obtain ⟨hΓ, hσle⟩ := h
    have hworld : worldLe w' w := ⟨hΓ, hσle⟩
    rw [hσ] at hσle
    cases hσ' : w'.σ with
    | nil =>
        obtain ⟨ps', hsome', hslot⟩ :=
          typeOfE_cov sigs w'.Γ w.Γ c hΓ ps hsome
        have hbool' : tmoves ps' [.anyValue .bool] = Bool.true :=
          tmoves_class_down hslot hbool
        have hbody : specLe (checkSeq sigs r w' body) (checkSeq sigs r w body) :=
          ih2 hsc w' hworld
        have hk := fold_worlds_specLe sigs r rest
          (fun u v huv => ih1 v hsc u huv)
        simp only [checkSeq, hσ, hσ', hsome, hsome', if_pos hbool, if_pos hbool']
        exact checkLoopBody_spec (.kRepeatWhile c body) []
          (fun fs => fs.foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows)
          hbody hk
    | cons t σ'' =>
        rw [hσ'] at hσle
        cases hσle
  case case29 =>
    intro w' h
    simp [checkSeq, specLe, *]
  case case30 =>
    intro w' h
    simp [checkSeq, specLe, *]
  case case31 =>
    rename_i sigs r w c body rest hσne
    intro w' h
    obtain ⟨hΓ, hσle⟩ := h
    cases hσ' : w'.σ with
    | nil =>
        cases hstack : w.σ with
        | nil => exact absurd hstack hσne
        | cons t σ =>
            exfalso
            simpa [hσ', hstack, stackLe] using hσle
    | cons t' σ'' =>
        cases hstack : w.σ with
        | nil =>
            exfalso
            simpa [hσ', hstack, stackLe] using hσle
        | cons t σ =>
            simp only [checkSeq, hσ', hstack]
            exact trivial
  case case32 =>
    intro w' h
    simp [checkSeq, specLe, *]
  case case33 =>
    rename_i sigs r w ex rest n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 S hsome ih1
    intro w' h
    obtain ⟨hΓ, hσle⟩ := h
    obtain ⟨S', hsome', hslot⟩ :=
      typeOfE_cov sigs w'.Γ w.Γ ex hΓ S hsome
    have hpush : worldLe { w' with σ := S' :: w'.σ }
        { w with σ := S :: w.σ } :=
      ⟨hΓ, stackLe_cons_intro hslot hσle⟩
    simp only [checkSeq, hsome, hsome']
    exact markThrow_specLe sigs ex (ih1 hsc _ hpush)
  case case46 =>
    intro w' h
    simp [checkSeq, specLe, *]
  case case47 =>
    rename_i sigs r w c body rest hpop ih2 ih1
    intro w' h
    obtain ⟨hΓ, hσle⟩ := h
    cases hσ : w.σ with
    | nil => simp [hσ, popTy] at hpop
    | cons t σ =>
        cases hσ' : w'.σ with
        | nil =>
            exfalso
            simpa [hσ, hσ', stackLe] using hσle
        | cons t' σ' =>
            rw [hσ] at hpop
            rw [hσ, hσ'] at hσle
            obtain ⟨hslot, hrest⟩ := hσle
            obtain ⟨hnil, hpop'⟩ := popTy_some_nil_cov hslot hrest hpop
            subst σ'
            have hw0 : worldLe { w' with σ := [] } { w with σ := [] } :=
              ⟨hΓ, by simp [stackLe]⟩
            have hbody := ih2 hsc ({ w' with σ := [] }) hw0
            have hk := fold_worlds_specLe sigs r rest
              (fun u v huv => ih1 v hsc u huv)
            simp only [checkSeq, hσ, hσ', hpop, hpop']
            exact checkLoopBody_spec (.kRepeatTest c body) []
              (fun fs => fs.foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows)
              hbody hk
  case case48 =>
    intro w' h
    simp [checkSeq, specLe, *]
  case case49 =>
    intro w' h
    simp [checkSeq, specLe, *]
  case case50 =>
    rename_i sigs r w x body rest hpop ih2 ih1
    intro w' h
    obtain ⟨hΓ, hσle⟩ := h
    cases hσ : w.σ with
    | nil => simp [hσ, popA, popTy] at hpop
    | cons t σ =>
        cases hσ' : w'.σ with
        | nil =>
            exfalso
            simpa [hσ, hσ', stackLe] using hσle
        | cons t' σ' =>
            rw [hσ] at hpop
            rw [hσ, hσ'] at hσle
            obtain ⟨hslot, hrest⟩ := hσle
            have hp : popTy [.anyValue .list] (t :: σ) = some [] := by
              simpa [popA] using hpop
            obtain ⟨hnil, hpop'⟩ := popTy_some_nil_cov hslot hrest hp
            have hpopA' : popA (.anyValue .list) (t' :: σ') = some [] := by
              simpa [popA] using hpop'
            subst σ'
            have hw0 : worldLe
                { Γ := (x, langT) :: w'.Γ, σ := [] }
                { Γ := (x, langT) :: w.Γ, σ := [] } :=
              ⟨envLe_cons hΓ (slotLe_refl _), by simp [stackLe]⟩
            have hbody := ih2 hsc _ hw0
            have hk := fold_worlds_specLe sigs r rest
              (fun u v huv => ih1 v hsc u huv)
            simp only [checkSeq, hσ, hσ', hpop, hpopA']
            exact checkLoopBody_spec (.kForStart x body) []
              (fun fs => fs.foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows)
              hbody hk
  case case51 =>
    intro w' h
    simp [checkSeq, specLe, *]
  case case52 =>
    rename_i sigs r w x elems body rest hσ ih2 ih1
    intro w' h
    obtain ⟨hΓ, hσle⟩ := h
    cases hσ' : w'.σ with
    | nil =>
        have hw0 : worldLe
            { Γ := (x, langT) :: w'.Γ, σ := [] }
            { Γ := (x, langT) :: w.Γ, σ := w.σ } :=
          ⟨envLe_cons hΓ (slotLe_refl _), by simp [hσ, stackLe]⟩
        have hbody := ih2 hsc _ hw0
        have hbody' : specLe
            (checkSeq sigs r { Γ := (x, langT) :: w'.Γ, σ := [] } body)
            (checkSeq sigs r { Γ := (x, langT) :: w.Γ, σ := [] } body) := by
          simpa [hσ] using hbody
        have hk := fold_worlds_specLe sigs r rest
          (fun u v huv => ih1 v hsc u huv)
        simp only [checkSeq, hσ, hσ']
        exact checkLoopBody_spec (.kForBody x [] body) []
          (fun fs => fs.foldl (fun acc u => mergeTC acc (checkSeq sigs r u rest)) noFlows)
          hbody' hk
    | cons t' σ'' =>
        exfalso
        simpa [hσ, hσ', stackLe] using hσle
  case case53 =>
    rename_i sigs r w x elems body rest hσne
    intro w' h
    obtain ⟨hΓ, hσle⟩ := h
    cases hσ' : w'.σ with
    | nil =>
        cases hstack : w.σ with
        | nil => exact absurd hstack hσne
        | cons t σ =>
            exfalso
            simpa [hσ', hstack, stackLe] using hσle
    | cons t' σ'' =>
        cases hstack : w.σ with
        | nil =>
            exfalso
            simpa [hσ', hstack, stackLe] using hσle
        | cons t σ =>
            simp only [checkSeq, hσ', hstack]
            exact trivial
  case case56 =>
    intro w' h
    simp [checkSeq, specLe, *]
  case case57 =>
    rename_i sigs r w i rest n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 n23 n24 n25 n26 n27 ws hstep ih1
    intro w' h
    obtain ⟨ws', hstep', hcov⟩ := step1_cov sigs i w' w h ws hstep
    have hne : ws ≠ [] → ws' ≠ [] := by
      intro _ 
      exact step1_some_ne sigs i w' ws' hstep'
    have hpoint : ∀ u' u, worldLe u' u →
        specLe (checkSeq sigs r u' rest) (checkSeq sigs r u rest) :=
      fun u' u hu => ih1 u hsc u' hu
    simp only [checkSeq, hstep, hstep']
    exact fork_specLe hcov hne hpoint