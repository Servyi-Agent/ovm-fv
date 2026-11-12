/- # Grammar core: ASTs, label elaboration, numbering audit, and
   compilation to Instr instruction lists. No surface syntax (that is
   Syntax.lean), no evaluation. -/

/- # ovm-fv metalanguage

   The ECMA-262 emu-alg metalanguage: surface grammar (`┊` depth
   markers, spec numbering), label-carrying elaboration, audits
   (numbering consecutiveness), SOS and kEval small-step semantics
   (frames for control boundaries), and the operation-registry
   protocol. Spec transcriptions live under spec/<clause>/spec.lean
   and are assembled into a registry by tools/build_corpus.py. -/

/- Numbered-step grammar with exact ECMA-262 tokens AND explicit
depth markers ┊ (one per level below the top):

  1: …          depth 1 (no marker)
  ┊a: …        depth 2
  ┊┊i: …       depth 3
  ┊┊┊1: …      depth 4 (numbers restart — no collision)
  ┊┊┊┊a: …     depth 5

A block at depth n is a maximal run of steps carrying exactly n-1
markers; it ends when a step with fewer markers appears. Since the
restarted depth-4 numbers are `┊┊┊1:` vs top-level `1:` —
different tokens — the greedy swallow of the marker-free design is
structurally impossible. Numbering becomes decoration: identifiers
serve as roman labels (no keyword shadowing), and the consecutiveness
audit remains purely as a typo check. -/

/- ===== Objects ===== -/

/- Property Descriptor — verbatim six optional fields (ES 6.2.6.1). -/
mutual
inductive Descriptor where
  | mk (value : Option JSValue) (writable : Option Bool)
      (getter : Option Nat) (setter : Option Nat)
      (enumerable : Option Bool) (configurable : Option Bool)
  deriving Repr
inductive JSValue where
  | undefined | null | boolean (b : Bool) | number (n : Int)
  | str (s : «String»)
  | listV (l : List JSValue)     -- spec List, injected for the AO layer
  | compl (abrupt : Bool) (v : JSValue)  -- Completion Record, as a value
  | obj (loc : Nat)                     -- object reference
  | descV (d : Descriptor)              -- Property Descriptor, as a value
  deriving Repr
end

/- ## Lawful structural equality.

    Lean cannot derive BEq laws for nested/mutual inductives, and the
    previous Float-based numbers were not even lawfully EQUAL (IEEE
    0.0 == -0.0). Numbers are Int (the model has no numeric ops yet),
    and equality is a fuel-structural mutual function with EXPLICIT
    constructor arms (match catch-alls do not reduce definitionally
    under brecOn with open fuel, so guarded equations are unusable in
    proofs). Depth alignment: dpt counts each descent level so that
    dpt k a + 1 <= k is exactly the invariant jeqF's reflexive
    unfolding needs. -/

/- ## Fuel-structural equality: every constructor pair is an explicit
     arm (guarded catch-all equations do not reduce definitionally
     under brecOn with open fuel). -/
mutual
def jeqF : Nat → JSValue → JSValue → Bool
  | 0, _, _ => Bool.false
  | k + 1, .undefined, .undefined => Bool.true
  | k + 1, .null, .null => Bool.true
  | k + 1, .boolean x₁, .boolean x₂ => x₁ == x₂
  | k + 1, .number x₁, .number x₂ => x₁ == x₂
  | k + 1, .str x₁, .str x₂ => x₁ == x₂
  | k + 1, .obj x₁, .obj x₂ => x₁ == x₂
  | k + 1, .compl a₁ v₁, .compl a₂ v₂ => (a₁ == a₂) && jeqF k v₁ v₂
  | k + 1, .listV xs₁, .listV xs₂ => jeqLF k xs₁ xs₂
  | k + 1, .descV d₁, .descV d₂ => deqF k d₁ d₂
  | k + 1, .undefined, .null => Bool.false
  | k + 1, .undefined, .boolean _ => Bool.false
  | k + 1, .undefined, .number _ => Bool.false
  | k + 1, .undefined, .str _ => Bool.false
  | k + 1, .undefined, .obj _ => Bool.false
  | k + 1, .undefined, .compl _ _ => Bool.false
  | k + 1, .undefined, .listV _ => Bool.false
  | k + 1, .undefined, .descV _ => Bool.false
  | k + 1, .null, .undefined => Bool.false
  | k + 1, .null, .boolean _ => Bool.false
  | k + 1, .null, .number _ => Bool.false
  | k + 1, .null, .str _ => Bool.false
  | k + 1, .null, .obj _ => Bool.false
  | k + 1, .null, .compl _ _ => Bool.false
  | k + 1, .null, .listV _ => Bool.false
  | k + 1, .null, .descV _ => Bool.false
  | k + 1, .boolean _, .undefined => Bool.false
  | k + 1, .boolean _, .null => Bool.false
  | k + 1, .boolean _, .number _ => Bool.false
  | k + 1, .boolean _, .str _ => Bool.false
  | k + 1, .boolean _, .obj _ => Bool.false
  | k + 1, .boolean _, .compl _ _ => Bool.false
  | k + 1, .boolean _, .listV _ => Bool.false
  | k + 1, .boolean _, .descV _ => Bool.false
  | k + 1, .number _, .undefined => Bool.false
  | k + 1, .number _, .null => Bool.false
  | k + 1, .number _, .boolean _ => Bool.false
  | k + 1, .number _, .str _ => Bool.false
  | k + 1, .number _, .obj _ => Bool.false
  | k + 1, .number _, .compl _ _ => Bool.false
  | k + 1, .number _, .listV _ => Bool.false
  | k + 1, .number _, .descV _ => Bool.false
  | k + 1, .str _, .undefined => Bool.false
  | k + 1, .str _, .null => Bool.false
  | k + 1, .str _, .boolean _ => Bool.false
  | k + 1, .str _, .number _ => Bool.false
  | k + 1, .str _, .obj _ => Bool.false
  | k + 1, .str _, .compl _ _ => Bool.false
  | k + 1, .str _, .listV _ => Bool.false
  | k + 1, .str _, .descV _ => Bool.false
  | k + 1, .obj _, .undefined => Bool.false
  | k + 1, .obj _, .null => Bool.false
  | k + 1, .obj _, .boolean _ => Bool.false
  | k + 1, .obj _, .number _ => Bool.false
  | k + 1, .obj _, .str _ => Bool.false
  | k + 1, .obj _, .compl _ _ => Bool.false
  | k + 1, .obj _, .listV _ => Bool.false
  | k + 1, .obj _, .descV _ => Bool.false
  | k + 1, .compl _ _, .undefined => Bool.false
  | k + 1, .compl _ _, .null => Bool.false
  | k + 1, .compl _ _, .boolean _ => Bool.false
  | k + 1, .compl _ _, .number _ => Bool.false
  | k + 1, .compl _ _, .str _ => Bool.false
  | k + 1, .compl _ _, .obj _ => Bool.false
  | k + 1, .compl _ _, .listV _ => Bool.false
  | k + 1, .compl _ _, .descV _ => Bool.false
  | k + 1, .listV _, .undefined => Bool.false
  | k + 1, .listV _, .null => Bool.false
  | k + 1, .listV _, .boolean _ => Bool.false
  | k + 1, .listV _, .number _ => Bool.false
  | k + 1, .listV _, .str _ => Bool.false
  | k + 1, .listV _, .obj _ => Bool.false
  | k + 1, .listV _, .compl _ _ => Bool.false
  | k + 1, .listV _, .descV _ => Bool.false
  | k + 1, .descV _, .undefined => Bool.false
  | k + 1, .descV _, .null => Bool.false
  | k + 1, .descV _, .boolean _ => Bool.false
  | k + 1, .descV _, .number _ => Bool.false
  | k + 1, .descV _, .str _ => Bool.false
  | k + 1, .descV _, .obj _ => Bool.false
  | k + 1, .descV _, .compl _ _ => Bool.false
  | k + 1, .descV _, .listV _ => Bool.false
def jeqLF : Nat → List JSValue → List JSValue → Bool
  | 0, [], [] => Bool.true
  | 0, _ :: _, [] => Bool.false
  | 0, [], _ :: _ => Bool.false
  | 0, _ :: _, _ :: _ => Bool.false
  | k + 1, [], [] => Bool.true
  | k + 1, _ :: _, [] => Bool.false
  | k + 1, [], _ :: _ => Bool.false
  | k + 1, x :: xs, y :: ys => jeqF k x y && jeqLF k xs ys
def deqF : Nat → Descriptor → Descriptor → Bool
  | 0, _, _ => Bool.false
  | k + 1, .mk v₁ w₁ g₁ s₁ e₁ c₁, .mk v₂ w₂ g₂ s₂ e₂ c₂ =>
      (match v₁, v₂ with
        | some x, some y => jeqF k x y
        | none, none => Bool.true
        | _, _ => Bool.false)
      && (w₁ == w₂) && (g₁ == g₂) && (s₁ == s₂)
      && (e₁ == e₂) && (c₁ == c₂)
end

/- ## Fuel-structural depth -/
mutual
def dpt : Nat → JSValue → Nat
  | 0, _ => 0
  | k + 1, .compl _ v => dpt k v + 1
  | k + 1, .listV vs => dptL k vs + 1
  | k + 1, .descV d => dptD k d + 1
  | k + 1, .undefined => 1
  | k + 1, .null => 1
  | k + 1, .boolean _ => 1
  | k + 1, .number _ => 1
  | k + 1, .str _ => 1
  | k + 1, .obj _ => 1
def dptL : Nat → List JSValue → Nat
  | 0, [] => 0
  | 0, _ :: _ => 0
  | k + 1, [] => 0
  | k + 1, v :: vs => Nat.max (dpt k v + 1) (dptL k vs + 1)
def dptD : Nat → Descriptor → Nat
  | 0, _ => 0
  | k + 1, .mk (some x) _ _ _ _ _ => dpt k x + 1
  | k + 1, .mk none _ _ _ _ _ => 1
end

/- ## WF depth -/
mutual
def depthL : List JSValue → Nat
  | [] => 0
  | v :: vs => depth v + depthL vs + 1
termination_by vs => sizeOf vs
def depth : JSValue → Nat
  | .compl _ v => depth v + 1
  | .listV vs => depthL vs + 1
  | .descV d => depthD d + 1
  | .undefined => 1
  | .null => 1
  | .boolean _ => 1
  | .number _ => 1
  | .str _ => 1
  | .obj _ => 1
termination_by v => sizeOf v
def depthD : Descriptor → Nat
  | .mk (some x) _ _ _ _ _ => depth x + 1
  | .mk none _ _ _ _ _ => 1
termination_by d => sizeOf d
decreasing_by all_goals simp_wf <;> simp_all [sizeOf] <;> omega
end

mutual
theorem dpt_le_depth : ∀ (k : Nat) (a : JSValue), dpt k a ≤ depth a := by
  intro k a
  cases k with
  | zero => cases a <;> simp [dpt] <;> omega
  | succ k =>
      cases a with
      | compl _ v => have ih := dpt_le_depth k v; simp only [dpt, depth]; omega
      | listV vs => have ih := dptL_le_depthL k vs; simp only [dpt, depth]; omega
      | descV d => have ih := dptD_le_depthD k d; simp only [dpt, depth]; omega
      | undefined | null | boolean _ | number _ | str _ | obj _ =>
          simp only [dpt, depth]; omega
termination_by k => k
theorem dptL_le_depthL : ∀ (k : Nat) (vs : List JSValue), dptL k vs ≤ depthL vs := by
  intro k vs
  cases k with
  | zero => cases vs <;> simp [dptL]
  | succ k =>
      cases vs with
      | nil => simp only [dptL, depthL]; omega
      | cons v rest =>
          have ih1 := dpt_le_depth k v
          have ih2 := dptL_le_depthL k rest
          simp only [dptL, depthL]
          exact Nat.max_le.mpr ⟨by omega, by omega⟩
termination_by k => k
theorem dptD_le_depthD : ∀ (k : Nat) (d : Descriptor), dptD k d ≤ depthD d := by
  intro k d
  cases k with
  | zero => cases d <;> simp [dptD]
  | succ k =>
      cases d with
      | mk v _ _ _ _ _ =>
          cases v with
          | some x => have ih := dpt_le_depth k x; simp only [dptD, depthD]; omega
          | none => simp only [dptD, depthD]; omega
termination_by k => k
end

/- ## Fuel monotonicity -/
mutual
theorem dpt_succ : ∀ (k : Nat) (a : JSValue), dpt k a ≤ dpt (k + 1) a := by
  intro k a
  cases a with
  | compl _ v =>
      cases k with
      | zero => simp only [dpt]; omega
      | succ k' => have ih := dpt_succ k' v; simp only [dpt]; omega
  | listV vs =>
      cases k with
      | zero => simp only [dpt]; omega
      | succ k' => have ih := dptL_succ k' vs; simp only [dpt]; omega
  | descV d =>
      cases k with
      | zero => simp only [dpt]; omega
      | succ k' => have ih := dptD_succ k' d; simp only [dpt]; omega
  | undefined | null | boolean _ | number _ | str _ | obj _ =>
      cases k <;> simp only [dpt] <;> omega
termination_by a => a
theorem dptL_succ : ∀ (k : Nat) (vs : List JSValue), dptL k vs ≤ dptL (k + 1) vs := by
  intro k vs
  cases vs with
  | nil => cases k <;> simp only [dptL] <;> omega
  | cons v rest =>
      cases k with
      | zero => simp only [dptL]; omega
      | succ k' =>
          have ih1 := dpt_succ k' v
          have ih2 := dptL_succ k' rest
          simp only [Nat.succ_eq_add_one, dptL]
          refine Nat.max_le.mpr ⟨?_, ?_⟩
          · exact Nat.le_trans (Nat.add_le_add_right ih1 1)
              (Nat.le_max_left (dpt (k' + 1) v + 1) (dptL (k' + 1) rest + 1))
          · exact Nat.le_trans (Nat.add_le_add_right ih2 1)
              (Nat.le_max_right (dpt (k' + 1) v + 1) (dptL (k' + 1) rest + 1))
termination_by vs => vs
theorem dptD_succ : ∀ (k : Nat) (d : Descriptor), dptD k d ≤ dptD (k + 1) d := by
  intro k d
  cases d with
  | mk v _ _ _ _ _ =>
      cases v with
      | some x =>
          cases k with
          | zero => simp only [dptD]; omega
          | succ k' => have ih := dpt_succ k' x; simp only [dptD]; omega
      | none => cases k <;> simp only [dptD] <;> omega
termination_by d => d
end

theorem dpt_mono : ∀ (j j' : Nat) (a : JSValue), j ≤ j' → dpt j a ≤ dpt j' a := by
  intro j j' a hle
  induction j' generalizing j with
  | zero => have : j = 0 := Nat.le_zero.mp hle; subst this; simp [dpt]
  | succ j'' ih =>
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · have h1 : dpt j a ≤ dpt j'' a :=
            ih j (Nat.le_of_lt_succ hlt)
        have h2 : dpt j'' a ≤ dpt (j'' + 1) a := dpt_succ j'' a
        omega
      · subst heq; exact Nat.le_refl _

/- ## refl -/
mutual
theorem jeqLF_refl : ∀ (k : Nat) (xs : List JSValue),
    dptL k xs + 1 ≤ k → jeqLF k xs xs = Bool.true := by
  intro k xs h
  cases k with
  | zero => cases xs <;> simp [dptL] at h
  | succ k =>
      cases xs with
      | nil => simp only [jeqLF]
      | cons x rest =>
          simp only [dptL] at h
          have hm : Nat.max (dpt k x + 1) (dptL k rest + 1) ≤ k := by omega
          obtain ⟨hx, hr⟩ := Nat.max_le.mp hm
          simp only [jeqLF, jeqF_refl k x hx, jeqLF_refl k rest hr, Bool.true_and]
termination_by k => k
theorem jeqF_refl : ∀ (k : Nat) (a : JSValue),
    dpt k a + 1 ≤ k → jeqF k a a = Bool.true := by
  intro k a h
  cases k with
  | zero => cases a <;> simp [dpt] at h
  | succ k =>
      cases a with
      | undefined | null => simp only [jeqF]
      | boolean _ | number _ | str _ | obj _ =>
          simp only [jeqF, beq_self_eq_true]
      | compl b v =>
          have hv : dpt k v + 1 ≤ k := by simp only [dpt] at h; omega
          simp only [jeqF, Bool.and_eq_true, beq_self_eq_true, jeqF_refl k v hv, and_true]
      | listV vs =>
          have hvs : dptL k vs + 1 ≤ k := by simp only [dpt] at h; omega
          simp only [jeqF, jeqLF_refl k vs hvs]
      | descV d =>
          have hd : dptD k d + 1 ≤ k := by simp only [dpt] at h; omega
          simp only [jeqF, deqF_refl k d hd]
termination_by k => k
theorem deqF_refl : ∀ (k : Nat) (d : Descriptor),
    dptD k d + 1 ≤ k → deqF k d d = Bool.true := by
  intro k d h
  cases k with
  | zero => cases d <;> simp [dptD] at h
  | succ k =>
      cases d with
      | mk v w g s e c =>
          cases v with
          | none =>
              simp only [deqF, Bool.and_eq_true, beq_self_eq_true, and_true]
          | some x =>
              have hx : dpt k x + 1 ≤ k := by simp only [dptD] at h; omega
              simp only [deqF, Bool.and_eq_true, jeqF_refl k x hx,
                         beq_self_eq_true, and_true]
termination_by k => k
end

/- ## eq -/
mutual
theorem jeqLF_eq : ∀ (k : Nat) (l₁ l₂ : List JSValue),
    jeqLF k l₁ l₂ = Bool.true → l₁ = l₂ := by
  intro k l₁ l₂ h
  cases k with
  | zero =>
      cases l₁ <;> cases l₂ <;> first
        | rfl
        | (simp only [jeqLF] at h; exact Bool.noConfusion h)
  | succ k =>
      cases l₁ <;> cases l₂ <;> first
        | rfl
        | (simp only [jeqLF] at h; exact Bool.noConfusion h)
        | (simp only [jeqLF, Bool.and_eq_true] at h
           obtain ⟨hx, hxs⟩ := h
           rw [jeqF_eq k _ _ hx, jeqLF_eq k _ _ hxs])
termination_by k => k
theorem jeqF_eq : ∀ (k : Nat) (a b : JSValue),
    jeqF k a b = Bool.true → a = b := by
  intro k a b h
  cases k with
  | zero => simp only [jeqF] at h; exact Bool.noConfusion h
  | succ k =>
      cases a <;> cases b <;> simp only [jeqF] at h <;> first
        | rfl
        | exact Bool.noConfusion h
        | exact congrArg _ (eq_of_beq h)
        | exact congrArg _ (jeqLF_eq k _ _ h)
        | exact congrArg _ (deqF_eq k _ _ h)
        | (simp only [Bool.and_eq_true] at h
           obtain ⟨h1, h2⟩ := h
           have ha := eq_of_beq h1
           have hv := jeqF_eq k _ _ h2
           rw [ha, hv])
termination_by k => k
theorem deqF_eq : ∀ (k : Nat) (d₁ d₂ : Descriptor),
    deqF k d₁ d₂ = Bool.true → d₁ = d₂ := by
  intro k d₁ d₂ h
  cases k with
  | zero => simp only [deqF] at h; exact Bool.noConfusion h
  | succ k =>
      cases d₁ with
      | mk v₁ w₁ g₁ s₁ e₁ c₁ =>
          cases d₂ with
          | mk v₂ w₂ g₂ s₂ e₂ c₂ =>
              cases v₁ with
              | none =>
                  cases v₂ with
                  | none =>
                      simp only [deqF, Bool.and_eq_true] at h
                      obtain ⟨⟨⟨⟨⟨_, hw⟩, hg⟩, hs⟩, he⟩, hc⟩ := h
                      rw [eq_of_beq hw, eq_of_beq hg, eq_of_beq hs,
                          eq_of_beq he, eq_of_beq hc]
                  | some y => simp only [deqF] at h; exact Bool.noConfusion h
              | some x =>
                  cases v₂ with
                  | none => simp only [deqF] at h; exact Bool.noConfusion h
                  | some y =>
                      simp only [deqF, Bool.and_eq_true] at h
                      obtain ⟨⟨⟨⟨⟨hx, hw⟩, hg⟩, hs⟩, he⟩, hc⟩ := h
                      rw [jeqF_eq k x y hx, eq_of_beq hw, eq_of_beq hg,
                          eq_of_beq hs, eq_of_beq he, eq_of_beq hc]
termination_by k => k
end

/- ## Instances -/
def jeq (a b : JSValue) : Bool := jeqF (Nat.max (depth a) (depth b) + 1) a b

instance : BEq JSValue := ⟨jeq⟩

theorem jeq_refl (a : JSValue) : (a == a) = Bool.true := by
  have hd := dpt_le_depth (depth a + 1) a
  show jeq a a = Bool.true
  unfold jeq
  simp only [Nat.max_self]
  exact jeqF_refl _ a (by omega)

theorem jeq_eq (a b : JSValue) (h : (a == b) = Bool.true) : a = b :=
  jeqF_eq _ a b h

instance : ReflBEq JSValue := by
  constructor
  exact jeq_refl _
instance : LawfulBEq JSValue := by
  constructor
  exact fun h => jeq_eq _ _ h

def deq (d₁ d₂ : Descriptor) : Bool :=
  deqF (Nat.max (depthD d₁) (depthD d₂) + 1) d₁ d₂

instance : BEq Descriptor := ⟨deq⟩

theorem deq_refl (d : Descriptor) : (d == d) = Bool.true := by
  have hd := dptD_le_depthD (depthD d + 1) d
  show deq d d = Bool.true
  unfold deq
  simp only [Nat.max_self]
  exact deqF_refl _ d (by omega)

theorem deq_eq (d₁ d₂ : Descriptor) (h : (d₁ == d₂) = Bool.true) : d₁ = d₂ :=
  deqF_eq _ d₁ d₂ h

instance : ReflBEq Descriptor := by
  constructor
  exact deq_refl _
instance : LawfulBEq Descriptor := by
  constructor
  exact fun h => deq_eq _ _ h

/- ## Transfer lemmas -/
theorem contains_transfer {x w : JSValue} {l : List JSValue}
    (hxw : (x == w) = Bool.true) (h : l.contains w = Bool.true) :
    l.contains x = Bool.true := by
  have hw : w ∈ l := List.contains_iff_mem.mp h
  have hx : x ∈ l := by rw [eq_of_beq hxw]; exact hw
  exact List.contains_iff_mem.mpr hx

theorem all_mem_contains : ∀ (ws xs : List JSValue),
    ws.all xs.contains = Bool.true → ∀ v, v ∈ ws → xs.contains v = Bool.true := by
  intro ws xs hall v hv
  revert hall hv
  induction ws with
  | nil => intro hall hv; cases hv
  | cons w rest ihw =>
      intro hall hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | hv'
      · rw [List.all_cons] at hall
        simp only [Bool.and_eq_true] at hall
        exact hall.1
      · rw [List.all_cons] at hall
        simp only [Bool.and_eq_true] at hall
        exact ihw hall.2 hv'

theorem all_contains_trans {vs ws xs : List JSValue}
    (h₁ : vs.all ws.contains = Bool.true)
    (h₂ : ws.all xs.contains = Bool.true) :
    vs.all xs.contains = Bool.true := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      rw [List.all_cons] at h₁ ⊢
      simp only [Bool.and_eq_true] at h₁ ⊢
      obtain ⟨hv, hrest⟩ := h₁
      refine ⟨?_, ih hrest⟩
      have hvm : v ∈ ws := List.contains_iff_mem.mp hv
      exact all_mem_contains ws xs h₂ v hvm


inductive Expr where
  | nv (name : «String»)
  | nat (n : Nat)
  | const (v : JSValue)
  | isObject (e : Expr)
  | isNotObject (e : Expr)
  | isNotUndefined (e : Expr)
  | hasCall (e : Expr)
  | hasCtor (e : Expr)
  | isU (e : Expr)
  | isBoolVal (b : Bool) (e : Expr)
  | isStrVal (s : «String») (e : Expr)
  | isNullOrUnd (e : Expr)
  | isNull (e : Expr)
  | isType (ty : «String») (e : Expr)
  | hasField (name : «String») (e : Expr)
  | imeth (name : «String») (recv : Expr) (args : List Expr)
  | ifield (name : «String») (e : Expr)
  | varNotPresent (name : «String»)
  | call (name : «String») (args : List Expr)
  | listE (es : List Expr)
  /- FIRST-CLASS COMPLETION OPS (the IteratorClose corner): a
     completion is an ordinary value; these test its kind and
     convert between the completion and bare layers. -/
  | isNormalC (e : Expr)     -- "e is a normal completion"
  | isCompletion (e : Expr)  -- "e is a Completion Record" (either kind)
  | isThrowC (e : Expr)      -- "e is a throw completion"
  | complValue (e : Expr)    -- e.[[Value]] (normal only)
  | completionOf (e : Expr)  -- Completion(e) (bare only)
  deriving Repr

/- Clean, label-free AST (what the interpreter consumes). -/
inductive Step where
  | ret (v : Expr)
  | retE (e : Expr)
  | retNewSlot (slotName : «String») (valVar : «String»)
  | assertE (e : Expr)
  | forEach (x : «String») (e : Expr) (body : List Step)
  | throw
  | setE (name : «String») (e : Expr)
  | letE (name : «String») (e : Expr)
  | ifS (c : Expr) (t : List Step) (e : List Step)
  | elseM (body : List Step)
  deriving Repr

abbrev Prog := List Step


/- Label-carrying parallel AST (what the audit consumes). -/
inductive LBody where
  | ret (v : Expr)
  | retE (e : Expr)
  | retNewSlot (slotName : «String») (valVar : «String»)
  | assertE (e : Expr)
  | forEach (x : «String») (e : Expr) (body : List («String» × LBody))
  | throw
  | setE (name : «String») (e : Expr)
  | letE (name : «String») (e : Expr)
  | ifS (c : Expr) (t : List («String» × LBody)) (e : List («String» × LBody))
  | elseM (body : List («String» × LBody))
  deriving Repr

abbrev LStep := String × LBody

/- Flat stream body: ifs and elses carry no branches here;
   `renest` fills them in from the depth markers. -/
inductive FBody where
  | ret (v : Expr)
  | retE (e : Expr)
  | throw
  | setE (name : «String») (e : Expr)
  | ifI (c : Expr) (s : FBody)
  | elseI (s : FBody)
  | elseG (c : Expr)
  | assertE (e : Expr)
  | forEach (x : «String») (e : Expr)
  | retNewSlot (slotName : «String») (valVar : «String»)
  | letE (name : «String») (e : Expr)
  | ifS (c : Expr)
  | elseM
  deriving Repr

abbrev FStep := Nat × String × FBody

/- Fuse an ECMA-262 `N. Else,` step into the immediately preceding if.
   A dangling marker is kept in the output — a stray "else" can never
   silently lose its branch; it stays visible for the audit. -/
/- else-if CHAINS nest: an else-step attaches to the end of the last
   if's else-branch, not by overwriting it. A dangling else (no
   preceding if) stays visible. -/
/- Attach a pending else-block at the INNERMOST if whose else is
   still open — else-if chains nest: `If c1 … / Else if c2 … / Else …`
   makes the second block the else of c2's if, not c1's. -/
def setDeepestElse (b : List LStep) : List LStep → List LStep
  | [] => b
  | (l, LBody.ifS c t []) :: rest => (l, LBody.ifS c t b) :: rest
  | (l, LBody.ifS c t e') :: rest => (l, LBody.ifS c t (setDeepestElse b e')) :: rest
  | p => p ++ b

/-- Attaching an elseM block removes exactly one elseM step; the
   lexicographic measure (elseM-count, total size) decreases. -/
def countElse : List LStep → Nat
  | [] => 0
  | (_, LBody.elseM _) :: r => 1 + countElse r
  | _ :: r => countElse r

theorem countElse_cons (n : «String») (b : LBody) (r : List LStep) :
    countElse r ≤ countElse ((n, b) :: r) := by
  cases b <;> simp [countElse]

def fuseL : List LStep → List LStep
  | [] => []
  | (l, LBody.ifS c t e') :: (_, LBody.elseM e) :: rest =>
      fuseL ((l, LBody.ifS c t (setDeepestElse e e')) :: rest)
  | p :: rest => p :: fuseL rest
termination_by l => countElse l + l.length
decreasing_by
  · simp [countElse] <;> omega
  · obtain ⟨n, b⟩ := p
    have hmono := countElse_cons n b rest
    simp only [List.length_cons]
    omega

mutual
def strip : List LStep → Prog
  | [] => []
  | (_l, b) :: rest => stripBody b :: strip rest
def stripBody : LBody → Step
  | .ret v => .ret v
  | .retNewSlot sn vv => .retNewSlot sn vv
  | .throw => .throw
  | .assertE e => .assertE e
  | .forEach x e b => .forEach x e (strip b)
  | .retE e => .retE e
  | .setE n e => .setE n e
  | .letE n e => .letE n e
  | .ifS c t e => .ifS c (strip t) (strip e)
  | .elseM b => .elseM (strip b)
end

/- Fuse else-steps, then strip labels. -/

/- Consecutiveness audit: label ordinals per scheme (1→1, a→1, i→1). -/
def romanOrd : «String» → Option Nat
  | "i" => some 1 | "ii" => some 2 | "iii" => some 3
  | "iv" => some 4 | "v" => some 5 | "vi" => some 6
  | _ => none

def labelOrd (s : «String») : Option Nat :=
  match s.toNat? with
  | some n => some n
  | none =>
    match romanOrd s with
    | some n => some n
    | none =>
      if s.length == 1
          && s.front.toNat ≥ 'a'.toNat && s.front.toNat ≤ 'z'.toNat then
        some (s.front.toNat - 'a'.toNat + 1)
      else none

mutual
/- check l i: the labels of l are i, i+1, i+2, … and every nested
   block (checked recursively) also starts at 1. -/
def check : List LStep → Nat → Bool
  | [], _ => true
  | p :: rest, i =>
      match labelOrd p.1 with
      | some n => n == i && checkBody p.2 && check rest (i + 1)
      | none => false
def checkBody : LBody → Bool
  | .ifS _ t e => check t 1 && check e 1
  | .forEach _ _ b => check b 1
  | .elseM b => check b 1
  | _ => true
end

def checkRun (l : List LStep) : Bool := check l 1


inductive Prim where              -- bedrock predicates (the axiom stratum)
  | pIsObj | pIsNotObj | pIsNotU | pHasCall
  | pHasCtor | pIsU | pIsTrue | pIsFalse
  | pNullOrUnd
  | pWrapC
  | pThrowC
  | pIsNull
  | pIsType (s : «String»)
  | pHasField (s : «String»)
  | pDescField (s : «String»)
  | pIsStr (s : «String»)
  | pPred (f : «String») (b : Bool)   -- correlated AO predicate (IsDataDescriptor(x) is b)
  | pIsNormalC                        -- v is a normal completion
  | pIsCompletion                     -- v is a Completion Record (either kind)
  | pIsThrowC                         -- v is a throw completion
  | pUnwrapC                          -- complN v -> v (loud on throw)
  deriving Repr





/- Control boundaries as frames: the callee REPLACES the current list
   (caller continuation saved in the frame — cannot be spliced wrong),
   and return POPS one frame (no scanning, cannot discard past a
   boundary). break/continue/try later = more Frame kinds. -/




/-- Calls the machine answers natively when the registry misses. -/
def nativeOps : List «String» :=
  ["GetV", "Get", "Call", "GetMethod", "OrdinaryToPrimitive"]

/- Internal-slot universe: closed by construction (ES declares the set). -/
inductive Slot where
  | call | construct | strData | dateValue
  | boolData | numData | symData | bigData
  deriving Repr, BEq

def slotOrd : Slot → Nat
  | .call => 0 | .construct => 1 | .strData => 2 | .dateValue => 3
  | .boolData => 4 | .numData => 5 | .symData => 6 | .bigData => 7

def slotOfName : «String» → Option Nat
  | "Call" => some (slotOrd .call)
  | "Construct" => some (slotOrd .construct)
  | "StringData" => some (slotOrd .strData)
  | "DateValue" => some (slotOrd .dateValue)
  | "BooleanData" => some (slotOrd .boolData)
  | "NumberData" => some (slotOrd .numData)
  | "SymbolData" => some (slotOrd .symData)
  | "BigIntData" => some (slotOrd .bigData)
  | _ => none

/- The transcribed-operation registry (the corpus). -/
abbrev AOReg := List («String» × (List «String» × Prog))


def findAO : AOReg → «String» → Option (List «String» × Prog)
  | [], _ => none
  | (n, e) :: r, n' => if n == n' then some e else findAO r n'




/- ===== SOS semantics: state = (remaining program, env).
   The if-rule splices the branch:  ifS c t e :: rest → (t ++ rest | e ++ rest).
   One SOS step = one whole statement (conditions/expressions evaluate atomically).
   Reference semantics closest to the spec prose; agreement with the machine
   above is the next theorem. ===== -/


/- ===== Frame machine: eval stack + frames + in-list loop markers.
   LoopFrame IS the statement list; the final marker is the redo
   instruction (user's design). Expressions decompose at runtime:

     kEval (call f [a1..an]) :: rt  =>  kEval a1 :: … :: kEval an :: kCall f n :: rt
     kEval (isObject e)      :: rt  =>  kEval e :: kPrim1 pIsObj :: rt

   Consumers pop the eval stack (top of stack = LAST pushed operand):
     kCall f n : pop n -> new frame (env = params.zip popped.reverse)
     kRet      : top of eval -> caller's eval, pop frame (stuck if empty)
     kThrow    : pop one frame per step, kThrow at the caller's head
     kSet/kDrop/kBranch/kAssert: pop 1
   Invariant (lemma, not type): eval stack empty at statement boundaries. -/

inductive Instr where
  | kEval (e : Expr)
  | kPrim1 (p : Prim)
  | kCall (f : «String») (n : Nat)
  | kSet (x : «String»)
  | kPop
  | kIte (t e : List Instr)
  | kAssert
  | kRet
  | kTest
  | kUnwrap
  | kIMeth (name : «String») (n : Nat)
  | kMkList (n : Nat)
  | kNewSlot (slotName : «String»)
  | kRepeatWhile (c : Expr) (body : List Instr)
  | kRepeatTest (c : Expr) (body : List Instr)
  | kForStart (x : «String») (body : List Instr)
  | kForBody (x : «String») (elems : List JSValue) (body : List Instr)
  | kTestVar (x : «String») (p : Prim)  -- fused variable test: push p(env x), no expansion
  deriving Repr


def compileSteps : List Step → List Instr
  | [] => []
  | .ret v :: rest => .kEval v :: .kPrim1 .pWrapC :: .kRet :: compileSteps rest
  | .retE e :: rest =>
      -- `Return ? e`: if e is a call/imeth its kEval decomposition already
      -- self-tests (propagating abrupt / unwrapping normal), so the value
      -- arrives raw and we just wrap it. Any other shape: test here.
      ((match e with
        | .call _ _ | .imeth _ _ _ | .ifield _ _ =>
            -- the dust of calls, imeths, and field reads yields a RAW
            -- value (the field read is a pure record projection);
            -- just wrap it. Any other shape: test here.
            [.kEval e, .kPrim1 .pWrapC, .kRet]
        | _ =>
            [.kEval e, .kTest, .kIte [.kRet] [.kUnwrap, .kPrim1 .pWrapC, .kRet]])
        : List Instr)
        ++ compileSteps rest
  | .retNewSlot sn vv :: rest =>
      .kEval (.nv vv) :: .kNewSlot sn :: .kPrim1 .pWrapC :: .kRet
        :: compileSteps rest
  | .throw :: rest =>
      .kEval (.const JSValue.undefined) :: .kPrim1 .pThrowC :: .kRet
        :: compileSteps rest
  | .setE n e :: rest => .kEval e :: .kSet n :: compileSteps rest
  | .letE n e :: rest => .kEval e :: .kSet n :: compileSteps rest
  | .assertE e :: rest => .kEval e :: .kAssert :: compileSteps rest
  | .forEach x e body :: rest =>
      .kEval e :: .kForStart x (compileSteps body) :: compileSteps rest
  | .ifS c t e :: rest =>
      .kEval c :: .kIte (compileSteps t) (compileSteps e) :: compileSteps rest
  | .elseM _ :: rest => compileSteps rest   -- unreachable post-fuseL

