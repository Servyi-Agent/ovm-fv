import Metalanguage.Grammar
import Metalanguage.Semantics
import Metalanguage.Typecheck

/- # Subject reduction: fstep preserves typing.

   A frame TYPES AS P: `checkSeq` of its remaining instructions,
   started from the canonically-abstracted runtime stack (plus one
   anticipated in-flight completion when a callee sits directly
   above), falls through to an eval stack of shape P — or exits via
   kRet. Each machine step preserves the judgment: the same P is
   re-derived from the new state, never recomputed from scratch.

   Two facts make the agreement between static and runtime intrinsic:
   - the abstract stack/type-env are DERIVED from the runtime values
     (`stackTyOf`, `envTyOf`), and the canonical value types track
     exactly the machine-invariant distinctions (compl, boolean, obj,
     list, any) — so runtime pushes land EXACTLY on the static types;
   - branches and loop bodies are stack-neutral (enforced by the
     checker's join rule), so P is a function of the frame, not of
     the moment. -/

/- Runtime-value <-> static-type agreement is definitional: -/

def stackTyOf : List JSValue → List STy := fun eval => eval.map typeOfV

def envTyOf : Env → TyEnv := fun env => env.map (fun (n, v) => (n, typeOfV v))

/- The canonical abstractions commute with the frame's own operations:

   lookup into the runtime env agrees with tyLookup into its
   abstraction (both first-match, so shadowing behaves identically). -/
theorem envTyOf_lookup (env : Env) (x : «String») :
    (lookup env x).map typeOfV = tyLookup (envTyOf env) x := by
  induction env with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨n, v⟩ := hd
      by_cases h : n == x
      · simp [lookup, tyLookup, envTyOf, h]
      · simp [lookup, tyLookup, envTyOf, h, ih]

/- Pushing a value extends the abstract stack canonically. -/
theorem stackTyOf_cons (v : JSValue) (eval : List JSValue) :
    stackTyOf (v :: eval) = typeOfV v :: stackTyOf eval := rfl

/- Binding a value extends the abstract type-env canonically. -/
theorem envTyOf_cons (n : «String») (v : JSValue) (env : Env) :
    envTyOf ((n, v) :: env) = (n, typeOfV v) :: envTyOf env := rfl

/- ## The in-flight completion.

   After kCall / kIMeth-"Get" fire, the caller's instructions are
   `kTest :: kIte [kRet] [kUnwrap] :: rest` and the completion it will
   test does not exist yet: it is inside the callee frame above. The
   judgment anticipates exactly one delivery — TYPED by the callee's
   destiny: the frame above knows its AO name, hence its declared
   return type. -/

def selfTestHead : List Instr → Bool
  | .kTest :: .kIte [.kRet] [.kUnwrap] :: _ => Bool.true
  | _ => Bool.false

def inflight (sigs : SigTable) (above : Option «String») : List STy :=
  match above with
  | some n => [STy.complN (sigRetTy sigs n)]
  | none => []

def absStack (sigs : SigTable) (above : Option «String») (f : Fr) : List STy :=
  inflight sigs above ++ stackTyOf f.eval

/- ## Frame and state typing -/

def frameOk (sigs : SigTable) (above : Option «String») (f : Fr) : Prop :=
  -- a frame under a callee MUST be waiting at the self-test idiom:
  -- the delivery assumption of kRet
  (above.isNone ∨ selfTestHead f.stmts = Bool.true)
    ∧ (match checkSeq sigs (sigRetTy sigs f.ret)
                [{ Γ := envTyOf f.env, σ := absStack sigs above f }] f.stmts with
       | .flows fb => terminal fb = Bool.true  -- every world returns
       | _ => False)

/-- Each frame is checked at its own destiny (its AO's declared
   return type), anticipating a delivery TYPED by the frame directly
   above. -/
def framesOkFrom : SigTable → Option «String» → List Fr → Prop
  | _, _, [] => True
  | sigs, above, f :: fs =>
      frameOk sigs above f ∧ framesOkFrom sigs f.ret fs

def framesOk (sigs : SigTable) (fs : List Fr) : Prop :=
  framesOkFrom sigs none fs

-- Object references reachable from a value (completions carry
-- payloads; descriptors and lists carry values).
mutual
def locsList : List JSValue → List Nat
  | [] => []
  | v :: vs => locsOf v ++ locsList vs
termination_by vs => sizeOf vs
decreasing_by all_goals simp_wf <;> omega

def locsOf : JSValue → List Nat
  | .obj l => [l]
  | .compl _ v => locsOf v
  | .descV (.mk (some v) _ (some g) (some s) _ _) =>
      locsOf v ++ [g, s]
  | .descV (.mk (some v) _ _ (some s) _ _) => locsOf v ++ [s]
  | .descV (.mk (some v) _ (some g) _ _ _) => locsOf v ++ [g]
  | .descV (.mk (some v) _ _ _ _ _) => locsOf v
  | .descV (.mk none _ (some g) (some s) _ _) => [g, s]
  | .descV (.mk none _ _ (some s) _ _) => [s]
  | .descV (.mk none _ (some g) _ _ _) => [g]
  | .descV _ => []
  | .listV vs => locsList vs
  | _ => []
termination_by v => sizeOf v
decreasing_by all_goals simp_wf <;> omega
end

/- References out of an allocated object: property descriptor
   payloads. -/
def objRefs (o : JsObj) : List Nat :=
  (o.props.flatMap (fun (_, d) =>
     match d with
     | .mk (some v) _ _ _ _ _ => locsOf v
     | _ => []))

/-- Heap agreement over a BOUNDED region [0, n) — the region grows
   with allocation, so no separate nextLoc conjunct is needed:
   (a) every frame-rooted object reference is in-region and resolves;
   (b) every object allocated IN-REGION has in-region, resolving
       outgoing references.
   Induction over these gives transitive soundness of every reachable
   chain; (b) is stronger than reachability (in-region garbage may not
   dangle either). Allocation at exactly n extends the region by one. -/
def heapOk (heap : Heap) (n : Nat) : List Fr → Prop
  | [] => ∀ l < n, ∀ o, heap l = some o →
      (objRefs o).all (fun r => r < n ∧ (heap r).isSome)
  | f :: fs =>
      (∀ l ∈ (f.eval.flatMap locsOf ++ (f.env.map Prod.snd).flatMap locsOf),
        l < n ∧ (heap l).isSome)
      ∧ heapOk heap n fs

/- ## Heap typing (store typing)

   A kind-map over locations, EXISTENTIALLY quantified in the state
   invariant. It makes the machine's "prototype chain is ordinary"
   assumption LOCAL: each object checks only its own edge —
   (1) the object is consistent with its map entry (kind matches;
       grows to shape checks per kind when exotics arrive),
   (2) if it has a prototype, the parent is allocated AND its map
       entry is ordinary (our [[Get]] runs OrdinaryGet unconditionally;
       per-kind dispatch would relax this to "parent's entry has a
       kind-appropriate [[Get]]").
   Composition over edges gives the whole chain — no chain walk, and
   no acyclicity (agreed: termination only, not safety). -/
abbrev HeapTy := Nat → Kind

def objConsistent (k : Kind) (o : JsObj) : Bool :=
  match k, o.kind with
  | .ordinary, .ordinary => Bool.true
  | .string _, .string _ => Bool.true
  | .builtin _ _, .builtin _ _ => Bool.true
  | _, _ => Bool.false

def heapTyOk (heap : Heap) (ht : HeapTy) (n : Nat) : Prop :=
  ∀ l < n, ∀ o, heap l = some o →
    objConsistent (ht l) o = Bool.true
    ∧ ∀ p, o.proto = some p →
        p < n ∧ (heap p).isSome = Bool.true ∧ ht p = .ordinary

/- The machine's return type is the BOTTOM frame's destiny (stable:
   only that frame popping turns the state into fdone). -/
def machineRet (sigs : SigTable) (fs : List Fr) : STy :=
  match fs.getLast? with
  | some f => sigRetTy sigs f.ret
  | none => .val anyV

/- ## State typing, indexed by the machine's answer type r.

   fell is ILL-TYPED: with this definition, preservation alone
   already implies progress. -/
def stateOk (sigs : SigTable) (r : STy) (m : FM) : Prop :=
  match m with
  | .frames fs heap nl =>
      fs.isEmpty = Bool.false
      ∧ framesOk sigs fs ∧ heapOk heap nl fs
      ∧ ∃ ht, heapTyOk heap ht nl
      ∧ machineRet sigs fs = r
  | .fdone v _ _ _ _ =>
      -- the final value: normal compl-wrapped payload ⊑ r, or a throw
      match typeOfV v with
      | .complN p => tmoves p r = Bool.true
      | .complT => True
      | _ => False
  | .fell _ _ _ _ => False

/- Registry coverage (existence): every name the checker may call is
   answered by the registry or natively; the MOP-Get dispatch target
   exists. -/
def closedRegistry (sigs : SigTable) (reg : AOReg) : Prop :=
  (∀ n _ps _ret, sigFind sigs n = some (_ps, _ret) →
      (findAO reg n).isSome = Bool.true ∨ nativeOps.contains n = Bool.true)
  ∧ (findAO reg "OrdinaryGet").isSome = Bool.true

/- ## The target statement (proof in progress, bottom-up):

   theorem type_safety (sigs : SigTable) (reg : AOReg)
       (hreg : registryCertified sigs reg)
       (hcover : closedRegistry sigs reg)
       (m : FM) (h : stateOk sigs r m) :
       stateOk sigs r (fstep reg m)

   Preservation alone suffices: fell is ill-typed in stateOk. -/

/- ## Registry certification

   kCall pushes the callee's compiled body with a fresh env made from
   the ACTUAL argument values. Nothing about the caller can make that
   frame well-typed, so subject reduction is relative to a registry
   certified at every argument typing that satisfies the signature
   (pointwise: equal, or the parameter is `any`). -/

def registryCertified (sigs : SigTable) (reg : AOReg) : Prop :=
  ∀ name ps prog, (name, (ps, prog)) ∈ reg →
    ∀ ts, leList ts (sigParams sigs name) →
      (match checkSeq sigs (sigRetTy sigs name)
              [{ Γ := zipTy ps ts, σ := [] }] (compileSteps prog) with
       | .flows fb => terminal fb = Bool.true
       | _ => False)


/- The subtype-transitivity and stack-subtyping lemmas are re-queued
   for the monotonicity push: STy is now a nested inductive (union /
   oneOf), so the induction needs a custom well-founded recursion;
   they land together with the refinement-monotonicity lemma. -/

/- ## Proof layer, step 1: subtype algebra -/

/-- Mask subset: a ⊆ b as bit sets. -/
def maskSub (a b : Nat) : Bool := (a - (a &&& b)) == 0

theorem maskSub_trans (a b c : Nat) (h₁ : maskSub a b = Bool.true)
    (h₂ : maskSub b c = Bool.true) : maskSub a c = Bool.true := by
  have ba : a &&& b ≤ a := Nat.and_le_left (n := a) (m := b)
  have bb : b &&& c ≤ b := Nat.and_le_left (n := b) (m := c)
  have d1 : a - (a &&& b) = 0 := of_decide_eq_true h₁
  have d2 : b - (b &&& c) = 0 := of_decide_eq_true h₂
  have e1 : a = a &&& b := by omega
  have e2 : b = b &&& c := by omega
  have h : a &&& c = a := by
    have s1 : a &&& c = (a &&& b) &&& c := by
      conv => lhs; rw [e1]
    have s2 : (a &&& b) &&& c = a &&& (b &&& c) := Nat.and_assoc a b c
    have s3 : a &&& (b &&& c) = a &&& b := by rw [← e2]
    have idem : a &&& b &&& b = a &&& b := by
      rw [Nat.and_assoc, Nat.and_self]
    calc a &&& c = (a &&& b) &&& c := s1
      _ = a &&& (b &&& c) := s2
      _ = a &&& b := s3
      _ = a := e1.symm
  unfold maskSub
  exact decide_eq_true (by omega)

theorem maskSub_mem (x a b : Nat) (hmem : x &&& a ≠ 0)
    (hs : maskSub a b = Bool.true) : x &&& b ≠ 0 := by
  intro hz
  have hle : a &&& b ≤ a := Nat.and_le_left (n := a) (m := b)
  have d1 : a - (a &&& b) = 0 := of_decide_eq_true hs
  have hab : a = a &&& b := by omega
  have key : (x &&& a) &&& b = x &&& a := by
    rw [Nat.and_assoc, ← hab]
  have rearr : (x &&& a) &&& b = (x &&& b) &&& a := by
    rw [Nat.and_assoc, Nat.and_comm a b, ← Nat.and_assoc]
  have h1 : (x &&& b) &&& a ≤ x &&& b := Nat.and_le_left (n := x &&& b) (m := a)
  rw [hz] at h1
  have h0 : (x &&& b) &&& a = 0 := by
    rw [hz]
    exact Nat.zero_and a
  have hkey : x &&& a = 0 := by
    calc x &&& a = (x &&& a) &&& b := key.symm
      _ = (x &&& b) &&& a := rearr
      _ = 0 := h0
  omega

/-- Depth of the complN spine — the ONLY place tmovesAtom recurses.
    (STy is a nested inductive, so the generic recursor is unusable;
    direct structural recursion on constructor arguments still
    works.) -/
def complDepth : STy → Nat
  | .complN t => 1 + complDepth t
  | .val _ | .desc _ | .descAny | .isValue _ | .oneOf _ | .notPresent
  | .union _ | .complT => 0

theorem complDepth_lt (p : STy) : complDepth p < complDepth (STy.complN p) := by
  simp only [complDepth]; omega

/-- Pointwise all-transfer: if every element of vs satisfies P, and P
    implies Q pointwise, every element satisfies Q. -/
theorem all_imp {vs : List JSValue} {P Q : JSValue → Bool}
    (himp : ∀ v, P v = Bool.true → Q v = Bool.true)
    (h : vs.all P = Bool.true) : vs.all Q = Bool.true := by
  induction vs with
  | nil => rfl
  | cons v rest ih =>
      rw [List.all_cons] at h ⊢
      simp only [Bool.and_eq_true] at h ⊢
      obtain ⟨hv, hr⟩ := h
      exact ⟨himp v hv, ih hr⟩

/- Prop-interface version of maskSub_mem. -/
theorem maskSub_mem' (x a b : Nat) (hmem : x &&& a ≠ 0)
    (hsub : a - (a &&& b) = 0) : x &&& b ≠ 0 :=
  maskSub_mem x a b hmem (by unfold maskSub; exact beq_iff_eq.mpr hsub)

/-- Pointwise membership: every element satisfying all Q. -/
theorem all_mem : ∀ (l : List JSValue) (Q : JSValue → Bool),
    l.all Q = Bool.true → ∀ v, v ∈ l → Q v = Bool.true := by
  intro l Q h
  revert h
  induction l with
  | nil => intro _ _ hv; cases hv
  | cons w rest ih =>
      intro h v hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | hv'
      · rw [List.all_cons] at h
        simp only [Bool.and_eq_true] at h
        exact h.1
      · rw [List.all_cons] at h
        simp only [Bool.and_eq_true] at h
        exact ih h.2 v hv'

/- ## Step 1a: transitivity through a NON-complN middle type. -/

theorem tmovesAtom_flat (b a c : STy) (hb : complDepth b = 0)
    (h₁ : tmovesAtom a b = Bool.true)
    (h₂ : tmovesAtom b c = Bool.true) : tmovesAtom a c = Bool.true := by
  cases b with
  | val m =>
      cases c with
      | val k =>
          cases a with
          | val n =>
              simp only [tmovesAtom, Bool.or_eq_true, beq_iff_eq] at h₁ h₂ ⊢
              rcases h₁ with h1a | h1b <;> rcases h₂ with h2a | h2b
              · exact Or.inl h1a
              · exact Or.inl h1a
              · rw [h2a] at h1b
                rw [Nat.and_zero, Nat.sub_zero] at h1b
                exact Or.inl h1b
              · have hb := maskSub_trans n m k (decide_eq_true h1b) (decide_eq_true h2b)
                simp only [maskSub, beq_iff_eq] at hb
                exact Or.inr hb
          | isValue v =>
              simp only [tmovesAtom] at h₁
              simp only [tmovesAtom, Bool.or_eq_true, beq_iff_eq] at h₂
              rcases h₂ with h2a | h2b
              · rw [h2a, Nat.and_zero] at h₁
                exact absurd h₁ (by simp)
              · exact bne_iff_ne.mpr
                  (maskSub_mem' (ctorBit v) m k (bne_iff_ne.mp h₁) h2b)
          | oneOf vs =>
              simp only [tmovesAtom] at h₁
              simp only [tmovesAtom, Bool.or_eq_true, beq_iff_eq] at h₂
              rcases h₂ with h2a | h2b
              · exact all_imp (fun v hv => by
                  rw [h2a, Nat.and_zero] at hv
                  exact absurd hv (by simp)) h₁
              · exact all_imp (fun v hv =>
                  bne_iff_ne.mpr
                    (maskSub_mem' (ctorBit v) m k (bne_iff_ne.mp hv) h2b)) h₁
          | desc _ | descAny | notPresent | union _ | complN _ | complT =>
              simp only [tmovesAtom] at h₁
              exact Bool.noConfusion h₁
      | isValue _ | oneOf _ | desc _ | descAny | notPresent
      | union _ | complN _ | complT =>
          simp only [tmovesAtom] at h₂
          exact Bool.noConfusion h₂
  | isValue w =>
      cases a with
      | isValue v =>
          have hvw : v = w := eq_of_beq (by simpa only [tmovesAtom] using h₁)
          subst hvw
          cases c with
          | isValue u => simpa only [tmovesAtom] using h₂
          | oneOf xs =>
              simp only [tmovesAtom] at h₂ ⊢
              exact contains_transfer (beq_self_eq_true _) h₂
          | val n => simpa only [tmovesAtom] using h₂
          | desc _ | descAny | notPresent | union _ | complN _ | complT =>
              simp only [tmovesAtom] at h₂
              exact Bool.noConfusion h₂
      | oneOf vs =>
          cases c with
          | isValue u =>
              simp only [tmovesAtom] at h₁ h₂ ⊢
              exact all_imp (fun _ hv => by rw [eq_of_beq hv]; exact h₂) h₁
          | oneOf xs =>
              simp only [tmovesAtom] at h₁ h₂ ⊢
              exact all_imp (fun _ hv => contains_transfer hv h₂) h₁
          | val n =>
              simp only [tmovesAtom] at h₁ h₂ ⊢
              exact all_imp (fun _ hv => by rw [eq_of_beq hv]; exact h₂) h₁
          | desc _ | descAny | notPresent | union _ | complN _ | complT =>
              simp only [tmovesAtom] at h₂
              exact Bool.noConfusion h₂
      | val _ | desc _ | descAny | notPresent | union _ | complN _ | complT =>
          simp only [tmovesAtom] at h₁
          exact Bool.noConfusion h₁
  | oneOf ws =>
      cases a with
      | isValue v =>
          cases c with
          | isValue u =>
              simp only [tmovesAtom] at h₁ h₂ ⊢
              exact all_mem ws (fun z => z == u) h₂ v (List.contains_iff_mem.mp h₁)
          | oneOf xs =>
              simp only [tmovesAtom] at h₁ h₂ ⊢
              exact all_mem ws xs.contains h₂ v (List.contains_iff_mem.mp h₁)
          | val k =>
              simp only [tmovesAtom] at h₁ h₂ ⊢
              exact all_mem ws (fun z => ctorBit z &&& k != 0) h₂ v
                (List.contains_iff_mem.mp h₁)
          | desc _ | descAny | notPresent | union _ | complN _ | complT =>
              simp only [tmovesAtom] at h₂
              exact Bool.noConfusion h₂
      | oneOf vs =>
          cases c with
          | oneOf xs =>
              simp only [tmovesAtom] at h₁ h₂ ⊢
              exact all_contains_trans h₁ h₂
          | val k =>
              simp only [tmovesAtom] at h₁ h₂ ⊢
              exact all_imp (fun v hv =>
                all_mem ws (fun z => ctorBit z &&& k != 0) h₂ v
                  (List.contains_iff_mem.mp hv)) h₁
          | isValue u =>
              simp only [tmovesAtom] at h₁ h₂ ⊢
              exact all_imp (fun v hv =>
                all_mem ws (fun z => z == u) h₂ v (List.contains_iff_mem.mp hv)) h₁
          | desc _ | descAny | notPresent | union _ | complN _ | complT =>
              simp only [tmovesAtom] at h₂
              exact Bool.noConfusion h₂
      | val _ | desc _ | descAny | notPresent | union _ | complN _ | complT =>
          simp only [tmovesAtom] at h₁
          exact Bool.noConfusion h₁
  | desc m =>
      cases a with
      | desc n =>
          cases c with
          | desc k =>
              simp only [tmovesAtom, Bool.or_eq_true, beq_iff_eq] at h₁ h₂ ⊢
              rcases h₁ with h1a | h1b <;> rcases h₂ with h2a | h2b
              · exact Or.inl h1a
              · exact Or.inl h1a
              · rw [h2a] at h1b
                rw [Nat.and_zero] at h1b
                exact Or.inl h1b.symm
              · exact Or.inr (by
                  calc n &&& k = (n &&& m) &&& k := by conv => lhs; rw [← h1b]
                    _ = n &&& (m &&& k) := Nat.and_assoc n m k
                    _ = n &&& m := by rw [h2b]
                    _ = n := h1b)
          | descAny => rfl
          | val _ | isValue _ | oneOf _ | notPresent | union _ | complN _ | complT =>
              simp only [tmovesAtom] at h₂
              exact Bool.noConfusion h₂
      | val _ | isValue _ | oneOf _ | descAny | notPresent | union _ | complN _ | complT =>
          simp only [tmovesAtom] at h₁
          exact Bool.noConfusion h₁
  | descAny =>
      cases a with
      | desc n =>
          cases c with
          | descAny => rfl
          | val _ | isValue _ | oneOf _ | desc _ | notPresent | union _ | complN _ | complT =>
              simp only [tmovesAtom] at h₂
              exact Bool.noConfusion h₂
      | descAny =>
          cases c with
          | descAny => rfl
          | val _ | isValue _ | oneOf _ | desc _ | notPresent | union _ | complN _ | complT =>
              simp only [tmovesAtom] at h₂
              exact Bool.noConfusion h₂
      | val _ | isValue _ | oneOf _ | notPresent | union _ | complN _ | complT =>
          simp only [tmovesAtom] at h₁
          exact Bool.noConfusion h₁
  | notPresent =>
      cases a with
      | notPresent =>
          cases c with
          | notPresent => rfl
          | val _ | isValue _ | oneOf _ | desc _ | descAny | union _ | complN _ | complT =>
              simp only [tmovesAtom] at h₂
              exact Bool.noConfusion h₂
      | val _ | isValue _ | oneOf _ | desc _ | descAny | union _ | complN _ | complT =>
          simp only [tmovesAtom] at h₁
          exact Bool.noConfusion h₁
  | complT =>
      cases a with
      | complT =>
          cases c with
          | complT => rfl
          | val _ | isValue _ | oneOf _ | desc _ | descAny | notPresent | union _ | complN =>
              simp only [tmovesAtom] at h₂
              exact Bool.noConfusion h₂
      | val _ | isValue _ | oneOf _ | desc _ | descAny | notPresent | union _ | complN =>
          simp only [tmovesAtom] at h₁
          exact Bool.noConfusion h₁
  | union ps =>
      cases a with
      | val _ | isValue _ | oneOf _ | desc _ | descAny | notPresent | union _ | complN _ | complT =>
          simp only [tmovesAtom] at h₁
          exact Bool.noConfusion h₁
  | complN p => rw [complDepth] at hb; omega

/- ## Step 1b: full transitivity by fuel induction on the spine. -/

theorem tmovesAtom_trans_fuel : ∀ (n : Nat) (b a c : STy), complDepth b ≤ n →
    tmovesAtom a b = Bool.true → tmovesAtom b c = Bool.true →
      tmovesAtom a c = Bool.true := by
  intro n
  induction n with
  | zero =>
      intro b a c hb h₁ h₂
      have hbd : complDepth b = 0 := Nat.le_zero.mp hb
      cases b with
      | complN p => rw [complDepth] at hbd; omega
      | val _ | isValue _ | oneOf _ | desc _ | descAny | notPresent | union _ | complT =>
          exact tmovesAtom_flat _ a c (by simpa only [complDepth] using hbd) h₁ h₂
  | succ n ih =>
      intro b a c hb h₁ h₂
      cases b with
      | complN p =>
          have hlt : complDepth p ≤ n := by
            have := complDepth_lt p
            simp only [complDepth] at this hb
            omega
          cases c with
          | complN q =>
              cases a with
              | complN n₂ =>
                  simp only [tmovesAtom] at h₁ h₂ ⊢
                  exact ih p n₂ q hlt h₁ h₂
              | val _ | isValue _ | oneOf _ | desc _ | descAny | notPresent
              | union _ | complT =>
                  simp only [tmovesAtom] at h₁
                  exact Bool.noConfusion h₁
          | val _ | isValue _ | oneOf _ | desc _ | descAny | notPresent
          | union _ | complT =>
              cases a with
              | complN n₂ =>
                  simp only [tmovesAtom] at h₂
                  exact Bool.noConfusion h₂
              | val _ | isValue _ | oneOf _ | desc _ | descAny | notPresent
              | union _ | complT =>
                  simp only [tmovesAtom] at h₁
                  exact Bool.noConfusion h₁
      | val _ | isValue _ | oneOf _ | desc _ | descAny | notPresent | union _ | complT =>
          exact tmovesAtom_flat _ a c (by simp only [complDepth]) h₁ h₂

theorem tmovesAtom_trans (b a c : STy) (h₁ : tmovesAtom a b = Bool.true)
    (h₂ : tmovesAtom b c = Bool.true) : tmovesAtom a c = Bool.true :=
  tmovesAtom_trans_fuel (complDepth b) b a c (Nat.le_refl _) h₁ h₂

/-- Union-level transitivity. -/
theorem tmoves_trans (t u v : STy)
    (h₁ : tmoves t u = Bool.true) (h₂ : tmoves u v = Bool.true) :
    tmoves t v = Bool.true := by
  simp only [tmoves, List.all_eq_true] at h₁ h₂ ⊢
  intro a ha
  have hau := h₁ a ha
  simp only [List.any_eq_true] at hau
  obtain ⟨b, hb, hab⟩ := hau
  have hbc := h₂ b hb
  simp only [List.any_eq_true] at hbc
  obtain ⟨c, hc, hbc⟩ := hbc
  simp only [List.any_eq_true]
  exact ⟨c, hc, tmovesAtom_trans b a c hab hbc⟩
