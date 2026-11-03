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

theorem locsOf_compl (b : Bool) (v : JSValue) :
    locsOf (.compl b v) = locsOf v := by rw [locsOf]

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
  | none => .anyValue anyV

/- ## State typing, indexed by the machine's answer type r.

   fell is ILL-TYPED: with this definition, preservation alone
   already implies progress. -/
/- Program-side literal well-formedness: every location referenced by
    a constant literal still to be executed is inside the heap region
    and resolves. Syntax is the only channel by which a location can
    enter the runtime state without having been reachable before (the
    emu-alg surface never embeds object literals, so corpus programs
    satisfy this vacuously; the conjunct covers the model's degenerate
    instructions). -/
def instrWf (heap : Heap) (nl : Nat) (i : Instr) : Prop :=
  match i with
  | .kEval (.const v) =>
      ∀ l ∈ locsOf v, l < nl ∧ (heap l).isSome = Bool.true
  | .kForBody _ vs _ =>
      ∀ l ∈ vs.flatMap locsOf, l < nl ∧ (heap l).isSome = Bool.true
  | _ => True

def instrsWf (heap : Heap) (nl : Nat) : List Instr → Prop
  | [] => True
  | i :: rest => instrWf heap nl i ∧ instrsWf heap nl rest

def framesWf (heap : Heap) (nl : Nat) : List Fr → Prop
  | [] => True
  | f :: fs => instrsWf heap nl f.stmts ∧ framesWf heap nl fs

def stateOk (sigs : SigTable) (r : STy) (m : FM) : Prop :=
  match m with
  | .frames fs heap nl =>
      fs.isEmpty = Bool.false
      ∧ framesOk sigs fs ∧ heapOk heap nl fs
      ∧ (∃ ht, heapTyOk heap ht nl)
      ∧ machineRet sigs fs = r
      ∧ framesWf heap nl fs
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

/-- The certificate a registry entry carries at a given argument
    typing. -/
def certifies (sigs : SigTable) (name : «String») (ps : List «String»)
    (ts : List STy) (prog : Prog) : Prop :=
  match checkSeq sigs (sigRetTy sigs name)
      [{ Γ := zipTy ps ts, σ := [] }] (compileSteps prog) with
  | .flows fb => terminal fb = Bool.true
  | _ => False

theorem certifies_flows_elim {sigs : SigTable} {name : «String»}
    {ps : List «String»} {ts : List STy} {prog : Prog}
    (h : certifies sigs name ps ts prog) :
    ∃ fb, checkSeq sigs (sigRetTy sigs name)
        [{ Γ := zipTy ps ts, σ := [] }] (compileSteps prog)
        = TCResult.flows fb ∧ terminal fb = Bool.true := by
  cases hb : checkSeq sigs (sigRetTy sigs name)
      [{ Γ := zipTy ps ts, σ := [] }] (compileSteps prog) with
  | flows fb =>
      simp only [certifies] at h
      rw [hb] at h
      exact ⟨fb, rfl, h⟩
  | reject s w =>
      simp only [certifies] at h
      rw [hb] at h
      exact False.elim h

def registryCertified (sigs : SigTable) (reg : AOReg) : Prop :=
  ∀ name ps prog, (name, (ps, prog)) ∈ reg →
    (∀ (heap : Heap) (nl : Nat), instrsWf heap nl (compileSteps prog)) ∧
    ∀ ts, leList ts (sigParams sigs name) →
      certifies sigs name ps ts prog


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
  | .anyValue _ | .desc _ | .descAny | .isValue _ | .oneOf _ | .notPresent
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
  | anyValue m =>
      cases c with
      | anyValue k =>
          cases a with
          | anyValue n =>
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
          | anyValue n => simpa only [tmovesAtom] using h₂
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
          | anyValue n =>
              simp only [tmovesAtom] at h₁ h₂ ⊢
              exact all_imp (fun _ hv => by rw [eq_of_beq hv]; exact h₂) h₁
          | desc _ | descAny | notPresent | union _ | complN _ | complT =>
              simp only [tmovesAtom] at h₂
              exact Bool.noConfusion h₂
      | anyValue _ | desc _ | descAny | notPresent | union _ | complN _ | complT =>
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
          | anyValue k =>
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
          | anyValue k =>
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
      | anyValue _ | desc _ | descAny | notPresent | union _ | complN _ | complT =>
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
          | anyValue _ | isValue _ | oneOf _ | notPresent | union _ | complN _ | complT =>
              simp only [tmovesAtom] at h₂
              exact Bool.noConfusion h₂
      | anyValue _ | isValue _ | oneOf _ | descAny | notPresent | union _ | complN _ | complT =>
          simp only [tmovesAtom] at h₁
          exact Bool.noConfusion h₁
  | descAny =>
      cases a with
      | desc n =>
          cases c with
          | descAny => rfl
          | anyValue _ | isValue _ | oneOf _ | desc _ | notPresent | union _ | complN _ | complT =>
              simp only [tmovesAtom] at h₂
              exact Bool.noConfusion h₂
      | descAny =>
          cases c with
          | descAny => rfl
          | anyValue _ | isValue _ | oneOf _ | desc _ | notPresent | union _ | complN _ | complT =>
              simp only [tmovesAtom] at h₂
              exact Bool.noConfusion h₂
      | anyValue _ | isValue _ | oneOf _ | notPresent | union _ | complN _ | complT =>
          simp only [tmovesAtom] at h₁
          exact Bool.noConfusion h₁
  | notPresent =>
      cases a with
      | notPresent =>
          cases c with
          | notPresent => rfl
          | anyValue _ | isValue _ | oneOf _ | desc _ | descAny | union _ | complN _ | complT =>
              simp only [tmovesAtom] at h₂
              exact Bool.noConfusion h₂
      | anyValue _ | isValue _ | oneOf _ | desc _ | descAny | union _ | complN _ | complT =>
          simp only [tmovesAtom] at h₁
          exact Bool.noConfusion h₁
  | complT =>
      cases a with
      | complT =>
          cases c with
          | complT => rfl
          | anyValue _ | isValue _ | oneOf _ | desc _ | descAny | notPresent | union _ | complN =>
              simp only [tmovesAtom] at h₂
              exact Bool.noConfusion h₂
      | anyValue _ | isValue _ | oneOf _ | desc _ | descAny | notPresent | union _ | complN =>
          simp only [tmovesAtom] at h₁
          exact Bool.noConfusion h₁
  | union ps =>
      cases a with
      | anyValue _ | isValue _ | oneOf _ | desc _ | descAny | notPresent | union _ | complN _ | complT =>
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
      | anyValue _ | isValue _ | oneOf _ | desc _ | descAny | notPresent | union _ | complT =>
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
              | anyValue _ | isValue _ | oneOf _ | desc _ | descAny | notPresent
              | union _ | complT =>
                  simp only [tmovesAtom] at h₁
                  exact Bool.noConfusion h₁
          | anyValue _ | isValue _ | oneOf _ | desc _ | descAny | notPresent
          | union _ | complT =>
              cases a with
              | complN n₂ =>
                  simp only [tmovesAtom] at h₂
                  exact Bool.noConfusion h₂
              | anyValue _ | isValue _ | oneOf _ | desc _ | descAny | notPresent
              | union _ | complT =>
                  simp only [tmovesAtom] at h₁
                  exact Bool.noConfusion h₁
      | anyValue _ | isValue _ | oneOf _ | desc _ | descAny | notPresent | union _ | complT =>
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

/- ## Step 2: refinement monotonicity.

    The static certificate explores a FINITE set of worlds; the runtime
    realizes ONE world that refines one of them pointwise (e.g. the
    checker reasons `val boolV`, the machine holds `isValue true`).
    Every checker operation is monotone under refinement, so the
    realized world stays inside the certificate's world set as
    execution proceeds. -/

/-- Type refinement (subtyping as a Prop). -/
def tyLe (t' t : STy) : Prop := tmoves t' t = Bool.true

/-- Environment refinement: every static binding is realized at a
    subtype (shadowing-identical first-match structure). -/
def envLe (Γ' Γ : TyEnv) : Prop :=
  ∀ x t, tyLookup Γ x = some t → ∃ t', tyLookup Γ' x = some t' ∧ tyLe t' t

/-- Stack refinement: same length, pointwise subtypes. -/
def stackLe : List STy → List STy → Prop
  | [], [] => True
  | t' :: σ', t :: σ => tyLe t' t ∧ stackLe σ' σ
  | _, _ => False

def worldLe (w' w : World) : Prop := envLe w'.Γ w.Γ ∧ stackLe w'.σ w.σ

def worldsLe (ws' ws : Worlds) : Prop := ∀ w' ∈ ws', ∃ w ∈ ws, worldLe w' w

/-- Atoms never contain an OUTER union; complN spines descend into
    union-free payloads (guaranteed by atoms's normalization). -/
def atomSh : STy → Bool
  | .union _ => Bool.false
  | .complN t => atomSh t
  | _ => Bool.true

/-- Combined union/complN nesting depth. -/
def aDepth : STy → Nat
  | .union ps => 1 + (ps.map aDepth).foldr Nat.max 0
  | .complN t => 1 + aDepth t
  | _ => 0

theorem foldr_max_ge : ∀ (xs : List Nat) (x : Nat), x ∈ xs →
    x ≤ xs.foldr Nat.max 0 := by
  intro xs x hx
  induction xs with
  | nil => cases hx
  | cons y rest ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx'
      · simp only [List.foldr_cons]
        exact Nat.le_max_left _ (List.foldr Nat.max 0 rest)
      · have h1 := ih hx'
        simp only [List.foldr_cons]
        exact Nat.le_trans h1 (Nat.le_max_right _ (List.foldr Nat.max 0 rest))

theorem all_append' {P : STy → Bool} {l₁ l₂ : List STy} :
    l₁.all P = Bool.true → l₂.all P = Bool.true →
    (l₁ ++ l₂).all P = Bool.true := by
  intro h₁ h₂
  simp only [List.all_eq_true, List.mem_append] at h₁ h₂ ⊢
  intro a ha
  rcases ha with ha | ha
  · exact h₁ a ha
  · exact h₂ a ha

theorem flatMap_all {P : STy → Bool} {ps : List STy}
    (h : ∀ p ∈ ps, (atoms p).all P = Bool.true) :
    (ps.flatMap atoms).all P = Bool.true := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
      have hp : (atoms p).all P = Bool.true := h p (by simp)
      have hr : (rest.flatMap atoms).all P = Bool.true :=
        ih (fun q hq => h q (by simp [hq]))
      simp only [List.flatMap_cons]
      exact all_append' hp hr

theorem map_all {P : STy → Bool} {f : STy → STy} {l : List STy}
    (h : l.all (fun x => P (f x)) = Bool.true) : (l.map f).all P = Bool.true := by
  simp only [List.all_eq_true, List.mem_map] at h ⊢
  intro a ha
  obtain ⟨x, hx, rfl⟩ := ha
  exact h x hx

/-- Every atom satisfies atomSh. -/
theorem atoms_sh : ∀ (n : Nat) (t : STy), aDepth t ≤ n →
    (atoms t).all atomSh = Bool.true := by
  intro n
  induction n with
  | zero =>
      intro t ht
      cases t with
      | union ps =>
          have h1 : 1 ≤ aDepth (STy.union ps) := by simp only [aDepth]; omega
          have h2 : aDepth (STy.union ps) ≤ 0 := ht
          omega
      | complN t' =>
          have h1 : 1 ≤ aDepth (STy.complN t') := by simp only [aDepth]; omega
          omega
      | anyValue _ | isValue _ | oneOf _ | desc _ | descAny | notPresent | complT =>
          simp only [atoms, atomSh, List.all_cons, List.all_nil, Bool.and_true]
  | succ n ih =>
      intro t ht
      cases t with
      | union ps =>
          simp only [atoms]
          apply flatMap_all
          intro p hp
          have hfold : aDepth p ≤ (ps.map aDepth).foldr Nat.max 0 :=
            foldr_max_ge (ps.map aDepth) (aDepth p) (List.mem_map_of_mem hp)
          simp only [aDepth] at ht
          have : aDepth p ≤ n := by omega
          exact ih p this
      | complN t' =>
          simp only [atoms]
          refine map_all ?_
          simp only [aDepth] at ht
          have : aDepth t' ≤ n := by omega
          have := ih t' this
          rw [List.all_eq_true] at this ⊢
          intro a ha
          have := this a ha
          simp only [atomSh]
          exact this
      | anyValue _ | isValue _ | oneOf _ | desc _ | descAny | notPresent | complT =>
          simp only [atoms, atomSh, List.all_cons, List.all_nil, Bool.and_true]

/-- Atom reflexivity for union-free spines, by spine fuel. -/
theorem tmovesAtom_refl_sh : ∀ (n : Nat) (a : STy), complDepth a ≤ n →
    atomSh a = Bool.true → tmovesAtom a a = Bool.true := by
  intro n
  induction n with
  | zero =>
      intro a ha hsh
      cases a with
      | complN t => rw [complDepth] at ha; omega
      | union _ => simp only [atomSh] at hsh; exact Bool.noConfusion hsh
      | anyValue m =>
          simp only [tmovesAtom, Bool.or_eq_true, beq_iff_eq, Nat.and_self, Nat.sub_self]
          exact Or.inr trivial
      | desc m =>
          simp only [tmovesAtom, Bool.or_eq_true, beq_iff_eq, Nat.and_self]
          exact Or.inr trivial
      | isValue v => simp only [tmovesAtom, beq_self_eq_true]
      | oneOf vs =>
          simp only [tmovesAtom, List.all_eq_true]
          intro v hv
          exact List.contains_iff_mem.mpr hv
      | descAny | notPresent | complT => rfl
  | succ n ih =>
      intro a ha hsh
      cases a with
      | complN t =>
          simp only [tmovesAtom]
          have ht : complDepth t ≤ n := by
            have := complDepth_lt t
            simp only [complDepth] at this ha
            omega
          exact ih t ht (by simp only [atomSh] at hsh; exact hsh)
      | union _ => simp only [atomSh] at hsh; exact Bool.noConfusion hsh
      | anyValue m =>
          simp only [tmovesAtom, Bool.or_eq_true, beq_iff_eq, Nat.and_self, Nat.sub_self]
          exact Or.inr trivial
      | desc m =>
          simp only [tmovesAtom, Bool.or_eq_true, beq_iff_eq, Nat.and_self]
          exact Or.inr trivial
      | isValue v => simp only [tmovesAtom, beq_self_eq_true]
      | oneOf vs =>
          simp only [tmovesAtom, List.all_eq_true]
          intro v hv
          exact List.contains_iff_mem.mpr hv
      | descAny | notPresent | complT => rfl

theorem tmoves_refl (t : STy) : tmoves t t = Bool.true := by
  have hsh := atoms_sh (aDepth t) t (Nat.le_refl _)
  simp only [tmoves, List.all_eq_true] at hsh ⊢
  intro a ha
  have h1 := hsh a ha
  have h2 := tmovesAtom_refl_sh (complDepth a) a (Nat.le_refl _) h1
  simp only [List.any_eq_true]
  exact ⟨a, ha, h2⟩

theorem tyLe_refl (t : STy) : tyLe t t := tmoves_refl t

theorem envLe_refl (Γ : TyEnv) : envLe Γ Γ := by
  intro x t h
  exact ⟨t, h, tyLe_refl t⟩

theorem stackLe_refl (σ : List STy) : stackLe σ σ := by
  cases σ with
  | nil => exact True.intro
  | cons t rest => exact ⟨tyLe_refl t, stackLe_refl rest⟩

theorem worldLe_refl (w : World) : worldLe w w :=
  ⟨envLe_refl w.Γ, stackLe_refl w.σ⟩

/- ## mapM plumbing -/

theorem mapM_some_all : ∀ (l : List World) (f : World → Option World),
    (∀ x ∈ l, ∃ y, f x = some y) → ∃ l₂, l.mapM f = some l₂ := by
  intro l f h
  induction l with
  | nil => exact ⟨[], by simp⟩
  | cons x rest ih =>
      obtain ⟨y, hy⟩ := h x (by simp)
      obtain ⟨l₂, hl₂⟩ := ih (fun q hq => h q (by simp [hq]))
      refine ⟨y :: l₂, ?_⟩
      simp only [List.mapM_cons, hy, hl₂]
      rfl

theorem mapM_some_mem : ∀ (l : List World) (f : World → Option World) (l₂ : List World),
    l.mapM f = some l₂ → ∀ x ∈ l, ∃ y, f x = some y ∧ y ∈ l₂ := by
  intro l f l₂ h
  induction l generalizing l₂ with
  | nil => cases h; intro x hx; cases hx
  | cons x rest ih =>
      simp only [List.mapM_cons] at h
      obtain ⟨y, hfx, hy2⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨l₂', hrest, hpure⟩ := Option.bind_eq_some_iff.mp hy2
      rw [Option.pure_def] at hpure
      injection hpure with hl
      subst hl
      intro x' hx'
      simp only [List.mem_cons] at hx'
      rcases hx' with rfl | hx''
      · exact ⟨y, hfx, by simp⟩
      · obtain ⟨z, hz1, hz2⟩ := ih l₂' hrest x' hx''
        exact ⟨z, hz1, by simp [hz2]⟩

theorem mapM_mem_of_mem : ∀ (l : List World) (f : World → Option World) (l₂ : List World),
    l.mapM f = some l₂ → ∀ v ∈ l₂, ∃ x ∈ l, f x = some v := by
  intro l f l₂ h
  induction l generalizing l₂ with
  | nil => cases h; intro v hv; cases hv
  | cons x rest ih =>
      simp only [List.mapM_cons] at h
      obtain ⟨y, hfx, hy2⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨l₂', hrest, hpure⟩ := Option.bind_eq_some_iff.mp hy2
      rw [Option.pure_def] at hpure
      injection hpure with hl
      subst hl
      intro v hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | hv'
      · exact ⟨x, by simp, hfx⟩
      · obtain ⟨z, hz1, hz2⟩ := ih l₂' hrest v hv'
        exact ⟨z, by simp [hz1], hz2⟩

theorem mapM_mono (f g : World → Option World)
    (h : ∀ w' w, worldLe w' w → ∀ v, f w = some v → ∃ v', g w' = some v' ∧ worldLe v' v)
    (hle : worldsLe ws' ws) (hM : ws.mapM f = some ws₂) :
    ∃ ws₂', ws'.mapM g = some ws₂' ∧ worldsLe ws₂' ws₂ := by
  have hall : ∀ w' ∈ ws', ∃ v', g w' = some v' ∧ ∃ v, v ∈ ws₂ ∧ worldLe v' v := by
    intro w' hw'
    obtain ⟨w, hw, hwl⟩ := hle w' hw'
    obtain ⟨v, hv, hvw⟩ := mapM_some_mem ws f ws₂ hM w hw
    obtain ⟨v', hv', hle'⟩ := h w' w hwl v hv
    exact ⟨v', hv', v, hvw, hle'⟩
  obtain ⟨ws₂', hM'⟩ := mapM_some_all ws' g
    (fun w' hw' => by obtain ⟨v', hv', _⟩ := hall w' hw'; exact ⟨v', hv'⟩)
  refine ⟨ws₂', hM', ?_⟩
  intro v' hv'
  obtain ⟨w', hw', hv'⟩ := mapM_mem_of_mem ws' g ws₂' hM' v' hv'
  obtain ⟨v₂, hv₂, ⟨v, hv, hle'⟩⟩ := hall w' hw'
  rw [hv₂] at hv'
  injection hv' with he
  subst he
  exact ⟨v, hv, hle'⟩

/- ## Stack plumbing -/

theorem leList_trans : ∀ (as bs cs : List STy),
    leList as bs = Bool.true → leList bs cs = Bool.true → leList as cs = Bool.true := by
  intro as bs cs h1 h2
  induction as generalizing bs cs with
  | nil =>
      cases bs <;> cases cs <;> first
        | rfl
        | (simp only [leList] at h1; exact Bool.noConfusion h1)
        | (simp only [leList] at h2; exact Bool.noConfusion h2)
  | cons a rest ih =>
      cases bs with
      | nil => simp only [leList] at h1; exact Bool.noConfusion h1
      | cons b bs' =>
          cases cs with
          | nil => simp only [leList] at h2; exact Bool.noConfusion h2
          | cons c cs' =>
              simp only [leList, Bool.and_eq_true] at h1 h2 ⊢
              obtain ⟨h1a, h1r⟩ := h1
              obtain ⟨h2a, h2r⟩ := h2
              exact ⟨tmoves_trans a b c h1a h2a, ih bs' cs' h1r h2r⟩

theorem stackLe_leList : ∀ (σ' σ : List STy),
    stackLe σ' σ → leList σ' σ = Bool.true := by
  intro σ' σ h
  induction σ' generalizing σ with
  | nil => cases σ with
    | nil => rfl
    | cons t rest => exact absurd h (by intro hc; cases hc)
  | cons t' rest' ih =>
      cases σ with
      | nil => exact absurd h (by intro hc; cases hc)
      | cons t rest =>
          obtain ⟨h1, h2⟩ := h
          simp only [leList, Bool.and_eq_true]
          exact ⟨h1, ih rest h2⟩

theorem popTy_le (t : STy) (σ' σ : List STy) (hle : stackLe σ' σ) :
    ∀ σ₂, popTy t σ = some σ₂ → ∃ σ₂', popTy t σ' = some σ₂' ∧ stackLe σ₂' σ₂ := by
  cases σ with
  | nil =>
      intro σ₂ h
      simp only [popTy] at h
      exact absurd h (by simp)
  | cons s rest =>
      intro σ₂ h
      cases σ' with
      | nil => exact absurd hle (by intro hc; cases hc)
      | cons s' rest' =>
          simp only [stackLe] at hle
          obtain ⟨h1, h2⟩ := hle
          simp only [popTy] at h
          by_cases hst : tmoves s t = Bool.true
          · rw [if_pos hst] at h
            injection h with hl
            subst hl
            have hst' : tmoves s' t = Bool.true := tmoves_trans s' s t h1 hst
            exact ⟨rest', by simp only [popTy, if_pos hst'], h2⟩
          · rw [if_neg (by simpa using hst)] at h
            exact absurd h (by simp)

theorem popTyN_le (n : Nat) (t : STy) (σ' σ : List STy) (hle : stackLe σ' σ) :
    ∀ σ₂, popTyN n t σ = some σ₂ → ∃ σ₂', popTyN n t σ' = some σ₂' ∧ stackLe σ₂' σ₂ := by
  induction n generalizing σ σ' hle with
  | zero =>
      intro σ₂ h
      simp only [popTyN] at h
      injection h with hl
      subst hl
      exact ⟨σ', rfl, hle⟩
  | succ n ih =>
      intro σ₂ h
      simp only [popTyN] at h
      cases hp : popTy t σ with
      | none => rw [hp] at h; exact absurd h (by simp)
      | some σ₁ =>
          rw [hp] at h
          obtain ⟨σ₁', hp', hle₁⟩ := popTy_le t σ' σ hle σ₁ hp
          obtain ⟨σ₂', h', hle₂⟩ := ih σ₁' σ₁ hle₁ σ₂ h
          exact ⟨σ₂', by simp only [popTyN, hp', h'], hle₂⟩

theorem leList_nil_cons (b : STy) (bs : List STy) : leList [] (b :: bs) = Bool.false := rfl

theorem leList_take : ∀ (n : Nat) (bs bs' : List STy),
    leList bs bs' = Bool.true → leList (bs.take n) (bs'.take n) = Bool.true := by
  intro n
  induction n with
  | zero => intro bs bs' _; rfl
  | succ n ih =>
      intro bs bs' h
      cases bs with
      | nil => cases bs' with
        | nil => rfl
        | cons b bs'' =>
            rw [leList_nil_cons] at h
            exact Bool.noConfusion h
      | cons b rest =>
          cases bs' with
          | nil => simp only [leList] at h; exact Bool.noConfusion h
          | cons b' rest' =>
              simp only [leList, Bool.and_eq_true] at h
              obtain ⟨h1, h2⟩ := h
              rw [List.take_cons (by omega : (0:Nat) < n + 1),
                  List.take_cons (by omega : (0:Nat) < n + 1)]
              simp only [Nat.add_sub_cancel, leList, Bool.and_eq_true]
              exact ⟨h1, ih rest rest' h2⟩

theorem stackLe_length : ∀ (σ' σ : List STy), stackLe σ' σ → σ'.length = σ.length := by
  intro σ' σ h
  cases σ' with
  | nil => cases σ with
    | nil => rfl
    | cons t rest => exact absurd h (by intro hc; cases hc)
  | cons t' rest' =>
      cases σ with
      | nil => exact absurd h (by intro hc; cases hc)
      | cons t rest =>
          simp only [stackLe] at h
          obtain ⟨_, h2⟩ := h
          have hlen := stackLe_length rest' rest h2
          simp only [List.length_cons]
          omega


/- ## Step 3 (start): one-step unfolding identities.

    Each machine step corresponds EXACTLY to one unfolding of
    checkSeq's recursion; these computational identities are the
    lockstep spine of the subject-reduction assembly. -/

/-- kEval (const v): the checker pushes `typeOfV v`, the machine pushes
    `v` whose canonical type is `typeOfV v` — IDENTICAL for every
    value now that typeOfE (const v) is the canonical abstraction
    (this closed the latent divergence for desc/compl literals). -/
theorem checkSeq_kEval_const (sigs : SigTable) (r : STy) (w : World)
    (rest : List Instr) (v : JSValue) :
    checkSeq sigs r [w] (.kEval (.const v) :: rest)
      = checkSeq sigs r [{ w with σ := typeOfV v :: w.σ }] rest := by
  simp only [checkSeq, testType, typeOfE]
  rfl

/-- kEval (nat n): both sides push the singleton number type. -/
theorem checkSeq_kEval_nat (sigs : SigTable) (r : STy) (w : World)
    (rest : List Instr) (n : Nat) :
    checkSeq sigs r [w] (.kEval (.nat n) :: rest)
      = checkSeq sigs r [{ w with σ := typeOfV (.number ↑n) :: w.σ }] rest := by
  simp only [checkSeq, testType, typeOfE]
  rfl

/-- kSet x on a nonempty stack: both sides bind the top type. -/
theorem checkSeq_kSet (sigs : SigTable) (r : STy) (w : World)
    (rest : List Instr) (x : «String») (t : STy) (σ : List STy) :
    checkSeq sigs r [{ w with σ := t :: σ }] (.kSet x :: rest)
      = checkSeq sigs r [{ Γ := (x, t) :: w.Γ, σ := σ }] rest := by
  simp [checkSeq, stepWorlds]

/-- kPop on a nonempty stack: both sides drop the top type. -/
theorem checkSeq_kPop (sigs : SigTable) (r : STy) (w : World)
    (rest : List Instr) (t : STy) (σ : List STy) :
    checkSeq sigs r [{ w with σ := t :: σ }] (.kPop :: rest)
      = checkSeq sigs r [{ w with σ := σ }] rest := by
  simp [checkSeq, stepWorlds]

/- ## Nonemptiness machinery (unblocked by the tyNonempty complN fix). -/

theorem tyNonemptyList_ex : ∀ (ps : List STy), tyNonemptyList ps = Bool.true →
    ∃ p ∈ ps, tyNonempty p = Bool.true := by
  intro ps h
  induction ps with
  | nil => simp only [tyNonemptyList] at h; exact Bool.noConfusion h
  | cons p rest ih =>
      simp only [tyNonemptyList, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ⟨p, by simp, h⟩
      · obtain ⟨q, hq, hneq⟩ := ih h
        exact ⟨q, by simp [hq], hneq⟩

/-- A nonempty type has a nonempty atom (by union depth). -/
theorem tyNonempty_atom : ∀ (n : Nat) (t : STy), aDepth t ≤ n →
    tyNonempty t = Bool.true → ∃ a₀ ∈ atoms t, tyNonempty a₀ = Bool.true := by
  intro n
  induction n with
  | zero =>
      intro t ht hne
      cases t with
      | union ps => have h1 : 1 ≤ aDepth (STy.union ps) := by simp only [aDepth]; omega
                    omega
      | complN t' => have h1 : 1 ≤ aDepth (STy.complN t') := by simp only [aDepth]; omega
                     omega
      | anyValue _ | isValue _ | oneOf _ | desc _ | descAny | notPresent | complT =>
          exact ⟨_, by simp [atoms], hne⟩
  | succ n ih =>
      intro t ht hne
      cases t with
      | union ps =>
          obtain ⟨p, hp, hnp⟩ := tyNonemptyList_ex ps (by simpa only [tyNonempty] using hne)
          have hfold : aDepth p ≤ (ps.map aDepth).foldr Nat.max 0 :=
            foldr_max_ge (ps.map aDepth) (aDepth p) (List.mem_map_of_mem hp)
          simp only [aDepth] at ht
          obtain ⟨a₀, ha₀, hn₀⟩ := ih p (by omega) hnp
          refine ⟨a₀, ?_, hn₀⟩
          simp only [atoms, List.mem_flatMap]
          exact ⟨p, hp, ha₀⟩
      | complN t' =>
          simp only [tyNonempty] at hne
          simp only [aDepth] at ht
          obtain ⟨a₀, ha₀, hn₀⟩ := ih t' (by omega) hne
          refine ⟨STy.complN a₀, ?_, ?_⟩
          · simp only [atoms, List.mem_map]
            exact ⟨a₀, ha₀, rfl⟩
          · simpa only [tyNonempty] using hn₀
      | anyValue _ | isValue _ | oneOf _ | desc _ | descAny | notPresent | complT =>
          exact ⟨_, by simp [atoms], hne⟩

theorem atom_ne_below_oneOf : ∀ (a₀ : STy) (vs : List JSValue),
    tmovesAtom a₀ (.oneOf vs) = Bool.true → tyNonempty a₀ = Bool.true →
    ∃ v, v ∈ vs := by
  intro a₀ vs h hne
  cases a₀ with
  | isValue v =>
      exact ⟨v, List.contains_iff_mem.mp (by simpa only [tmovesAtom] using h)⟩
  | oneOf us =>
      simp only [tmovesAtom, List.all_eq_true] at h
      cases us with
      | nil => simp only [tyNonempty] at hne; exact Bool.noConfusion hne
      | cons u rest =>
          exact ⟨u, List.contains_iff_mem.mp (h u (by simp))⟩
  | anyValue _ | desc _ | descAny | notPresent | union _ | complN _ | complT =>
      simp only [tmovesAtom] at h; exact Bool.noConfusion h

/-- Nonemptiness transfers up through atom-subtyping. -/
theorem tmovesAtom_le_ne (a b : STy) (h : tmovesAtom a b = Bool.true)
    (hne : tyNonempty a = Bool.true) : tyNonempty b = Bool.true := by
  cases b with
  | anyValue m =>
      simp only [tyNonempty, bne_iff_ne]
      intro hm0
      rw [hm0] at h
      cases a with
      | anyValue k =>
          simp only [tmovesAtom, Bool.or_eq_true, beq_iff_eq] at h
          simp only [tyNonempty, bne_iff_ne] at hne
          rcases h with h1 | h1
          · exact hne h1
          · rw [Nat.and_zero, Nat.sub_zero] at h1
            exact hne h1
      | isValue v =>
          have hb := bne_iff_ne.mp (by simpa only [tmovesAtom] using h)
          rw [Nat.and_zero] at hb
          exact hb rfl
      | oneOf vs =>
          simp only [tmovesAtom, List.all_eq_true] at h
          cases vs with
          | nil => simp only [tyNonempty] at hne; exact Bool.noConfusion hne
          | cons v rest =>
              have hb := bne_iff_ne.mp (h v (by simp))
              rw [Nat.and_zero] at hb
              exact hb rfl
      | union _ | desc _ | descAny | notPresent | complN _ | complT =>
          simp only [tmovesAtom] at h; exact Bool.noConfusion h
  | oneOf vs =>
      have key : ∃ v, v ∈ vs := by
        cases a with
        | isValue v =>
            exact atom_ne_below_oneOf (.isValue v) vs
              (by simpa only [tmovesAtom] using h) hne
        | oneOf us =>
            exact atom_ne_below_oneOf (.oneOf us) vs
              (by simpa only [tmovesAtom] using h) hne
        | anyValue _ | desc _ | descAny | notPresent | union _ | complN _ | complT =>
            simp only [tmovesAtom] at h; exact Bool.noConfusion h
      obtain ⟨v, hv⟩ := key
      cases vs with
      | nil => exact absurd hv (by simp)
      | cons x rest => simp [tyNonempty]
  | union _ =>
      cases a <;> simp only [tmovesAtom] at h <;> exact Bool.noConfusion h
  | desc _ | descAny | isValue _ | notPresent | complT =>
      simp only [tyNonempty]
  | complN t =>
      cases a with
      | complN a₂ =>
          simp only [tmovesAtom] at h
          simp only [tyNonempty] at hne
          simp only [tyNonempty]
          exact tmovesAtom_le_ne a₂ t h hne
      | anyValue _ | isValue _ | oneOf _ | desc _ | descAny | notPresent | union _ | complT =>
          simp only [tmovesAtom] at h; exact Bool.noConfusion h

/- ## Bit algebra + meet soundness. -/

theorem pow2_land_eq (p k : Nat) (hk : Nat.testBit k p = true) :
    (2 ^ p &&& k) = 2 ^ p := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hpi : p = i
  · subst hpi
    simp only [Bool.and_true]
    exact hk
  · have hd : (decide (p = i) : Bool) = false := by simp [hpi]
    rw [hd]
    rfl

theorem pow2_land (p k : Nat) : (2 ^ p &&& k) = 0 ∨ (2 ^ p &&& k) = 2 ^ p := by
  by_cases hk : Nat.testBit k p = true
  · exact Or.inr (pow2_land_eq p k hk)
  · left
    by_cases hz : (2 ^ p &&& k) = 0
    · exact hz
    · exfalso
      obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hz
      have h1 : ((decide (p = i)) && Nat.testBit k i) = true := by
        have hh := hi
        rw [Nat.testBit_and, Nat.testBit_two_pow] at hh
        exact hh
      rw [Bool.and_eq_true, decide_eq_true_eq] at h1
      obtain ⟨hip, hkb⟩ := h1
      subst hip
      exact hk hkb

theorem hasBit_pow2_trans (p k m : Nat) (h1 : (2 ^ p &&& k) ≠ 0)
    (h2 : (2 ^ p &&& m) ≠ 0) : (2 ^ p &&& (k &&& m)) ≠ 0 := by
  rcases pow2_land p k with hc | hc
  · exact absurd hc h1
  · rcases pow2_land p m with hd | hd
    · exact absurd hd h2
    · rw [← Nat.and_assoc, hc, hd]
      exact Nat.ne_of_gt (Nat.two_pow_pos p)

theorem ctorBit_pow2 (v : JSValue) :
    (∃ p, ctorBit v = 2 ^ p) ∨ ctorBit v = 0 := by
  cases v with
  | undefined => exact Or.inl ⟨0, rfl⟩
  | null => exact Or.inl ⟨1, rfl⟩
  | boolean b => cases b with
    | true => exact Or.inl ⟨2, rfl⟩
    | false => exact Or.inl ⟨3, rfl⟩
  | number _ => exact Or.inl ⟨4, rfl⟩
  | str _ => exact Or.inl ⟨5, rfl⟩
  | obj _ => exact Or.inl ⟨6, rfl⟩
  | listV _ => exact Or.inl ⟨7, rfl⟩
  | descV _ => exact Or.inl ⟨8, rfl⟩
  | compl _ _ => exact Or.inr rfl

/-- All atoms nonempty (the runtime side typeOfV satisfies this). -/
def atomsNE (a : STy) : Bool := (atoms a).all tyNonempty

theorem maskSub_inter (j k m : Nat) (h1 : maskSub j k = Bool.true)
    (h2 : maskSub j m = Bool.true) : maskSub j (k &&& m) = Bool.true := by
  have e1 : j = j &&& k := by
    have := Nat.and_le_left (n := j) (m := k)
    have := (of_decide_eq_true h1)
    omega
  have e2 : j = j &&& m := by
    have := Nat.and_le_left (n := j) (m := m)
    have := (of_decide_eq_true h2)
    omega
  unfold maskSub
  refine decide_eq_true ?_
  have hcalc : j &&& (k &&& m) = j := by
    calc j &&& (k &&& m) = (j &&& k) &&& m := (Nat.and_assoc j k m).symm
      _ = j &&& m := by conv => rhs; rw [e1]
      _ = j := e2.symm
  have hle : j &&& (k &&& m) ≤ j := Nat.and_le_left (n := j) (m := k &&& m)
  omega

theorem ctorBit_inter_ne (v : JSValue) (k m : Nat)
    (h1 : ((ctorBit v) &&& k) ≠ 0) (h2 : ((ctorBit v) &&& m) ≠ 0) :
    ((ctorBit v) &&& (k &&& m)) ≠ 0 := by
  rcases ctorBit_pow2 v with ⟨p, hp⟩ | h0
  · rw [hp] at h1 h2 ⊢
    exact hasBit_pow2_trans p k m h1 h2
  · rw [h0] at h1
    exact absurd h1 (by simp)

/-- Meet soundness at the atom level: a witness below both inputs is
    below the computed meet (for mask tests). -/
theorem tmovesAtom_meet_val (a₀ s₀ : STy) (m : Nat)
    (hle : tmovesAtom a₀ s₀ = Bool.true)
    (hm : tmovesAtom a₀ (STy.anyValue m) = Bool.true) :
    tmovesAtom a₀ (tyMeetAtom s₀ (STy.anyValue m)) = Bool.true := by
  cases s₀ with
  | anyValue k =>
      cases a₀ with
      | anyValue j =>
          simp only [tyMeetAtom, tmovesAtom, Bool.or_eq_true, beq_iff_eq] at hle hm ⊢
          rcases hle with h1 | h1 <;> rcases hm with h2 | h2
          · exact Or.inl h1
          · exact Or.inl h1
          · exact Or.inl h2
          · have hb := maskSub_inter j k m (decide_eq_true h1) (decide_eq_true h2)
            rw [maskSub, beq_iff_eq] at hb
            exact Or.inr hb
      | isValue v =>
          simp only [tyMeetAtom, tmovesAtom, bne_iff_ne] at hle hm ⊢
          exact ctorBit_inter_ne v k m hle hm
      | oneOf vs =>
          have hall : ∀ w ∈ vs, ((ctorBit w) &&& k) ≠ 0 ∧ ((ctorBit w) &&& m) ≠ 0 := by
            intro w hw
            have e1 := (List.all_eq_true.mp (by simpa only [tmovesAtom] using hle)) w hw
            have e2 := (List.all_eq_true.mp (by simpa only [tmovesAtom] using hm)) w hw
            constructor
            · simpa only [bne_iff_ne] using e1
            · simpa only [bne_iff_ne] using e2
          simp only [tyMeetAtom, tmovesAtom, List.all_eq_true, bne_iff_ne]
          intro w hw
          obtain ⟨h1, h2⟩ := hall w hw
          exact ctorBit_inter_ne w k m h1 h2
      | desc _ | descAny | notPresent | union _ | complN _ | complT =>
          simp only [tmovesAtom] at hm; exact Bool.noConfusion hm
  | isValue v =>
      cases a₀ with
      | isValue w =>
          have hwv : w = v := eq_of_beq (by simpa only [tmovesAtom] using hle)
          rw [hwv] at hle hm
          rw [hwv]
          have hcond : (((ctorBit v) &&& m) != 0) = Bool.true := by
            simpa only [tmovesAtom, bne_iff_ne] using hm
          simp only [tyMeetAtom, if_pos hcond, tmovesAtom, beq_self_eq_true]
      | oneOf ws =>
          cases ws with
          | nil =>
              simp only [tyMeetAtom]
              split <;> simp [tmovesAtom]
          | cons w rest =>
              have hwv : w = v := eq_of_beq
                ((List.all_eq_true.mp (by simpa only [tmovesAtom] using hle)) w (by simp))
              have hwm : ((ctorBit w) &&& m) ≠ 0 := by
                have := (List.all_eq_true.mp (by simpa only [tmovesAtom] using hm)) w (by simp)
                simpa only [tmovesAtom, bne_iff_ne] using this
              have hbm : ((ctorBit v) &&& m) ≠ 0 := by rw [hwv] at hwm; exact hwm
              have hcond : (((ctorBit v) &&& m) != 0) = Bool.true := bne_iff_ne.mpr hbm
              simp only [tyMeetAtom, if_pos hcond]
              simpa only [tmovesAtom] using hle
      | anyValue _ | desc _ | descAny | notPresent | union _ | complN _ | complT =>
          simp only [tmovesAtom] at hle; exact Bool.noConfusion hle
  | oneOf us =>
      cases a₀ with
      | isValue v =>
          have hv : us.contains v = Bool.true := by simpa only [tmovesAtom] using hle
          have hbm : ((ctorBit v) &&& m) ≠ 0 := by
            simpa only [tmovesAtom, bne_iff_ne] using hm
          have hmem : v ∈ us.filter (fun w => ((ctorBit w) &&& m) != 0) :=
            List.mem_filter.mpr ⟨List.contains_iff_mem.mp hv, bne_iff_ne.mpr hbm⟩
          have hne : (us.filter (fun w => ((ctorBit w) &&& m) != 0)).isEmpty = Bool.false := by
            cases hf : us.filter (fun w => ((ctorBit w) &&& m) != 0) with
            | nil => rw [hf] at hmem; exact absurd hmem (by simp)
            | cons x r => rfl
          simp only [tyMeetAtom, hne, Bool.false_eq_true, if_false]
          exact List.contains_iff_mem.mpr hmem
      | oneOf ws =>
          have hall : ws.all us.contains = Bool.true := by simpa only [tmovesAtom] using hle
          have hball : ∀ w ∈ ws, ((ctorBit w) &&& m) ≠ 0 := by
            intro w hw
            have := (List.all_eq_true.mp (by simpa only [tmovesAtom] using hm)) w hw
            simpa only [tmovesAtom, bne_iff_ne] using this
          cases hf : us.filter (fun w => ((ctorBit w) &&& m) != 0) with
          | nil =>
              cases ws with
              | nil =>
                  simp [tyMeetAtom, hf, tmovesAtom]
              | cons w rest =>
                  exfalso
                  have hwu : w ∈ us := List.contains_iff_mem.mp
                    ((List.all_eq_true.mp hall) w (by simp))
                  have hmem : w ∈ us.filter (fun w => ((ctorBit w) &&& m) != 0) :=
                    List.mem_filter.mpr ⟨hwu, bne_iff_ne.mpr (hball w (by simp))⟩
                  rw [hf] at hmem
                  exact absurd hmem (by simp)
          | cons x r =>
              simp only [tyMeetAtom, hf, List.isEmpty_cons, Bool.false_eq_true,
                if_false, tmovesAtom, List.all_eq_true]
              intro w hw
              have hwu : w ∈ us := List.contains_iff_mem.mp
                ((List.all_eq_true.mp hall) w hw)
              have hmem : w ∈ us.filter (fun z => ((ctorBit z) &&& m) != 0) :=
                List.mem_filter.mpr ⟨hwu, bne_iff_ne.mpr (hball w hw)⟩
              rw [hf] at hmem
              exact List.contains_iff_mem.mpr hmem
      | anyValue _ | desc _ | descAny | notPresent | union _ | complN _ | complT =>
          simp only [tmovesAtom] at hle; exact Bool.noConfusion hle
  | desc _ | descAny | notPresent | complN _ | complT =>
      cases a₀ <;> first
        | (simp only [tmovesAtom] at hm; exact Bool.noConfusion hm)
        | (simp only [tmovesAtom] at hle; exact Bool.noConfusion hle)
  | union ps =>
      cases a₀ <;> simp only [tmovesAtom] at hle <;> exact Bool.noConfusion hle


/-- Intro rule for tmoves: exhibit a partner atom per LHS atom. -/
theorem tmoves_intro (a X : STy)
    (h : ∀ a₀ ∈ atoms a, ∃ k ∈ atoms X, tmovesAtom a₀ k = Bool.true) :
    tmoves a X = Bool.true := by
  simp only [tmoves, List.all_eq_true]
  intro a₀ ha₀
  obtain ⟨k, hk, hle⟩ := h a₀ ha₀
  simp only [List.any_eq_true]
  exact ⟨k, hk, hle⟩

/-- tyMeetAtom results are union-free singletons of themselves. -/
theorem meetAtom_atoms_self (s t : STy) :
    atoms (tyMeetAtom s t) = [tyMeetAtom s t] := by
  cases s <;> cases t <;>
    simp only [tyMeetAtom, atoms] <;>
    first
      | rfl
      | (split <;> first
          | rfl
          | (simp only [atoms])
          | (simp only [atoms, List.isEmpty_cons, Bool.not_false]))

/-- Elements of a kept list appear among the atoms of its union. -/
theorem ofAtoms_mem (L : List STy) (hL : ∀ k ∈ L, atoms k = [k]) :
    ∀ k ∈ L, k ∈ atoms (ofAtoms L) := by
  intro k hk
  cases L with
  | nil => exact absurd hk (by simp)
  | cons x r =>
      cases r with
      | nil =>
          obtain rfl := List.mem_singleton.mp hk
          simp only [ofAtoms]
          rw [hL k (by simp)]
          exact List.mem_singleton.mpr rfl
      | cons y r' =>
          simp only [ofAtoms, atoms, List.mem_flatMap]
          refine ⟨k, hk, ?_⟩
          rw [hL k hk]
          exact List.mem_singleton.mpr rfl

/-- Meet soundness, mask tests (full type level). -/
theorem tmoves_meet_val (a S : STy) (m : Nat) (hne : atomsNE a = Bool.true)
    (hS : tmoves a S = Bool.true) (hm : tmoves a (STy.anyValue m) = Bool.true) :
    tmoves a (tyMeet S (STy.anyValue m)) = Bool.true := by
  refine tmoves_intro a _ ?_
  intro a₀ ha₀
  have hn₀ : tyNonempty a₀ = Bool.true :=
    (List.all_eq_true.mp hne) a₀ ha₀
  have hS' := (List.all_eq_true.mp hS) a₀ ha₀
  simp only [List.any_eq_true] at hS'
  obtain ⟨s₀, hs₀, hle₀⟩ := hS'
  have hm₀ : tmovesAtom a₀ (STy.anyValue m) = Bool.true := by
    have hany := (List.all_eq_true.mp hm) a₀ ha₀
    simp only [List.any_eq_true] at hany
    obtain ⟨b, hb, hbe⟩ := hany
    have hbv : b = STy.anyValue m := by
      cases b with
      | anyValue n =>
          exact List.mem_singleton.mp (by simpa only [atoms] using hb)
      | isValue _ | oneOf _ | desc _ | descAny | notPresent
      | union _ | complN _ | complT =>
          exact absurd hb (by simp [atoms])
    subst hbv
    exact hbe
  have hgrid := tmovesAtom_meet_val a₀ s₀ m hle₀ hm₀
  have hkeep : tyNonempty (tyMeetAtom s₀ (STy.anyValue m)) = Bool.true :=
    tmovesAtom_le_ne _ _ hgrid hn₀
  refine ⟨tyMeetAtom s₀ (STy.anyValue m), ?_, hgrid⟩
  have hself := meetAtom_atoms_self s₀ (STy.anyValue m)
  have hLcond : ∀ k ∈ (atoms S).flatMap
      (fun s => (atoms (STy.anyValue m)).filterMap
        (fun b => let mm := tyMeetAtom s b
                  if tyNonempty mm then some mm else none)),
      atoms k = [k] := by
    intro k hk
    simp only [List.mem_flatMap] at hk
    obtain ⟨s₁, _, hk₁⟩ := hk
    simp only [List.mem_filterMap] at hk₁
    obtain ⟨b, _, hfb⟩ := hk₁
    split at hfb
    · injection hfb with hk'
      subst hk'
      exact meetAtom_atoms_self s₁ b
    · exact absurd hfb (by simp)
  exact ofAtoms_mem _ hLcond _ (by
    simp only [List.mem_flatMap]
    exact ⟨s₀, hs₀, by
      simp only [List.mem_filterMap]
      exact ⟨STy.anyValue m, by simp [atoms], by
        rw [if_pos hkeep]⟩⟩)

/-- Meet soundness for absent-variable tests. -/
theorem tmovesAtom_meet_notPresent (a₀ s₀ : STy)
    (hle : tmovesAtom a₀ s₀ = Bool.true)
    (hm : tmovesAtom a₀ .notPresent = Bool.true) :
    tmovesAtom a₀ (tyMeetAtom s₀ .notPresent) = Bool.true := by
  cases a₀ with
  | notPresent =>
      cases s₀ with
      | notPresent => rfl
      | anyValue _ | isValue _ | oneOf _ | desc _ | descAny
      | union _ | complN _ | complT =>
          simp only [tmovesAtom] at hle; exact Bool.noConfusion hle
  | anyValue _ | isValue _ | oneOf _ | desc _ | descAny
  | union _ | complN _ | complT =>
      simp only [tmovesAtom] at hm; exact Bool.noConfusion hm

/-- Meet soundness for singleton tests, atom level. -/
theorem tmovesAtom_meet_isValue (a₀ s₀ : STy) (w : JSValue)
    (hle : tmovesAtom a₀ s₀ = Bool.true)
    (hm : tmovesAtom a₀ (STy.isValue w) = Bool.true) :
    tmovesAtom a₀ (tyMeetAtom s₀ (STy.isValue w)) = Bool.true := by
  cases s₀ with
  | isValue v =>
      cases a₀ with
      | isValue x =>
          have h1 : x = v := eq_of_beq (by simpa only [tmovesAtom] using hle)
          have h2 : x = w := eq_of_beq (by simpa only [tmovesAtom] using hm)
          have hvw : v = w := by rw [← h1]; exact h2
          rw [hvw] at hle ⊢
          have hxw : x = w := eq_of_beq (by simpa only [tmovesAtom] using hle)
          rw [hxw]
          simp only [tyMeetAtom, beq_self_eq_true, if_true, tmovesAtom,
            beq_self_eq_true]
      | oneOf xs =>
          cases xs with
          | nil =>
              simp only [tyMeetAtom]
              split <;> simp [tmovesAtom]
          | cons x r =>
              have h1 : x = v := eq_of_beq
                ((List.all_eq_true.mp (by simpa only [tmovesAtom] using hle)) x (by simp))
              have h2 : x = w := eq_of_beq
                ((List.all_eq_true.mp (by simpa only [tmovesAtom] using hm)) x (by simp))
              have hvw : v = w := by rw [← h1]; exact h2
              rw [hvw] at hle ⊢
              simp only [tyMeetAtom, beq_self_eq_true, if_true]
              simpa only [tmovesAtom] using hle
      | anyValue _ =>
          simp only [tmovesAtom] at hm; exact Bool.noConfusion hm
      | desc _ | descAny | notPresent | union _ | complN _ | complT =>
          simp only [tmovesAtom] at hle; exact Bool.noConfusion hle
  | anyValue k =>
      cases a₀ with
      | isValue x =>
          have hxw : x = w := eq_of_beq (by simpa only [tmovesAtom] using hm)
          rw [hxw] at hle hm ⊢
          have hcond : (((ctorBit w) &&& k) != 0) = Bool.true := by
            simpa only [tmovesAtom, bne_iff_ne] using hle
          simp only [tyMeetAtom, hcond, if_pos, tmovesAtom, beq_self_eq_true]
      | oneOf xs =>
          cases xs with
          | nil =>
              simp only [tyMeetAtom]
              split <;> simp [tmovesAtom]
          | cons x r =>
              have hxw : x = w := eq_of_beq
                ((List.all_eq_true.mp (by simpa only [tmovesAtom] using hm)) x (by simp))
              rw [hxw] at hle hm ⊢
              have hcond : (((ctorBit w) &&& k) != 0) = Bool.true := by
                have hlek : tmovesAtom (STy.isValue w) (STy.anyValue k) = Bool.true :=
                  (List.all_eq_true.mp (by simpa only [tmovesAtom] using hle)) w
                    (by simp)
                simpa only [tmovesAtom, bne_iff_ne] using hlek
              simp only [tyMeetAtom, hcond, if_pos]
              exact hm
      | anyValue _ =>
          simp only [tmovesAtom] at hm; exact Bool.noConfusion hm
      | desc _ | descAny | notPresent | union _ | complN _ | complT =>
          simp only [tmovesAtom] at hle; exact Bool.noConfusion hle
  | oneOf us =>
      cases a₀ with
      | isValue x =>
          have hxw : x = w := eq_of_beq (by simpa only [tmovesAtom] using hm)
          rw [hxw] at hle hm ⊢
          have hc : us.contains w = Bool.true := by
            simpa only [tmovesAtom] using hle
          simp only [tyMeetAtom, hc, if_pos, tmovesAtom, beq_self_eq_true]
      | oneOf xs =>
          cases xs with
          | nil =>
              simp only [tyMeetAtom]
              split <;> simp [tmovesAtom]
          | cons x r =>
              have hxw : x = w := eq_of_beq
                ((List.all_eq_true.mp (by simpa only [tmovesAtom] using hm)) x (by simp))
              rw [hxw] at hle hm ⊢
              have hc : us.contains w = Bool.true := by
                have hxu : us.contains w = Bool.true :=
                  (List.all_eq_true.mp (by simpa only [tmovesAtom] using hle)) w (by simp)
                exact hxu
              simp only [tyMeetAtom, hc, if_pos]
              exact hm
      | anyValue _ =>
          simp only [tmovesAtom] at hm; exact Bool.noConfusion hm
      | desc _ | descAny | notPresent | union _ | complN _ | complT =>
          simp only [tmovesAtom] at hle; exact Bool.noConfusion hle
  | desc _ | descAny =>
      cases a₀ with
      | desc _ | descAny =>
          simp only [tmovesAtom] at hm; exact Bool.noConfusion hm
      | anyValue _ | isValue _ | oneOf _ | notPresent | union _ | complN _ | complT =>
          simp only [tmovesAtom] at hle; exact Bool.noConfusion hle
  | notPresent =>
      cases a₀ with
      | notPresent =>
          simp only [tmovesAtom] at hm; exact Bool.noConfusion hm
      | anyValue _ | isValue _ | oneOf _ | desc _ | descAny | union _ | complN _ | complT =>
          simp only [tmovesAtom] at hle; exact Bool.noConfusion hle
  | complN _ | complT =>
      cases a₀ with
      | complN _ | complT =>
          simp only [tmovesAtom] at hm; exact Bool.noConfusion hm
      | anyValue _ | isValue _ | oneOf _ | desc _ | descAny | notPresent | union _ =>
          simp only [tmovesAtom] at hle; exact Bool.noConfusion hle
  | union ps =>
      cases a₀ <;> simp only [tmovesAtom] at hle <;> exact Bool.noConfusion hle

/- ## Preservation templates.

    One generic statement per STATE SHAPE; every arm is then an
    instance supplying: the machine-step equation, the new frame's
    certificate, heap-root coverage, and continuation
    well-formedness. Shared stateOk structure is factored into
    extractors so instances never destructure it. -/

theorem machineRet_cons_eq (sigs : SigTable) (f g : Fr) (fs : List Fr)
    (hr : f.ret = g.ret) :
    machineRet sigs (f :: fs) = machineRet sigs (g :: fs) := by
  unfold machineRet
  cases fs with
  | nil =>
      show sigRetTy sigs f.ret = sigRetTy sigs g.ret
      rw [hr]
  | cons x xs => simp only [List.getLast?_cons_cons]

/- ### Extractors -/

theorem stateOk_head_frameOk {sigs : SigTable} {r : STy} {f : Fr}
    {fs : List Fr} {heap : Heap} {nl : Nat}
    (h : stateOk sigs r (FM.frames (f :: fs) heap nl)) :
    frameOk sigs none f := by
  obtain ⟨_, hframes, _, _, _, _⟩ := h
  simp only [framesOk, framesOkFrom] at hframes
  exact hframes.1

theorem stateOk_tail_framesOkFrom {sigs : SigTable} {r : STy} {f : Fr}
    {fs : List Fr} {heap : Heap} {nl : Nat}
    (h : stateOk sigs r (FM.frames (f :: fs) heap nl)) :
    framesOkFrom sigs f.ret fs := by
  obtain ⟨_, hframes, _, _, _, _⟩ := h
  simp only [framesOk, framesOkFrom] at hframes
  exact hframes.2

theorem stateOk_heap_roots {sigs : SigTable} {r : STy} {f : Fr}
    {fs : List Fr} {heap : Heap} {nl : Nat}
    (h : stateOk sigs r (FM.frames (f :: fs) heap nl)) :
    ∀ l ∈ (f.eval.flatMap locsOf ++ (f.env.map Prod.snd).flatMap locsOf),
      l < nl ∧ (heap l).isSome = Bool.true := by
  obtain ⟨_, _, hheap, _, _, _⟩ := h
  exact hheap.1

theorem stateOk_heap_tail {sigs : SigTable} {r : STy} {f : Fr}
    {fs : List Fr} {heap : Heap} {nl : Nat}
    (h : stateOk sigs r (FM.frames (f :: fs) heap nl)) :
    heapOk heap nl fs := by
  obtain ⟨_, _, hheap, _, _, _⟩ := h
  exact hheap.2

theorem stateOk_heapTy {sigs : SigTable} {r : STy} {f : Fr}
    {fs : List Fr} {heap : Heap} {nl : Nat}
    (h : stateOk sigs r (FM.frames (f :: fs) heap nl)) :
    ∃ ht, heapTyOk heap ht nl := by
  obtain ⟨_, _, _, hht, _, _⟩ := h
  exact hht

theorem stateOk_machineRet {sigs : SigTable} {r : STy} {f : Fr}
    {fs : List Fr} {heap : Heap} {nl : Nat}
    (h : stateOk sigs r (FM.frames (f :: fs) heap nl)) :
    machineRet sigs (f :: fs) = r := by
  obtain ⟨_, _, _, _, hret, _⟩ := h
  exact hret

theorem stateOk_framesWf_head {sigs : SigTable} {r : STy} {f : Fr}
    {fs : List Fr} {heap : Heap} {nl : Nat}
    (h : stateOk sigs r (FM.frames (f :: fs) heap nl)) :
    instrsWf heap nl f.stmts := by
  obtain ⟨_, _, _, _, _, hwf⟩ := h
  exact hwf.1

theorem stateOk_framesWf_tail {sigs : SigTable} {r : STy} {f : Fr}
    {fs : List Fr} {heap : Heap} {nl : Nat}
    (h : stateOk sigs r (FM.frames (f :: fs) heap nl)) :
    framesWf heap nl fs := by
  obtain ⟨_, _, _, _, _, hwf⟩ := h
  exact hwf.2

theorem frameOk_flows_elim {sigs : SigTable} {above : Option «String»} {f : Fr}
    (h : frameOk sigs above f) :
    ∃ fb, checkSeq sigs (sigRetTy sigs f.ret)
        [{ Γ := envTyOf f.env, σ := absStack sigs above f }] f.stmts
        = TCResult.flows fb ∧ terminal fb = Bool.true := by
  obtain ⟨_, hc⟩ := h
  cases hb : checkSeq sigs (sigRetTy sigs f.ret)
      [{ Γ := envTyOf f.env, σ := absStack sigs above f }] f.stmts with
  | flows fb =>
      rw [hb] at hc
      exact ⟨fb, rfl, hc⟩
  | reject s w => rw [hb] at hc; exact False.elim hc

theorem frameOk_none_flows (sigs : SigTable) (f : Fr) (fb : Flows)
    (h : checkSeq sigs (sigRetTy sigs f.ret)
        [{ Γ := envTyOf f.env, σ := stackTyOf f.eval }] f.stmts
        = TCResult.flows fb)
    (ht : terminal fb = Bool.true) :
    frameOk sigs none f :=
  ⟨Or.inl Option.isNone_none, by
    have ha : absStack sigs none f = stackTyOf f.eval := rfl
    rw [ha, h]; exact ht⟩

/- ### Masters -/

/-- Frame template: the step rewrites the head frame f to f' (same
    tail, heap, region). Supplies: step equation, same destiny, the
    new certificate, root coverage, continuation well-formedness. -/
theorem subject_reduction_frame (sigs : SigTable) (reg : AOReg) (r : STy)
    (f f' : Fr) (fs : List Fr) (heap : Heap) (nl : Nat)
    (h : stateOk sigs r (FM.frames (f :: fs) heap nl))
    (hstep : fstep reg (FM.frames (f :: fs) heap nl)
      = FM.frames (f' :: fs) heap nl)
    (hreq : f'.ret = f.ret)
    (hcert : frameOk sigs none f')
    (hroots : ∀ l ∈ (f'.eval.flatMap locsOf
        ++ (f'.env.map Prod.snd).flatMap locsOf),
      l < nl ∧ (heap l).isSome = Bool.true)
    (hwfs : instrsWf heap nl f'.stmts) :
    stateOk sigs r (fstep reg (FM.frames (f :: fs) heap nl)) := by
  rw [hstep]
  refine ⟨rfl, ?_, ?_, stateOk_heapTy h, ?_, ?_⟩
  · exact And.intro hcert (by rw [hreq]; exact stateOk_tail_framesOkFrom h)
  · exact And.intro hroots (stateOk_heap_tail h)
  · exact (machineRet_cons_eq sigs f' f fs hreq).trans (stateOk_machineRet h)
  · exact And.intro hwfs (stateOk_framesWf_tail h)

/-- Terminal template: the absorbing answer state. -/
theorem subject_reduction_fdone (sigs : SigTable) (reg : AOReg) (r : STy)
    (v : JSValue) (fs : List Fr) (heap : Heap) (nl n : Nat)
    (h : stateOk sigs r (FM.fdone v fs heap nl n)) :
    stateOk sigs r (fstep reg (FM.fdone v fs heap nl n)) := by
  show stateOk sigs r (FM.fdone v fs heap nl (n + 1))
  exact h

/-- Vacuous templates: states the invariant already rules out. -/
theorem subject_reduction_absurd_fell (sigs : SigTable) (reg : AOReg) (r : STy)
    (fs : List Fr) (heap : Heap) (nl n : Nat)
    (h : stateOk sigs r (FM.fell fs heap nl n)) :
    stateOk sigs r (fstep reg (FM.fell fs heap nl n)) :=
  False.elim h

theorem subject_reduction_absurd_nil (sigs : SigTable) (reg : AOReg) (r : STy)
    (heap : Heap) (nl : Nat)
    (h : stateOk sigs r (FM.frames [] heap nl)) :
    stateOk sigs r (fstep reg (FM.frames [] heap nl)) := by
  obtain ⟨hne, _⟩ := h
  exact absurd hne (by simp)

/- ### Instances -/

/-- The const-literal push, through the template: the certificate
    carries over the unfolding identity; nothing else remains. -/
theorem subject_reduction_kEval_const (sigs : SigTable) (reg : AOReg) (r : STy)
    (env : Env) (eval : List JSValue) (ret : «String»)
    (fs : List Fr) (heap : Heap) (nl : Nat)
    (rest : List Instr) (v : JSValue)
    (h : stateOk sigs r (FM.frames
        (⟨.kEval (.const v) :: rest, env, eval, ret⟩ :: fs) heap nl)) :
    stateOk sigs r (fstep reg (FM.frames
        (⟨.kEval (.const v) :: rest, env, eval, ret⟩ :: fs) heap nl)) := by
  obtain ⟨fb, hb, ht⟩ := frameOk_flows_elim (stateOk_head_frameOk h)
  have ha : absStack sigs none (⟨.kEval (.const v) :: rest, env, eval, ret⟩ : Fr)
      = stackTyOf eval := rfl
  rw [ha, checkSeq_kEval_const sigs (sigRetTy sigs ret)
      { Γ := envTyOf env, σ := stackTyOf eval } rest v] at hb
  obtain ⟨hhd, hrest⟩ := stateOk_framesWf_head h
  exact subject_reduction_frame sigs reg r _ ⟨rest, env, v :: eval, ret⟩ fs heap nl
    h rfl rfl (frameOk_none_flows _ _ fb hb ht)
    (by intro l hl
        simp only [List.flatMap_cons, List.append_assoc, List.mem_append] at hl
        rcases hl with hl | hl
        · exact hhd l hl
        · exact (stateOk_heap_roots h) l
            (List.mem_append.mpr hl : l ∈ (List.flatMap locsOf eval
              ++ List.flatMap locsOf (List.map Prod.snd env))))
    hrest

/- ## Preservation status ledger.

    PROVEN (exact-match family - the runtime world after the step IS
    the certificate's own continuation world; no monotonicity needed):
    * step_pres_kEval_const          (the template case)

    NOT YET PROVEN - collected with the missing ingredient:

    Exact-match, template-extractable (the identities exist; packaging
    into a common step_pres_exact master hit record-projection /
    anonymous-constructor whnf friction - mechanical, next session):
    * kEval (nat n)      identity: checkSeq_kEval_nat (proven)
    * kPrim1 pWrapC      identity: new (needs stepWorlds pWrapC unfold)
    * kUnwrap            identity: new (normal completions only; the
                         machine arm accepts abrupt compls whose static
                         twin is the dead val anyV path)
    * kPop               identity: checkSeq_kPop (proven)
    * kSet x             identity: checkSeq_kSet (proven); envTyOf cons
    * kRet (bottom frame pops to fdone): extraction from the kRet-arm's
                         payload check (tmoves p r where typeOfV v =
                         complN p); the machineRet is the frame destiny
    * fdone/fell absorbing steps, frames-nil, stmts-nil: vacuous/trivial
    * kEval (nv x) with lookup = some v: identity needs envTyOf_lookup
                         INSIDE the mapM-pushed world (mapM-singleton
                         beta before the tyLookup rewrite); unbound is
                         vacuous via the checker's reject

    Refinement cases (need the realization invariant / checkSeq_mono,
    powered by tmoves_meet_val + the remove side still to come):
    * kPrim1 p for p != pWrapC: checker pushes val boolV, machine holds
      isValue (boolean b) - a strict refinement, not equality
    * kEval (varNotPresent x): same val boolV vs singleton boolean
    * kTest: verdict val cFalse/cTrue vs isValue (boolean abrupt)
    * kIte: dispatch precision (both-verdict worlds split by the checker)
    * kMkList: val cList vs isValue (listV vs)
    * kNewSlot: val cObj vs isValue (obj nl) + heap-extension lemmas
    * kAssert: true-branch continuation under the refined verdict
    * kRet with caller frames: in-flight delivery refinement
      (complN p ⊑ complN (sigRetTy callee))

    Expansion cases (machine rewrites kEval e into sub-evaluation
    instruction lists; the checker instead splits worlds or consults
    the signature - needs the world-set realization argument over the
    EXPANDED prefix):
    * kEval e for the is-family tests (isObject, isU, isType, ...):
      machine: kEval e' :: kPrim1 p :: rest; checker: splitWorlds
    * kEval (call f args): arg decomposition + kCall + kTest/kIte
      self-test idiom; callee frames via registryCertified (V ts ⊑ ps)
    * kEval (imeth ...): MOP dispatch; OrdinaryGet via registry
    * kEval (ifield ...): pDescField result typing
    * kEval (listE es): element decomposition + kMkList

    Loop family (stack neutrality under refinement):
    * kRepeatWhile / kRepeatTest / kForStart / kForBody
-/

/- ## The per-state interface: "subject reduction holds at t".

    Each machine arm is stated as SR applied to its concrete state
    shape; the final theorem is then plain case analysis:

      theorem subject_reduction (sigs reg r) : ∀ m, SR sigs reg r m := by
        intro m
        match m with
        | .fdone v fs heap nl n        => exact sr_fdone …
        | .fell fs heap nl n           => exact sr_fell …
        | .frames [] heap nl           => exact sr_nil …
        | .frames (f :: fs) heap nl    =>
            match f.stmts, f.env, f.eval with
            | .kEval (.const v) :: rest, env, eval =>
                exact sr_kEval_const …
            | …                         => exact sr_<arm> …
-/

/-- Subject reduction holds at t: the state typing is preserved by one
    step FROM t. The registry side conditions are part of the
    predicate: reg must be certified (every entry's body typechecks at
    its declared signature, for every argument typing below the
    parameter types - this makes freshly pushed callee frames frameOk)
    and closed (every name the signatures may call is answered by reg
    or natively, and the MOP-Get dispatch target exists - this keeps
    kCall/kIMeth steps from falling to the ill-typed fell state).
    Without these, fstep's findAO lookups can fail and preservation is
    false for a garbage registry. -/
def SR (sigs : SigTable) (reg : AOReg) (r : STy) (m : FM) : Prop :=
  registryCertified sigs reg → closedRegistry sigs reg →
    stateOk sigs r m → stateOk sigs r (fstep reg m)

theorem sr_fdone (sigs : SigTable) (reg : AOReg) (r : STy)
    (v : JSValue) (fs : List Fr) (heap : Heap) (nl n : Nat) :
    SR sigs reg r (FM.fdone v fs heap nl n) :=
  fun _ _ h => subject_reduction_fdone sigs reg r v fs heap nl n h

theorem sr_fell (sigs : SigTable) (reg : AOReg) (r : STy)
    (fs : List Fr) (heap : Heap) (nl n : Nat) :
    SR sigs reg r (FM.fell fs heap nl n) :=
  fun _ _ h => subject_reduction_absurd_fell sigs reg r fs heap nl n h

theorem sr_nil (sigs : SigTable) (reg : AOReg) (r : STy)
    (heap : Heap) (nl : Nat) :
    SR sigs reg r (FM.frames [] heap nl) :=
  fun _ _ h => subject_reduction_absurd_nil sigs reg r heap nl h

theorem sr_kEval_const (sigs : SigTable) (reg : AOReg) (r : STy)
    (env : Env) (eval : List JSValue) (ret : «String»)
    (fs : List Fr) (heap : Heap) (nl : Nat)
    (rest : List Instr) (v : JSValue) :
    SR sigs reg r (FM.frames
      (⟨.kEval (.const v) :: rest, env, eval, ret⟩ :: fs) heap nl) :=
  fun _ _ h => subject_reduction_kEval_const sigs reg r env eval ret
    fs heap nl rest v h

/- ## Plumbing for the call family. -/

theorem leList_length : ∀ (as bs : List STy), leList as bs = Bool.true →
    as.length = bs.length := by
  intro as bs h
  induction as generalizing bs with
  | nil =>
      cases bs with
      | nil => rfl
      | cons b bs' => exact absurd h (by simp [leList])
  | cons a rest ih =>
      cases bs with
      | nil => exact absurd h (by simp [leList])
      | cons b bs' =>
          simp only [leList, Bool.and_eq_true] at h
          have h3 := ih bs' h.2
          simp only [List.length_cons]
          omega

theorem leList_snoc {xs ys : List STy} {a b : STy} :
    leList (xs ++ [a]) (ys ++ [b]) = (tmoves a b && leList xs ys) := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys' => simp [leList]
  | cons x xs' ih =>
      cases ys with
      | nil => simp [leList]
      | cons y ys' =>
          simp only [List.cons_append, leList, ih]
          simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]

theorem leList_nil_false (X : List STy) (h : X ≠ []) :
    leList [] X = Bool.false := by
  cases X with
  | nil => exact absurd rfl h
  | cons x xs => rfl

theorem rev_cons_ne_nil {α : Type} (b : α) (bs : List α) :
    (b :: bs).reverse ≠ [] := by
  intro hc
  have h1 : (b :: bs).reverse.length = (b :: bs).length := List.length_reverse
  rw [hc] at h1
  simp at h1

theorem leList_cons_nil_false (X : List STy) (h : X ≠ []) :
    leList X [] = Bool.false := by
  cases X with
  | nil => exact absurd rfl h
  | cons x xs => rfl

theorem leList_rev_cancel : ∀ (as bs : List STy),
    leList as.reverse bs.reverse = leList as bs := by
  intro as bs
  induction as generalizing bs with
  | nil =>
      cases bs with
      | nil => simp [List.reverse_nil]
      | cons b bs' =>
          simp only [List.reverse_nil]
          rw [leList_nil_false _ (rev_cons_ne_nil b bs'),
            leList_nil_false _ (by simp)]
  | cons a rest ih =>
      cases bs with
      | nil =>
          simp only [List.reverse_nil]
          rw [leList_cons_nil_false _ (rev_cons_ne_nil a rest),
            leList_cons_nil_false _ (by simp)]
      | cons b bs' =>
          rw [List.reverse_cons, List.reverse_cons, leList_snoc, ih, leList]

theorem list_map_take {α β : Type} (f : α → β) : ∀ (l : List α) (n : Nat),
    (l.take n).map f = (l.map f).take n := by
  intro l n
  induction l generalizing n with
  | nil => simp [List.take_nil]
  | cons a rest ih =>
      cases n with
      | zero => rfl
      | succ m =>
          rw [List.take_cons (Nat.succ_pos m)]
          simp only [List.map_cons, List.take_cons (Nat.succ_pos m),
            Nat.succ_sub_one]
          exact congrArg _ (ih m)

theorem list_map_drop {α β : Type} (f : α → β) : ∀ (l : List α) (n : Nat),
    (l.drop n).map f = (l.map f).drop n := by
  intro l n
  induction l generalizing n with
  | nil => simp [List.drop_nil]
  | cons a rest ih =>
      cases n with
      | zero => rfl
      | succ m =>
          rw [List.drop_cons (Nat.succ_pos m)]
          simp only [List.map_cons, List.drop_cons (Nat.succ_pos m),
            Nat.succ_sub_one]
          exact ih m

theorem stackTyOf_take (l : List JSValue) (n : Nat) :
    (stackTyOf l).take n = stackTyOf (l.take n) := by
  simp only [stackTyOf, list_map_take]

theorem stackTyOf_drop (l : List JSValue) (n : Nat) :
    (stackTyOf l).drop n = stackTyOf (l.drop n) := by
  simp only [stackTyOf, list_map_drop]

theorem envTyOf_zip : ∀ (ps : List «String») (vs : List JSValue),
    envTyOf (ps.zip vs) = zipTy ps (vs.map typeOfV) := by
  intro ps vs
  induction ps generalizing vs with
  | nil => cases vs <;> rfl
  | cons p rest ih =>
      cases vs with
      | nil => rfl
      | cons v vs' =>
          show (p, typeOfV v) :: envTyOf (rest.zip vs')
            = (p, typeOfV v) :: zipTy rest (vs'.map typeOfV)
          rw [ih vs']

theorem findAO_mem : ∀ (reg : AOReg) (name : «String») (ps : List «String»)
    (prog : Prog), findAO reg name = some (ps, prog) → (name, (ps, prog)) ∈ reg := by
  intro reg name ps prog h
  induction reg with
  | nil =>
      simp only [findAO] at h
      exact absurd h (by simp)
  | cons e rest ih =>
      rcases e with ⟨en, ee⟩
      simp only [findAO] at h
      by_cases hn : (en == name) = Bool.true
      · rw [if_pos hn] at h
        injection h with hv
        subst hv
        exact List.mem_cons.mpr (Or.inl (by rw [← eq_of_beq hn]))
      · rw [if_neg hn] at h
        right
        exact ih h

theorem mem_of_mem_take {α : Type} (n : Nat) : ∀ (l : List α) (a : α),
    a ∈ l.take n → a ∈ l := by
  induction n with
  | zero => intro l a h; simp at h
  | succ m ih =>
      intro l a h
      cases l with
      | nil => simp at h
      | cons b rest =>
          simp only [List.take_cons (Nat.succ_pos m), Nat.succ_sub_one,
            List.mem_cons] at h
          rcases h with rfl | h
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (ih rest a h)

theorem mem_of_mem_drop {α : Type} (n : Nat) : ∀ (l : List α) (a : α),
    a ∈ l.drop n → a ∈ l := by
  induction n with
  | zero => intro l a h; exact h
  | succ m ih =>
      intro l a h
      cases l with
      | nil => simp at h
      | cons b rest =>
          simp only [List.drop_cons (Nat.succ_pos m), Nat.succ_sub_one] at h
          exact List.mem_cons_of_mem _ (ih rest a h)

theorem mem_of_mem_zip_snd {α β : Type} : ∀ (ps : List α) (vs : List β)
    (p : α × β), p ∈ ps.zip vs → p.2 ∈ vs := by
  intro ps vs p h
  induction ps generalizing vs with
  | nil => cases vs <;> simp at h
  | cons q ps' ih =>
      cases vs with
      | nil => simp at h
      | cons v vs' =>
          rcases List.mem_cons.mp h with h | h
          · rw [h]
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih vs' h)

theorem list_map_reverse {α β : Type} (f : α → β) : ∀ (l : List α),
    (l.reverse).map f = (l.map f).reverse := by
  intro l
  induction l with
  | nil => rfl
  | cons a rest ih =>
      simp [List.reverse_cons, List.map_append, ih]

theorem machineRet_push (sigs : SigTable) (callee caller caller' : Fr)
    (fs : List Fr) (hr : caller'.ret = caller.ret) :
    machineRet sigs (callee :: caller' :: fs) = machineRet sigs (caller :: fs) := by
  unfold machineRet
  cases fs with
  | nil =>
      rw [List.getLast?_cons_cons, List.getLast?_singleton, List.getLast?_singleton]
      exact congrArg (sigRetTy sigs) hr
  | cons x xs => rfl

/- ## The call identity and the push master. -/

theorem checkSeq_kCall (sigs : SigTable) (rr : STy) (w : World)
    (ps : List STy) (ret : STy) (fname : «String») (n : Nat) (rest : List Instr)
    (hsig : sigFind sigs fname = some (ps, ret))
    (hlen : (ps.length == n) = Bool.true)
    (hpops : popArgs ps w.σ = Bool.true) :
    checkSeq sigs rr [w] (.kCall fname n :: rest)
      = checkSeq sigs rr [{ w with σ := .complN ret :: w.σ.drop n }] rest := by
  simp only [checkSeq, stepWorlds, hsig, hlen, hpops,
    List.all_cons, List.all_nil, Bool.and_true]
  rfl

theorem subject_reduction_push (sigs : SigTable) (reg : AOReg) (r : STy)
    (callee caller caller' : Fr) (fs : List Fr) (heap : Heap) (nl : Nat)
    (h : stateOk sigs r (FM.frames (caller :: fs) heap nl))
    (hstep : fstep reg (FM.frames (caller :: fs) heap nl)
      = FM.frames (callee :: caller' :: fs) heap nl)
    (hreq : caller'.ret = caller.ret)
    (hcertc : frameOk sigs none callee)
    (hcert2 : frameOk sigs (some callee.ret) caller')
    (hrootsC : ∀ l ∈ (callee.eval.flatMap locsOf
        ++ (callee.env.map Prod.snd).flatMap locsOf),
      l < nl ∧ (heap l).isSome = Bool.true)
    (hrootsC' : ∀ l ∈ (caller'.eval.flatMap locsOf
        ++ (caller'.env.map Prod.snd).flatMap locsOf),
      l < nl ∧ (heap l).isSome = Bool.true)
    (hwfs : instrsWf heap nl callee.stmts)
    (hwfs' : instrsWf heap nl caller'.stmts) :
    stateOk sigs r (fstep reg (FM.frames (caller :: fs) heap nl)) := by
  rw [hstep]
  refine ⟨rfl, ?_, ?_, stateOk_heapTy h, ?_, ?_⟩
  · simp only [framesOk, framesOkFrom]
    exact And.intro hcertc
      (And.intro hcert2 (by rw [hreq]; exact stateOk_tail_framesOkFrom h))
  · simp only [heapOk]
    exact And.intro hrootsC (And.intro hrootsC' (stateOk_heap_tail h))
  · exact (machineRet_push sigs callee caller caller' fs hreq).trans
      (stateOk_machineRet h)
  · exact ⟨hwfs, hwfs', stateOk_framesWf_tail h⟩

/-- The call dispatch: THE registry-consuming arm. The callee frame is
    certified by registryCertified at the ACTUAL argument abstractions
    (the canonical world makes them coincide with the static stack);
    the caller's continuation certificate carries over the kCall
    identity; the caller re-enters with the in-flight completion typed
    by the callee's destiny, and its remaining stmts are exactly the
    self-test idiom the delivery protocol demands. -/
theorem sr_kCall (sigs : SigTable) (reg : AOReg) (r : STy)
    (env : Env) (eval : List JSValue) (ret : «String»)
    (fs : List Fr) (heap : Heap) (nl : Nat)
    (rest₀ : List Instr) (fname : «String») (n : Nat)
    (ps : List STy) (retsig : STy) (regps : List «String») (body : Prog)
    (hsig : sigFind sigs fname = some (ps, retsig))
    (hnp : ps.length = n)
    (hle : leList (((eval.take n).reverse).map typeOfV) ps)
    (hfind : findAO reg fname = some (regps, body)) :
    SR sigs reg r (FM.frames
      (⟨.kCall fname n :: .kTest :: .kIte [.kRet] [.kUnwrap] :: rest₀,
        env, eval, ret⟩ :: fs) heap nl) := by
  intro hreg _ h
  have hll : (eval.take n).length = ps.length := by
    have h2 := leList_length _ _ hle
    simpa using h2
  have hge : ¬ (eval.length < n) := by
    have h3 : Nat.min n eval.length = ps.length := by
      rw [← hll, List.length_take]
    have h5 : n ≤ eval.length := by
      calc n = ps.length := hnp.symm
        _ = Nat.min n eval.length := h3.symm
        _ ≤ eval.length := Nat.min_le_right n eval.length
    exact Nat.not_lt.mpr h5
  have hstep : fstep reg (FM.frames
      (⟨.kCall fname n :: .kTest :: .kIte [.kRet] [.kUnwrap] :: rest₀,
        env, eval, ret⟩ :: fs) heap nl)
      = FM.frames (⟨compileSteps body, regps.zip (eval.take n).reverse, [], fname⟩
          :: ⟨.kTest :: .kIte [.kRet] [.kUnwrap] :: rest₀, env, eval.drop n, ret⟩
          :: fs) heap nl := by
    simp only [fstep, if_neg hge, hfind]
  obtain ⟨fb, hb0, ht⟩ := frameOk_flows_elim (stateOk_head_frameOk h)
  have ha : absStack sigs none
      (⟨.kCall fname n :: .kTest :: .kIte [.kRet] [.kUnwrap] :: rest₀,
        env, eval, ret⟩ : Fr) = stackTyOf eval := rfl
  rw [ha] at hb0
  have hpops : popArgs ps (stackTyOf eval) = Bool.true := by
    have h3 : Nat.min n eval.length = ps.length := by
      rw [← hll, List.length_take]
    simp only [popArgs, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · have h1 : (stackTyOf eval).length = eval.length := by simp [stackTyOf]
      have h3 : Nat.min n eval.length = ps.length := by
        rw [← hll, List.length_take]
      calc (stackTyOf eval).length = eval.length := h1
        _ ≥ Nat.min n eval.length := Nat.min_le_right n eval.length
        _ = ps.length := h3
    · rw [hnp, stackTyOf_take]
      simp only [stackTyOf, ← list_map_reverse]
      exact hle
  rw [checkSeq_kCall sigs _ _ ps retsig fname n _ hsig (by simpa using hnp) hpops,
    stackTyOf_drop] at hb0
  have hsr : sigRetTy sigs fname = retsig := by simp only [sigRetTy, hsig]
  have hcert2 : frameOk sigs (some fname)
      ⟨.kTest :: .kIte [.kRet] [.kUnwrap] :: rest₀, env, eval.drop n, ret⟩ := by
    refine ⟨Or.inr rfl, ?_⟩
    have habs : absStack sigs (some fname)
        (⟨.kTest :: .kIte [.kRet] [.kUnwrap] :: rest₀, env, eval.drop n, ret⟩ : Fr)
        = .complN retsig :: stackTyOf (eval.drop n) := by
      simp only [absStack, inflight, List.cons_append, List.nil_append, hsr]
    show (match checkSeq sigs (sigRetTy sigs ret)
            [{ Γ := envTyOf env,
               σ := absStack sigs (some fname)
                 ⟨.kTest :: .kIte [.kRet] [.kUnwrap] :: rest₀, env, eval.drop n, ret⟩ }]
            (.kTest :: .kIte [.kRet] [.kUnwrap] :: rest₀) with
      | .flows fb => terminal fb = Bool.true
      | _ => False)
    rw [habs, hb0]
    exact ht
  obtain ⟨hwfbody, hcertgen⟩ :=
    hreg fname regps body (findAO_mem reg fname regps body hfind)
  have hts : leList (((eval.take n).reverse).map typeOfV)
      (sigParams sigs fname) := by
    have hp : sigParams sigs fname = ps := by simp only [sigParams, hsig]
    rw [hp]
    exact hle
  obtain ⟨fb2, hb2, ht2⟩ := certifies_flows_elim (hcertgen _ hts)
  have hcertc : frameOk sigs none
      ⟨compileSteps body, regps.zip (eval.take n).reverse, [], fname⟩ := by
    refine ⟨Or.inl Option.isNone_none, ?_⟩
    rw [envTyOf_zip,
      show absStack sigs none
        (⟨compileSteps body, regps.zip (eval.take n).reverse, [], fname⟩ : Fr)
        = ([] : List STy) from rfl, hb2]
    exact ht2
  refine subject_reduction_push sigs reg r
    ⟨compileSteps body, regps.zip (eval.take n).reverse, [], fname⟩
    ⟨.kCall fname n :: .kTest :: .kIte [.kRet] [.kUnwrap] :: rest₀, env, eval, ret⟩
    ⟨.kTest :: .kIte [.kRet] [.kUnwrap] :: rest₀, env, eval.drop n, ret⟩
    fs heap nl h hstep rfl hcertc hcert2 ?_ ?_ (hwfbody heap nl) ?_
  · intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact absurd hl (by simp)
    · obtain ⟨v, hv, hlv⟩ := List.mem_flatMap.mp hl
      have hvp : v ∈ (regps.zip (eval.take n).reverse).map Prod.snd := hv
      obtain ⟨p, hp, hp2⟩ := List.mem_map.mp hvp
      have hv2 : v ∈ (eval.take n).reverse := by
        rw [← hp2]
        exact mem_of_mem_zip_snd _ _ _ hp
      have hv3 : v ∈ eval.take n := List.mem_reverse.mp hv2
      refine (stateOk_heap_roots h) l (List.mem_append.mpr (Or.inl ?_))
      exact List.mem_flatMap.mpr ⟨v, mem_of_mem_take n eval v hv3, hlv⟩
  · intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨v, hv, hlv⟩ := List.mem_flatMap.mp hl
      refine (stateOk_heap_roots h) l (List.mem_append.mpr (Or.inl ?_))
      exact List.mem_flatMap.mpr ⟨v, mem_of_mem_drop n eval v hv, hlv⟩
    · exact (stateOk_heap_roots h) l (List.mem_append.mpr (Or.inr hl))
  · obtain ⟨_, hr2⟩ := stateOk_framesWf_head h
    exact hr2

/- ### More exact-match arms through the frame template. -/

theorem sr_kEval_nat (sigs : SigTable) (reg : AOReg) (r : STy)
    (env : Env) (eval : List JSValue) (ret : «String»)
    (fs : List Fr) (heap : Heap) (nl : Nat)
    (rest : List Instr) (n : Nat)
    (h : stateOk sigs r (FM.frames
        (⟨.kEval (.nat n) :: rest, env, eval, ret⟩ :: fs) heap nl)) :
    SR sigs reg r (FM.frames
        (⟨.kEval (.nat n) :: rest, env, eval, ret⟩ :: fs) heap nl) := by
  intro hreg _ hst
  obtain ⟨fb, hb, ht⟩ := frameOk_flows_elim (stateOk_head_frameOk hst)
  have ha : absStack sigs none
      (⟨.kEval (.nat n) :: rest, env, eval, ret⟩ : Fr) = stackTyOf eval := rfl
  rw [ha, checkSeq_kEval_nat sigs (sigRetTy sigs ret)
      { Γ := envTyOf env, σ := stackTyOf eval } rest n] at hb
  obtain ⟨hhd, hrest⟩ := stateOk_framesWf_head hst
  exact subject_reduction_frame sigs reg r _
    ⟨rest, env, .number ↑n :: eval, ret⟩ fs heap nl hst rfl rfl
    (frameOk_none_flows _ _ fb hb ht)
    (by intro l hl
        rcases List.mem_append.mp hl with hl | hl
        · obtain ⟨w, hw, hlw⟩ := List.mem_flatMap.mp hl
          refine (stateOk_heap_roots hst) l (List.mem_append.mpr (Or.inl ?_))
          refine List.mem_flatMap.mpr ⟨w, ?_, hlw⟩
          rcases List.mem_cons.mp hw with rfl | hw'
          · exact absurd hlw (by simp [locsOf])
          · exact hw'
        · exact (stateOk_heap_roots hst) l (List.mem_append.mpr (Or.inr hl)))
    hrest

theorem sr_kPop (sigs : SigTable) (reg : AOReg) (r : STy)
    (env : Env) (eval : List JSValue) (ret : «String»)
    (fs : List Fr) (heap : Heap) (nl : Nat)
    (rest : List Instr) (v : JSValue)
    (h : stateOk sigs r (FM.frames
        (⟨.kPop :: rest, env, v :: eval, ret⟩ :: fs) heap nl)) :
    SR sigs reg r (FM.frames
        (⟨.kPop :: rest, env, v :: eval, ret⟩ :: fs) heap nl) := by
  intro hreg _ hst
  obtain ⟨fb, hb, ht⟩ := frameOk_flows_elim (stateOk_head_frameOk hst)
  have ha : absStack sigs none
      (⟨.kPop :: rest, env, v :: eval, ret⟩ : Fr)
      = typeOfV v :: stackTyOf eval := rfl
  rw [ha, checkSeq_kPop sigs (sigRetTy sigs ret)
      { Γ := envTyOf env, σ := typeOfV v :: stackTyOf eval } rest
      (typeOfV v) (stackTyOf eval)] at hb
  obtain ⟨hhd, hrest⟩ := stateOk_framesWf_head hst
  exact subject_reduction_frame sigs reg r _
    ⟨rest, env, eval, ret⟩ fs heap nl hst rfl rfl
    (frameOk_none_flows _ _ fb hb ht)
    (by intro l hl
        rcases List.mem_append.mp hl with hl | hl
        · obtain ⟨w, hw, hlw⟩ := List.mem_flatMap.mp hl
          refine (stateOk_heap_roots hst) l (List.mem_append.mpr (Or.inl ?_))
          refine List.mem_flatMap.mpr ⟨w, ?_, hlw⟩
          exact List.mem_cons_of_mem _ hw
        · exact (stateOk_heap_roots hst) l (List.mem_append.mpr (Or.inr hl)))
    hrest

theorem sr_kSet (sigs : SigTable) (reg : AOReg) (r : STy)
    (env : Env) (eval : List JSValue) (ret : «String»)
    (fs : List Fr) (heap : Heap) (nl : Nat)
    (rest : List Instr) (x : «String») (v : JSValue)
    (h : stateOk sigs r (FM.frames
        (⟨.kSet x :: rest, env, v :: eval, ret⟩ :: fs) heap nl)) :
    SR sigs reg r (FM.frames
        (⟨.kSet x :: rest, env, v :: eval, ret⟩ :: fs) heap nl) := by
  intro hreg _ hst
  obtain ⟨fb, hb, ht⟩ := frameOk_flows_elim (stateOk_head_frameOk hst)
  have ha : absStack sigs none
      (⟨.kSet x :: rest, env, v :: eval, ret⟩ : Fr)
      = typeOfV v :: stackTyOf eval := rfl
  rw [ha, checkSeq_kSet sigs (sigRetTy sigs ret)
      { Γ := envTyOf env, σ := typeOfV v :: stackTyOf eval } rest x
      (typeOfV v) (stackTyOf eval)] at hb
  simp only at hb
  obtain ⟨hhd, hrest⟩ := stateOk_framesWf_head hst
  have hcert2 : frameOk sigs none ⟨rest, (x, v) :: env, eval, ret⟩ := by
    refine ⟨Or.inl Option.isNone_none, ?_⟩
    show (match checkSeq sigs (sigRetTy sigs ret)
        [{ Γ := envTyOf ((x, v) :: env), σ := stackTyOf eval }] rest with
      | .flows fb => terminal fb = Bool.true
      | _ => False)
    have hE : ({ Γ := envTyOf ((x, v) :: env), σ := stackTyOf eval } : World)
        = { Γ := (x, typeOfV v) :: envTyOf env,
            σ := stackTyOf eval } := by
      simp only [envTyOf_cons]
    rw [hE, hb]
    exact ht
  refine subject_reduction_frame sigs reg r _ ⟨rest, (x, v) :: env, eval, ret⟩
    fs heap nl hst rfl rfl hcert2 ?_ hrest
  intro l hl
  rcases List.mem_append.mp hl with hl | hl
  · obtain ⟨w, hw, hlw⟩ := List.mem_flatMap.mp hl
    have hw' : w ∈ eval := hw
    refine (stateOk_heap_roots hst) l (List.mem_append.mpr (Or.inl
      (List.mem_flatMap.mpr ⟨w, List.mem_cons_of_mem v hw', hlw⟩)))
  · rw [List.map_cons, List.flatMap_cons] at hl
    rcases List.mem_append.mp hl with hl | hl'
    · exact (stateOk_heap_roots hst) l (List.mem_append.mpr (Or.inl
        (List.mem_flatMap.mpr ⟨v, List.mem_cons_self .., hl⟩)))
    · exact (stateOk_heap_roots hst) l (List.mem_append.mpr (Or.inr hl'))

/- ### Remaining exact-match arms. -/

theorem checkSeq_kPrim1_pWrapC (sigs : SigTable) (rr : STy) (w : World)
    (rest : List Instr) (t : STy) (σ : List STy) :
    checkSeq sigs rr [{ w with σ := t :: σ }] (.kPrim1 .pWrapC :: rest)
      = checkSeq sigs rr [{ w with σ := .complN t :: σ }] rest := by
  simp [checkSeq, stepWorlds]

theorem checkSeq_kUnwrap (sigs : SigTable) (rr : STy) (w : World)
    (rest : List Instr) (t : STy) (σ : List STy) :
    checkSeq sigs rr [{ w with σ := .complN t :: σ }] (.kUnwrap :: rest)
      = checkSeq sigs rr [{ w with σ := t :: σ }] rest := by
  simp [checkSeq, stepWorlds]

theorem checkSeq_kEval_nv (sigs : SigTable) (rr : STy) (env : Env)
    (eval : List JSValue) (rest : List Instr) (x : «String») (v : JSValue)
    (hl : lookup env x = some v) :
    checkSeq sigs rr [{ Γ := envTyOf env, σ := stackTyOf eval }]
        (.kEval (.nv x) :: rest)
      = checkSeq sigs rr
        [{ Γ := envTyOf env, σ := typeOfV v :: stackTyOf eval }] rest := by
  simp only [checkSeq, testType, typeOfE]
  rw [if_neg (by simp)]
  simp only [List.mapM_cons]
  have hty : tyLookup (envTyOf env) x = some (typeOfV v) := by
    rw [← envTyOf_lookup, hl]
    rfl
  rw [hty]
  rfl

theorem sr_kPrim1_pWrapC (sigs : SigTable) (reg : AOReg) (r : STy)
    (env : Env) (eval : List JSValue) (ret : «String»)
    (fs : List Fr) (heap : Heap) (nl : Nat)
    (rest : List Instr) (v : JSValue)
    (h : stateOk sigs r (FM.frames
        (⟨.kPrim1 .pWrapC :: rest, env, v :: eval, ret⟩ :: fs) heap nl)) :
    SR sigs reg r (FM.frames
        (⟨.kPrim1 .pWrapC :: rest, env, v :: eval, ret⟩ :: fs) heap nl) := by
  intro hreg _ hst
  obtain ⟨fb, hb, ht⟩ := frameOk_flows_elim (stateOk_head_frameOk hst)
  have ha : absStack sigs none
      (⟨.kPrim1 .pWrapC :: rest, env, v :: eval, ret⟩ : Fr)
      = typeOfV v :: stackTyOf eval := rfl
  rw [ha, checkSeq_kPrim1_pWrapC sigs (sigRetTy sigs ret)
      { Γ := envTyOf env, σ := stackTyOf eval } rest (typeOfV v)
      (stackTyOf eval)] at hb
  obtain ⟨hhd, hrest⟩ := stateOk_framesWf_head hst
  refine subject_reduction_frame sigs reg r _
    ⟨rest, env, .compl Bool.false v :: eval, ret⟩
    fs heap nl hst rfl rfl (frameOk_none_flows _ _ fb hb ht) ?_ hrest
  intro l hl
  rcases List.mem_append.mp hl with hl | hl
  · obtain ⟨w, hw, hlw⟩ := List.mem_flatMap.mp hl
    have hw0 : w ∈ (.compl Bool.false v :: eval : List JSValue) :=
      (show w ∈ (.compl Bool.false v :: eval : List JSValue) from hw)
    rcases List.mem_cons.mp hw0 with heq | hw'
    · rw [heq, locsOf_compl] at hlw
      exact (stateOk_heap_roots hst) l (List.mem_append.mpr (Or.inl
        (List.mem_flatMap.mpr ⟨v, List.mem_cons_self .., hlw⟩)))
    · refine (stateOk_heap_roots hst) l (List.mem_append.mpr (Or.inl
        (List.mem_flatMap.mpr ⟨w, ?_, hlw⟩)))
      exact List.mem_cons_of_mem v hw'
  · exact (stateOk_heap_roots hst) l (List.mem_append.mpr (Or.inr hl))

theorem sr_kUnwrap (sigs : SigTable) (reg : AOReg) (r : STy)
    (env : Env) (eval : List JSValue) (ret : «String»)
    (fs : List Fr) (heap : Heap) (nl : Nat)
    (rest : List Instr) (v : JSValue)
    (h : stateOk sigs r (FM.frames
        (⟨.kUnwrap :: rest, env, .compl Bool.false v :: eval, ret⟩ :: fs)
        heap nl)) :
    SR sigs reg r (FM.frames
        (⟨.kUnwrap :: rest, env, .compl Bool.false v :: eval, ret⟩ :: fs)
        heap nl) := by
  intro hreg _ hst
  obtain ⟨fb, hb, ht⟩ := frameOk_flows_elim (stateOk_head_frameOk hst)
  have ha : absStack sigs none
      (⟨.kUnwrap :: rest, env, .compl Bool.false v :: eval, ret⟩ : Fr)
      = .complN (typeOfV v) :: stackTyOf eval := rfl
  rw [ha, checkSeq_kUnwrap sigs (sigRetTy sigs ret)
      { Γ := envTyOf env, σ := stackTyOf eval } rest (typeOfV v)
      (stackTyOf eval)] at hb
  obtain ⟨hhd, hrest⟩ := stateOk_framesWf_head hst
  refine subject_reduction_frame sigs reg r _
    ⟨rest, env, v :: eval, ret⟩
    fs heap nl hst rfl rfl (frameOk_none_flows _ _ fb hb ht) ?_ hrest
  intro l hl
  rcases List.mem_append.mp hl with hl | hl
  · obtain ⟨w, hw, hlw⟩ := List.mem_flatMap.mp hl
    have hw0 : w ∈ (v :: eval : List JSValue) :=
      (show w ∈ (v :: eval : List JSValue) from hw)
    rcases List.mem_cons.mp hw0 with heq | hw'
    · have hlw2 : l ∈ locsOf (JSValue.compl Bool.false v) := by
        rw [locsOf_compl]
        rw [← heq]
        exact hlw
      exact (stateOk_heap_roots hst) l (List.mem_append.mpr (Or.inl
        (List.mem_flatMap.mpr ⟨.compl Bool.false v, List.mem_cons_self .., hlw2⟩)))
    · refine (stateOk_heap_roots hst) l (List.mem_append.mpr (Or.inl
        (List.mem_flatMap.mpr ⟨w, ?_, hlw⟩)))
      exact List.mem_cons_of_mem _ hw'
  · exact (stateOk_heap_roots hst) l (List.mem_append.mpr (Or.inr hl))

theorem lookup_mem : ∀ (env : Env) (x : «String») (v : JSValue),
    lookup env x = some v → v ∈ env.map Prod.snd := by
  intro env x v h
  induction env with
  | nil => simp only [lookup] at h; exact absurd h (by simp)
  | cons pv rest ih =>
      simp only [lookup] at h
      by_cases hn : (pv.fst == x) = Bool.true
      · rw [if_pos hn] at h
        injection h with hv
        have hmap : (pv :: rest : Env).map Prod.snd
            = Prod.snd pv :: rest.map Prod.snd := rfl
        rw [hmap, ← hv]
        exact List.mem_cons_self ..
      · rw [if_neg hn] at h
        right
        exact ih h

theorem sr_kEval_nv (sigs : SigTable) (reg : AOReg) (r : STy)
    (env : Env) (eval : List JSValue) (ret : «String»)
    (fs : List Fr) (heap : Heap) (nl : Nat)
    (rest : List Instr) (x : «String») (v : JSValue)
    (hlb : lookup env x = some v)
    (h : stateOk sigs r (FM.frames
        (⟨.kEval (.nv x) :: rest, env, eval, ret⟩ :: fs) heap nl)) :
    SR sigs reg r (FM.frames
        (⟨.kEval (.nv x) :: rest, env, eval, ret⟩ :: fs) heap nl) := by
  intro hreg _ hst
  obtain ⟨fb, hb, ht⟩ := frameOk_flows_elim (stateOk_head_frameOk hst)
  have ha : absStack sigs none
      (⟨.kEval (.nv x) :: rest, env, eval, ret⟩ : Fr)
      = stackTyOf eval := rfl
  rw [ha, checkSeq_kEval_nv sigs (sigRetTy sigs ret) env eval rest x v hlb]
    at hb
  obtain ⟨hhd, hrest⟩ := stateOk_framesWf_head hst
  refine subject_reduction_frame sigs reg r _
    ⟨rest, env, v :: eval, ret⟩
    fs heap nl hst (by simp [fstep, hlb]) rfl (frameOk_none_flows _ _ fb hb ht) ?_ hrest
  intro l hl
  rcases List.mem_append.mp hl with hl | hl
  · obtain ⟨w, hw, hlw⟩ := List.mem_flatMap.mp hl
    have hw0 : w ∈ (v :: eval : List JSValue) :=
      (show w ∈ (v :: eval : List JSValue) from hw)
    rcases List.mem_cons.mp hw0 with heq | hw'
    · have hmem : v ∈ env.map Prod.snd := lookup_mem env x v hlb
      have hlw2 : l ∈ locsOf v := by
          have h5 := hlw
          rw [show w = v from heq] at h5
          exact h5
      exact (stateOk_heap_roots hst) l (List.mem_append.mpr (Or.inr
        (List.mem_flatMap.mpr ⟨v, hmem, hlw2⟩)))
    · exact (stateOk_heap_roots hst) l (List.mem_append.mpr (Or.inl
        (List.mem_flatMap.mpr ⟨w, hw', hlw⟩)))
  · exact (stateOk_heap_roots hst) l (List.mem_append.mpr (Or.inr hl))

/- ### The answer-producing arm: kRet at the bottom frame. -/

theorem sr_kRet_bottom (sigs : SigTable) (reg : AOReg) (r : STy)
    (env : Env) (eval : List JSValue) (ret : «String»)
    (rs : List Instr) (heap : Heap) (nl : Nat) (v : JSValue)
    (h : stateOk sigs r (FM.frames
        (⟨.kRet :: rs, env, v :: eval, ret⟩ :: []) heap nl)) :
    SR sigs reg r (FM.frames
        (⟨.kRet :: rs, env, v :: eval, ret⟩ :: []) heap nl) := by
  intro hreg _ hst
  have hstep : fstep reg (FM.frames
      (⟨.kRet :: rs, env, v :: eval, ret⟩ :: []) heap nl)
      = FM.fdone v [] heap nl 0 := rfl
  rw [hstep]
  have hr : machineRet sigs [⟨.kRet :: rs, env, v :: eval, ret⟩] = r :=
    stateOk_machineRet hst
  simp only [machineRet, List.getLast?_singleton] at hr
  obtain ⟨fb, hb, ht⟩ := frameOk_flows_elim (stateOk_head_frameOk hst)
  have ha : absStack sigs none
      (⟨.kRet :: rs, env, v :: eval, ret⟩ : Fr)
      = typeOfV v :: stackTyOf eval := rfl
  rw [ha] at hb
  rw [checkSeq] at hb
  split at hb
  next hcond =>
    injection hb with hfb
    subst hfb
    simp only [List.all_cons, List.all_nil, Bool.and_true] at hcond
    show (match typeOfV v with
      | .complN p => tmoves p r
      | .complT => True
      | _ => False)
    cases hv : typeOfV v with
    | complN p => rw [hv, hr] at hcond; exact hcond
    | complT => exact trivial
    | anyValue _ => rw [hv] at hcond; exact absurd hcond (by simp)
    | desc _ => rw [hv] at hcond; exact absurd hcond (by simp)
    | descAny => rw [hv] at hcond; exact absurd hcond (by simp)
    | isValue _ => rw [hv] at hcond; exact absurd hcond (by simp)
    | oneOf _ => rw [hv] at hcond; exact absurd hcond (by simp)
    | notPresent => rw [hv] at hcond; exact absurd hcond (by simp)
    | union _ => rw [hv] at hcond; exact absurd hcond (by simp)
  next hcond =>
    exact absurd hb (by intro hc; exact TCResult.noConfusion hc)

/- ### kTest: verdict arms (canonical singleton, exact). -/

theorem checkSeq_kTest (sigs : SigTable) (rr : STy) (w : World)
    (rest : List Instr) (t : STy) (σ : List STy) :
    checkSeq sigs rr [{ w with σ := .complN t :: σ }] (.kTest :: rest)
      = checkSeq sigs rr
        [{ w with σ := .isValue (.boolean Bool.false) :: .complN t :: σ }]
        rest := by
  simp [checkSeq, stepWorlds]

theorem checkSeq_kTestT (sigs : SigTable) (rr : STy) (w : World)
    (rest : List Instr) (σ : List STy) :
    checkSeq sigs rr [{ w with σ := .complT :: σ }] (.kTest :: rest)
      = checkSeq sigs rr
        [{ w with σ := .isValue (.boolean Bool.true) :: .complT :: σ }]
        rest := by
  simp [checkSeq, stepWorlds]

theorem sr_kTest (sigs : SigTable) (reg : AOReg) (r : STy)
    (env : Env) (eval : List JSValue) (ret : «String»)
    (fs : List Fr) (heap : Heap) (nl : Nat)
    (rest : List Instr) (v : JSValue)
    (h : stateOk sigs r (FM.frames
        (⟨.kTest :: rest, env, .compl Bool.false v :: eval, ret⟩ :: fs)
        heap nl)) :
    SR sigs reg r (FM.frames
        (⟨.kTest :: rest, env, .compl Bool.false v :: eval, ret⟩ :: fs)
        heap nl) := by
  intro hreg _ hst
  obtain ⟨fb, hb, ht⟩ := frameOk_flows_elim (stateOk_head_frameOk hst)
  have ha : absStack sigs none
      (⟨.kTest :: rest, env, .compl Bool.false v :: eval, ret⟩ : Fr)
      = .complN (typeOfV v) :: stackTyOf eval := rfl
  rw [ha, checkSeq_kTest sigs (sigRetTy sigs ret)
      { Γ := envTyOf env, σ := stackTyOf eval } rest (typeOfV v)
      (stackTyOf eval)] at hb
  obtain ⟨hhd, hrest⟩ := stateOk_framesWf_head hst
  refine subject_reduction_frame sigs reg r _
    ⟨rest, env, .boolean Bool.false :: .compl Bool.false v :: eval, ret⟩
    fs heap nl hst rfl rfl (frameOk_none_flows _ _ fb hb ht) ?_ hrest
  intro l hl
  rcases List.mem_append.mp hl with hl | hl
  · obtain ⟨w, hw, hlw⟩ := List.mem_flatMap.mp hl
    have hw0 : w ∈ (.boolean Bool.false :: .compl Bool.false v :: eval : List JSValue) :=
      (show w ∈ (.boolean Bool.false :: .compl Bool.false v :: eval : List JSValue) from hw)
    rcases List.mem_cons.mp hw0 with heq | hw'
    · rw [heq] at hlw
      exact absurd hlw (by simp [locsOf])
    · exact (stateOk_heap_roots hst) l (List.mem_append.mpr (Or.inl
        (List.mem_flatMap.mpr ⟨w, hw', hlw⟩)))
  · exact (stateOk_heap_roots hst) l (List.mem_append.mpr (Or.inr hl))

theorem sr_kTestT (sigs : SigTable) (reg : AOReg) (r : STy)
    (env : Env) (eval : List JSValue) (ret : «String»)
    (fs : List Fr) (heap : Heap) (nl : Nat)
    (rest : List Instr) (v : JSValue)
    (h : stateOk sigs r (FM.frames
        (⟨.kTest :: rest, env, .compl Bool.true v :: eval, ret⟩ :: fs)
        heap nl)) :
    SR sigs reg r (FM.frames
        (⟨.kTest :: rest, env, .compl Bool.true v :: eval, ret⟩ :: fs)
        heap nl) := by
  intro hreg _ hst
  obtain ⟨fb, hb, ht⟩ := frameOk_flows_elim (stateOk_head_frameOk hst)
  have ha : absStack sigs none
      (⟨.kTest :: rest, env, .compl Bool.true v :: eval, ret⟩ : Fr)
      = .complT :: stackTyOf eval := rfl
  rw [ha, checkSeq_kTestT sigs (sigRetTy sigs ret)
      { Γ := envTyOf env, σ := stackTyOf eval } rest (stackTyOf eval)]
    at hb
  obtain ⟨hhd, hrest⟩ := stateOk_framesWf_head hst
  refine subject_reduction_frame sigs reg r _
    ⟨rest, env, .boolean Bool.true :: .compl Bool.true v :: eval, ret⟩
    fs heap nl hst rfl rfl (frameOk_none_flows _ _ fb hb ht) ?_ hrest
  intro l hl
  rcases List.mem_append.mp hl with hl | hl
  · obtain ⟨w, hw, hlw⟩ := List.mem_flatMap.mp hl
    have hw0 : w ∈ (.boolean Bool.true :: .compl Bool.true v :: eval : List JSValue) :=
      (show w ∈ (.boolean Bool.true :: .compl Bool.true v :: eval : List JSValue) from hw)
    rcases List.mem_cons.mp hw0 with heq | hw'
    · rw [heq] at hlw
      exact absurd hlw (by simp [locsOf])
    · exact (stateOk_heap_roots hst) l (List.mem_append.mpr (Or.inl
        (List.mem_flatMap.mpr ⟨w, hw', hlw⟩)))
  · exact (stateOk_heap_roots hst) l (List.mem_append.mpr (Or.inr hl))
