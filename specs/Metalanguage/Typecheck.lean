import Metalanguage.Grammar

/- # Static typechecking: the flat lattice + pending completions.

    Types are SETS over a closed constructor universe, always in FLAT
    form: Ty = List VTy, a disjunction of atoms with no nesting. A
    test `x is a T` SPLITS the world (then: x ∩ T, verdict singleton
    true; else: x − T, verdict singleton false). Completions are NOT
    types: a world parks at most one completion (pending), pushed by
    bare kCall/kIMeth and completion literals, peeked by kTest,
    extracted by kUnwrap, re-parked by pWrapC/pThrowC, exempt at
    kRet. Descriptor well-formedness is part of the tag's meaning:
    anyValue desc = any well-formed descriptor; desc fs = exactly
    these fields. -/

/- ## Constructor tags (the coarse universe) -/

inductive Ctor where
  | undef | null | bool | num | str | obj | list | desc
  deriving Repr, DecidableEq, BEq

def langTags : List Ctor := [.undef, .null, .bool, .num, .str, .obj]
def anyTags : List Ctor := langTags ++ [.list, .desc]

/- ## Descriptor fields -/

inductive Field where
  | value | writable | getter | setter | enumerable | configurable
  deriving Repr, DecidableEq, BEq

def fData : List Field := [.value, .writable]
def fAcc : List Field := [.getter, .setter]

/-- Well-formed field-set: never both a data field and an accessor
    field — the spec's descriptor-disjointness invariant. -/
def wfFields (fs : List Field) : Bool :=
  !(fs.any (fun fld => fData.contains fld) && fs.any (fun fld => fAcc.contains fld))

def fieldsOf : Descriptor → List Field
  | .mk value writ get set enum conf =>
      (if value.isSome then [Field.value] else [])
      ++ (if writ.isSome then [Field.writable] else [])
      ++ (if get.isSome then [Field.getter] else [])
      ++ (if set.isSome then [Field.setter] else [])
      ++ (if enum.isSome then [Field.enumerable] else [])
      ++ (if conf.isSome then [Field.configurable] else [])

/- ## Atoms: the flat value layer -/

inductive VTy where
  | anyValue (c : Ctor)          -- any value of this class
  | isValue (v : JSValue)        -- exactly this value (singleton)
  | desc (fs : List Field)      -- descriptor with exactly this field-set
  | notPresent                   -- the binding is absent (optional arg)
  deriving Repr, BEq

/-- A flat type: a finite disjunction of atoms. -/
abbrev Ty := List VTy

/-- A parked completion: normal payload (a flat type) or a throw. -/
inductive Pending where
  | normal (t : Ty)
  | throw
  deriving Repr

def tagOf : JSValue → Ctor
  | .undefined => .undef | .null => .null
  | .boolean _ => .bool | .number _ => .num | .str _ => .str
  | .obj _ => .obj | .listV _ => .list | .descV _ => .desc
  | .compl _ _ => .undef        -- completions are never stack atoms

/-- Canonical abstraction of a NON-completion stack value.
    Completions are abstracted by pendingOf, never by typeOfV. -/
def typeOfV : JSValue → VTy
  | .descV d => .desc (fieldsOf d)
  | .compl _ _ => .notPresent   -- unreachable; totality only
  | v => .isValue v

/-- Canonical abstraction of a completion value. -/
def pendingOf : JSValue → Pending
  | .compl Bool.false v => .normal [typeOfV v]
  | .compl Bool.true _ => .throw
  | _ => .throw

def anyOf (cs : List Ctor) : Ty := cs.map VTy.anyValue
def langT : Ty := anyOf langTags
def anyT : Ty := anyOf anyTags

/- ## Subtyping: a finite grid on atoms; forall-exists on flat types -/

def tmovesV : VTy → VTy → Bool
  | .anyValue c, .anyValue c' => c == c'
  | .isValue v, .isValue w => v == w
  | .isValue v, .anyValue c => tagOf v == c
  | .desc _, .anyValue .desc => Bool.true
  | .notPresent, .notPresent => Bool.true
  | _, _ => Bool.false

def tmoves (t u : Ty) : Bool :=
  t.all (fun a => u.any (fun b => tmovesV a b))

def leTy : List Ty → List Ty → Bool
  | [], [] => Bool.true
  | t :: ts, t' :: ts' => tmoves t t' && leTy ts ts'
  | _, _ => Bool.false

/- ## Meets and differences on the flat lattice -/

/-- Atom meet; none = empty. -/
def meetAtom : VTy → VTy → Option VTy
  | .anyValue c, .anyValue c' => if c == c' then some (.anyValue c) else none
  | .isValue v, .isValue w => if v == w then some (.isValue v) else none
  | .desc fs, .desc fs' => if fs == fs' then some (.desc fs) else none
  | .desc fs, .anyValue .desc => some (.desc fs)
  | .anyValue .desc, .desc fs => some (.desc fs)
  | .isValue v, .anyValue c => if tagOf v == c then some (.isValue v) else none
  | .anyValue c, .isValue v => if tagOf v == c then some (.isValue v) else none
  | .notPresent, .notPresent => some .notPresent
  | _, _ => none

def meetTy (S T : Ty) : Ty :=
  S.flatMap (fun a => T.flatMap (fun b =>
    match meetAtom a b with
    | some m => [m]
    | none => []))

/-- Difference. On this lattice a − b is empty exactly when a ⊑ b
    (classes cannot be punctured by singletons), so removal is
    filtration by ¬(a ⊑ b). -/
def removeTy (S T : Ty) : Ty :=
  S.filter (fun a => !T.any (fun b => tmovesV a b))

/- ## Signature tables -/

abbrev SigTable := List («String» × (List Ty × Ty))

def sigFind : SigTable → «String» → Option (List Ty × Ty)
  | [], _ => none
  | (n, s) :: rest, f => if n == f then some s else sigFind rest f

def sigParams (sigs : SigTable) (name : «String») : List Ty :=
  match sigFind sigs name with
  | some (ps, _) => ps
  | none => []

def sigRetTy (sigs : SigTable) (name : «String») : Ty :=
  match sigFind sigs name with
  | some (_, ret) => ret
  | none => [.anyValue .undef]  -- unknown callee: empty payload

abbrev TyEnv := List («String» × Ty)

def zipTy : List «String» → List Ty → TyEnv
  | [], [] => []
  | x :: xs, t :: ts => (x, t) :: zipTy xs ts
  | _, _ => []

def tyLookup : TyEnv → «String» → Option Ty
  | [], _ => none
  | (n, t) :: r, x => if n == x then some t else tyLookup r x

def mopArity : «String» → Option Nat
  | "Get" => some 2
  | "GetOwnProperty" => some 1
  | "GetPrototypeOf" => some 0
  | _ => none

def mopResult : «String» → Ty
  | "Get" => langT
  | "GetPrototypeOf" => [.anyValue .null, .anyValue .obj]
  | "Value" | "Getter" | "Setter" => langT
  | "Writable" | "Enumerable" | "Configurable" => [.anyValue .bool]
  | "GetOwnProperty" =>
      -- stored descriptors are completed at write time: data-complete
      -- or accessor-complete (the spec's disjointness invariant)
      [.desc [.value, .writable, .enumerable, .configurable],
       .desc [.getter, .setter, .enumerable, .configurable],
       .anyValue .undef]
  | _ => anyT

/- ## Worlds -/

structure World where
  Γ : TyEnv
  σ : List Ty
  pending : Option Pending
  deriving Repr

abbrev Worlds := List World

/- ## Expression typing (no side conditions; the is-family refines
    only via the kEval split below) -/

mutual
def typesOf (sigs : SigTable) (Γ : TyEnv) : List Expr → Option (List Ty)
  | [] => some []
  | x :: xs =>
      match typeOfE sigs Γ x, typesOf sigs Γ xs with
      | some t, some ts => some (t :: ts)
      | _, _ => none
termination_by es => sizeOf es

def typeOfE (sigs : SigTable) (Γ : TyEnv) : Expr → Option Ty
  | .nv x => tyLookup Γ x
  | .nat n => some [.isValue (.number ↑n)]
  | .const (.compl _ _) => none    -- completions are parked, never typed
  | .const v => some [typeOfV v]
  | .varNotPresent _ => some [.anyValue .bool]
  | .call f as =>
      match sigFind sigs f with
      | some (ps, ret) =>
          match typesOf sigs Γ as with
          | some ts =>
              if leTy ts ps
                 || (as.length == ps.length - 1
                     && leTy ts (ps.dropLast))
              then some ret else none
          | none => none
      | none => none
  | .imeth nm recv args =>
      match mopArity nm with
      | some k =>
          if args.length == k && typeOfE sigs Γ recv == some [.anyValue .obj]
             && (typesOf sigs Γ args).isSome
          then some (mopResult nm) else none
      | none => none
  | .ifield nm x =>
      -- the zero-arg-MOP deviation: o.[[GetPrototypeOf]] is
      -- semantically the call; other fields are dynamic guards
      if (typeOfE sigs Γ x).isSome then some (mopResult nm) else none
  | .listE es =>
      if (typesOf sigs Γ es).isSome then some [.anyValue .list] else none
  | .isObject x | .isNotObject x | .isNotUndefined x | .hasCall x
  | .hasCtor x | .isU x | .isBoolVal _ x | .isStrVal _ x
  | .isNullOrUnd x | .isNull x | .isType _ x | .hasField _ x =>
      if (typeOfE sigs Γ x).isSome then some [.anyValue .bool] else none
termination_by e => sizeOf e
end

/- ## Flows and results -/

structure Flows where
  exits : Bool
  falls : Worlds
  /- Assert obligations that could not be discharged by the splits:
     each recorded assumption is a proof debt (caller contracts, spec
     editor claims); the certificate is RELATIVE to them. Discharged
     asserts (impossible false-worlds) leave no trace. -/
  assumes : List «String»
  deriving Repr

/-- Frame-level demand: every world exits (returns), none falls. -/
def terminal (f : Flows) : Bool :=
  f.exits && f.falls.isEmpty

inductive TCResult where
  | flows (f : Flows)
  | reject (site : Instr) (why : «String»)
  deriving Repr

/- ## Stack operations -/

/-- Pop one slot, demanding every atom below the upper bound T. -/
def popTy (T : Ty) (σ : List Ty) : Option (List Ty) :=
  match σ with
  | ts :: σ' => if tmoves ts T then some σ' else none
  | [] => none

def popA (t : VTy) (σ : List Ty) : Option (List Ty) := popTy [t] σ

def popTyN : Nat → Ty → List Ty → Option (List Ty)
  | 0, _, σ => some σ
  | k + 1, t, σ =>
      match popTy t σ with
      | some σ' => popTyN k t σ'
      | none => none

/- Argument check: the top n stack types REVERSED (the machine pushes
    args in order, so the top is the LAST argument) are pointwise
    below the callee's parameters. -/
def popArgs (ps σ : List Ty) : Bool :=
  σ.length ≥ ps.length && leTy (σ.take ps.length).reverse ps

def primTys (p : Prim) : Option (Ty × Ty) :=
  match p with
  | .pThrowC => none                     -- t ↦ pending throw, inline
  | .pWrapC => none                      -- t ↦ pending normal t, inline
  | .pIsObj | .pIsNotObj | .pIsNotU | .pHasCall | .pHasCtor | .pIsU
  | .pIsTrue | .pIsFalse | .pNullOrUnd | .pIsNull
  | .pIsType _ | .pHasField _ | .pIsStr _ => some (anyT, [.anyValue .bool])
  | .pDescField _ => some (anyT, anyT)

/- ## Shape tests: the flat type a test's THEN side asserts -/

def typeMask : «String» → Ty
  | "Boolean" => [.anyValue .bool]
  | "Number" => [.anyValue .num]
  | "String" => [.anyValue .str]
  | _ => []        -- no such constructor in our universe

def testType : Expr → Option Ty
  | .isObject _ => some [.anyValue .obj]
  | .isNotObject _ => some (anyOf (anyTags.filter (fun c => c != .obj)))
  | .isU _ => some [.anyValue .undef]
  | .isNotUndefined _ => some (anyOf (anyTags.filter (fun c => c != .undef)))
  | .isNull _ => some [.anyValue .null]
  | .isNullOrUnd _ => some [.anyValue .undef, .anyValue .null]
  | .isBoolVal b _ => some [.isValue (.boolean b)]
  | .isStrVal s _ => some [.isValue (.str s)]
  | .isType ty _ => some (typeMask ty)
  | .varNotPresent _ => some [.notPresent]
  | _ => none

/-- The variable a shape test inspects, if any. -/
def testedVar : Expr → Option «String»
  | .isObject (.nv x) | .isNotObject (.nv x) | .isU (.nv x)
  | .isNotUndefined (.nv x) | .isNull (.nv x) | .isNullOrUnd (.nv x)
  | .isBoolVal _ (.nv x) | .isStrVal _ (.nv x) | .isType _ (.nv x)
  | .varNotPresent x => some x
  | _ => none

/- ## The world-stepping checker -/

/-- Park a completion in a world; refuses double parking. -/
def parkPending (p : Pending) (w : World) : Option World :=
  if w.pending.isSome then none
  else some { w with pending := some p }

/-- Step every world through one stack instruction (no control
    flow). Fails (none) if any world's stack or pending does not
    match. -/
def stepWorlds (sigs : SigTable) (ws : Worlds) (i : Instr) : Option Worlds :=
  match i with
  | .kPrim1 .pWrapC =>
      ws.mapM (fun w =>
        match w.σ with
        | t :: σ' => parkPending (.normal t) { w with σ := σ' }
        | [] => none)
  | .kPrim1 .pThrowC =>
      ws.mapM (fun w =>
        match w.σ with
        | _ :: σ' => parkPending .throw { w with σ := σ' }
        | [] => none)
  | .kPrim1 p =>
      match primTys p with
      | some (tin, tout) =>
          ws.mapM (fun w => match popTy tin w.σ with
            | some σ' => some { w with σ := tout :: σ' }
            | none => none)
      | none => some ws
  | .kCall f n =>
      -- PARKING SPLITS: a callee can answer with a normal payload
      -- (typed by its signature) OR a throw - explore BOTH deliveries
      -- as separate worlds. The throw world exits at the self-test's
      -- kRet (exempt); the normal world continues through kUnwrap.
      match sigFind sigs f with
      | some (ps, ret) =>
          if ps.length == n
              && ws.all (fun w => w.pending.isNone && popArgs ps w.σ) then
            some (ws.flatMap (fun w =>
              [{ w with σ := w.σ.drop n, pending := some (.normal ret) },
               { w with σ := w.σ.drop n, pending := some .throw }]))
          else none
      | none => none
  | .kSet x =>
      ws.mapM (fun w =>
        match w.σ with
        | t :: σ' => some { w with Γ := (x, t) :: w.Γ, σ := σ' }
        | [] => none)
  | .kPop =>
      ws.mapM (fun w =>
        match w.σ with
        | _ :: σ' => some { w with σ := σ' }
        | [] => none)
  | .kTest =>
      -- TESTING OBSERVES: parking already split the deliveries into
      -- worlds; each world parks exactly one completion and gets its
      -- EXACT verdict singleton (normal -> false, throw -> true). No
      -- pending: the machine fells on a non-completion - reject.
      ws.mapM (fun w =>
        match w.pending with
        | some (.normal _) =>
            some { w with σ := [.isValue (.boolean Bool.false)] :: w.σ }
        | some .throw =>
            some { w with σ := [.isValue (.boolean Bool.true)] :: w.σ }
        | none => none)
  | .kUnwrap =>
      ws.mapM (fun w =>
        match w.pending with
        | some (.normal t) => some { w with σ := t :: w.σ, pending := none }
        | some .throw =>
            some { w with σ := anyT :: w.σ, pending := none }  -- dead path
        | none => none)
  | .kIMeth nm n =>
      -- PARKING SPLITS (same both-deliveries rule as kCall)
      if mopArity nm == some n
          && ws.all (fun w =>
            w.pending.isNone
              && match popTyN n anyT w.σ with
                 | some σ' => (popA (.anyValue .obj) σ').isSome
                 | none => Bool.false) then
        some (ws.flatMap (fun w =>
          match popTyN n anyT w.σ with
          | some σ' =>
              match popA (.anyValue .obj) σ' with
              | some σ'' =>
                  [{ w with σ := σ'', pending := some (.normal (mopResult nm)) },
                   { w with σ := σ'', pending := some .throw }]
              | none => []
          | none => []))
      else none
  | .kMkList n =>
      ws.mapM (fun w =>
        match popTyN n anyT w.σ with
        | some σ' => some { w with σ := [.anyValue .list] :: σ' }
        | none => none)
  | .kNewSlot sn =>
      if (slotOfName sn).isSome then
        ws.mapM (fun w =>
          match popTy anyT w.σ with
          | some σ' => some { w with σ := [.anyValue .obj] :: σ' }
          | none => none)
      else none
  | _ => some ws

/-- Correlated predicate tests: IsDataDescriptor(x) /
    IsAccessorDescriptor(x) are decidable per EXACT desc atom
    (field-set membership); everything else is undecided and
    duplicated to both sides. -/
def predDecide (f : «String») : Option (VTy → Option Bool) :=
  match f with
  | "IsDataDescriptor" =>
      some (fun t => match t with
        | .desc fs => some (fs.any (fun fld => fData.contains fld))
        | _ => none)
  | "IsAccessorDescriptor" =>
      some (fun t => match t with
        | .desc fs => some (fs.any (fun fld => fAcc.contains fld))
        | _ => none)
  | _ => none

/-- The decider for a correlated `IsX(x) is true` expression, if any. -/
def predDecideEx : Expr → Option (VTy → Option Bool)
  | .isBoolVal Bool.true (Expr.call f [Expr.nv _]) => predDecide f
  | _ => none

/-- Split worlds by a per-atom decider: determined atoms go to their
    side (verdict singletons); undecided atoms are duplicated to both
    sides (the runtime picks one). -/
def splitWorldsP (x : «String») (dec : VTy → Option Bool)
    (ws : Worlds) : Option Worlds :=
  match ws.mapM (fun (w : World) =>
    match tyLookup w.Γ x with
    | none => none
    | some S =>
        let go (acc : Worlds × Worlds) (a : VTy) : Worlds × Worlds :=
          match dec a with
          | some Bool.true =>
              (acc.1 ++ [{ Γ := (x, [a]) :: w.Γ, σ := [.isValue (.boolean Bool.true)] :: w.σ, pending := w.pending }], acc.2)
          | some Bool.false =>
              (acc.1, acc.2 ++ [{ Γ := (x, [a]) :: w.Γ, σ := [.isValue (.boolean Bool.false)] :: w.σ, pending := w.pending }])
          | none =>
              (acc.1 ++ [{ Γ := (x, [a]) :: w.Γ, σ := [.isValue (.boolean Bool.true)] :: w.σ, pending := w.pending }],
               acc.2 ++ [{ Γ := (x, [a]) :: w.Γ, σ := [.isValue (.boolean Bool.false)] :: w.σ, pending := w.pending }])
        let parts := S.foldl go ([], [])
        let all := parts.1 ++ parts.2
        if all.isEmpty then none else (some all : Option Worlds)) with
  | none => none
  | some wss => some (List.flatten wss)

/-- Split worlds at a test of x with then-type T. -/
def splitWorlds (x : «String») (T : Ty) (ws : Worlds) : Option Worlds :=
  match ws.mapM (fun (w : World) =>
    match tyLookup w.Γ x with
    | none => none
    | some S =>
        let thenS := meetTy S T
        let elseS := removeTy S T
        -- at least one side must be possible; emit verdict + refined Γ
        let out : List World :=
          (if !thenS.isEmpty then [{ Γ := (x, thenS) :: w.Γ, σ := [.isValue (.boolean Bool.true)] :: w.σ, pending := w.pending }] else [])
          ++ (if !elseS.isEmpty then [{ Γ := (x, elseS) :: w.Γ, σ := [.isValue (.boolean Bool.false)] :: w.σ, pending := w.pending }] else [])
        if out.isEmpty then none else (some out : Option Worlds)) with
  | none => none
  | some wss => some (List.flatten wss)

/- Loop join: every falls-world must come back to the loop-entry
    stack with no parked completion (neutrality); the continuation
    runs from those worlds. -/
def checkLoopBody (rbody : TCResult) (site : Instr)
    (σ₀ : List Ty) (k : Worlds → TCResult) : TCResult :=
  match rbody with
  | .reject site' why => .reject site' why
  | .flows fb =>
      let neutral := fb.falls.all (fun w => w.σ == σ₀ && w.pending.isNone)
      if neutral then
        match k fb.falls with
        | .flows fr => .flows { exits := fb.exits || fr.exits, falls := fr.falls, assumes := fb.assumes ++ fr.assumes }
        | res => res
      else .reject site "loop body is not stack-neutral"

def checkSeq : SigTable → Ty → Worlds → List Instr → TCResult
  | _, _, ws, [] => .flows { exits := Bool.false, falls := ws, assumes := [] }
  | _, r, ws, .kRet :: _ =>
      -- every world returns: pending payload ⊑ r, or a throw
      if ws.all (fun w =>
        match w.pending with
        | some (.normal t) => tmoves t r
        | some .throw => Bool.true
        | none => Bool.false) then
        .flows { exits := Bool.true, falls := [], assumes := [] }
      else .reject .kRet "kRet: payload does not match the frame's destiny r"
  | sigs, r, ws, .kIte t e :: rest =>
      -- dispatch each world on its verdict; split both-verdict worlds
      let dispatch (w : World) : Option (Worlds × Worlds) :=
        match w.σ with
        | ts :: σ' =>
            if ts.all (fun a => tmovesV a (.isValue (.boolean Bool.true))) then
              some ([{ w with σ := σ' }], [])
            else if ts.all (fun a => tmovesV a (.isValue (.boolean Bool.false))) then
              some ([], [{ w with σ := σ' }])
            else if ts.all (fun a => tmovesV a (.anyValue .bool)) then
              some ([{ w with σ := σ' }], [{ w with σ := σ' }])
            else none
        | [] => none
      match ws.mapM dispatch with
      | none => .reject (.kIte t e) "kIte: verdict is not boolean"
      | some pairs =>
          let wsT := (pairs.map Prod.fst).flatten
          let wsE := (pairs.map Prod.snd).flatten
          match checkSeq sigs r wsT t, checkSeq sigs r wsE e with
          | .reject site' why, _ => .reject site' why
          | _, .reject site' why => .reject site' why
          | .flows f₁, .flows f₂ =>
              match checkSeq sigs r (f₁.falls ++ f₂.falls) rest with
              | .flows fr =>
                  .flows { exits := f₁.exits || f₂.exits || fr.exits
                         , falls := fr.falls
                         , assumes := f₁.assumes ++ f₂.assumes ++ fr.assumes }
              | res => res
  | sigs, r, ws, .kEval (.const (.compl Bool.false pv)) :: rest =>
      -- a completion literal parks itself (never a stack atom)
      match ws.mapM (fun w => parkPending (.normal [typeOfV pv]) w) with
      | none => .reject (.kEval (.const (.compl Bool.false pv))) "double-parked completion"
      | some ws' => checkSeq sigs r ws' rest
  | sigs, r, ws, .kEval (.const (.compl Bool.true _)) :: rest =>
      match ws.mapM (fun w => parkPending .throw w) with
      | none => .reject (.kEval (.const (.compl Bool.true JSValue.undefined))) "double-parked completion"
      | some ws' => checkSeq sigs r ws' rest
  | sigs, r, ws, .kEval ex :: rest =>
      -- correlated predicate tests (IsDataDescriptor(x) is true, …)
      -- split the worlds via the per-atom decider; otherwise the
      -- ordinary shape-test / push paths
      match ex, predDecideEx ex with
      | .isBoolVal Bool.true (Expr.call f [Expr.nv x]), some dec =>
          match splitWorldsP x dec ws with
          | none => .reject (.kEval ex) "ill-typed predicate test (unbound or empty split)"
          | some ws' => checkSeq sigs r ws' rest
      | _, _ =>
          if (testType ex).isSome then
            match testedVar ex with
            | some x =>
                match splitWorlds x (testType ex).get! ws with
                | none => .reject (.kEval ex) "ill-typed test (unbound or empty split)"
                | some ws' => checkSeq sigs r ws' rest
            | none =>
                match ws.mapM (fun (w : World) =>
                  match typeOfE sigs w.Γ ex with
                  | none => none
                  | some t => some { w with σ := t :: w.σ }) with
                | none => .reject (.kEval ex) "ill-typed expression"
                | some ws' => checkSeq sigs r ws' rest
          else
            match ws.mapM (fun (w : World) =>
              match typeOfE sigs w.Γ ex with
              | none => none
              | some t => some { w with σ := t :: w.σ }) with
            | none => .reject (.kEval ex) "ill-typed expression (unbound or bad args)"
            | some ws' => checkSeq sigs r ws' rest
  | sigs, r, ws, .kRepeatWhile c body :: rest =>
      if ws.all (fun w =>
        match typeOfE sigs w.Γ c with
        | some t => tmoves t [.anyValue .bool]
        | none => Bool.false) then
        checkLoopBody (checkSeq sigs r ws body) (.kRepeatWhile c body)
          (ws.head?.map World.σ |>.getD []) (fun wsf => checkSeq sigs r wsf rest)
      else .reject (.kRepeatWhile c body) "loop condition is not boolean"
  | sigs, r, ws, .kRepeatTest c body :: rest =>
      match ws.mapM (fun (w : World) => popTy [.anyValue .bool] w.σ) with
      | none => .reject (.kRepeatTest c body) "loop verdict is not boolean"
      | some ws' =>
          let ws'' := ws.zip ws' |>.map (fun (w, σ') => { w with σ := σ' })
          checkLoopBody (checkSeq sigs r ws'' body) (.kRepeatTest c body)
            (ws''.head?.map World.σ |>.getD []) (fun wsf => checkSeq sigs r wsf rest)
  | sigs, r, ws, .kForStart x body :: rest =>
      match ws.mapM (fun (w : World) => popA (.anyValue .list) w.σ) with
      | none => .reject (.kForStart x body) "for-each over a non-list"
      | some ws' =>
          let ws'' := (ws.zip ws').map (fun (w, σ') =>
            { w with Γ := (x, langT) :: w.Γ, σ := σ' })
          checkLoopBody (checkSeq sigs r ws'' body) (.kForStart x body)
            (ws''.head?.map World.σ |>.getD []) (fun wsf => checkSeq sigs r wsf rest)
  | sigs, r, ws, .kForBody x _ body :: rest =>
      let ws' := ws.map (fun w => { w with Γ := (x, langT) :: w.Γ })
      checkLoopBody (checkSeq sigs r ws' body) (.kForBody x [] body)
        (ws'.head?.map World.σ |>.getD []) (fun wsf => checkSeq sigs r wsf rest)
  | sigs, r, ws, .kAssert :: rest =>
      -- asserts: the true-verdict worlds continue; false-verdict
      -- worlds are ASSUMED away (proof debt recorded); an undecided
      -- boolean continues with its false side assumed away
      let rec step (w : World) : World × Bool :=
        match w.σ with
        | ts :: σ' =>
            if ts.all (fun a => tmovesV a (.isValue (.boolean Bool.true))) then
              ({ w with σ := σ' }, Bool.false)
            else if ts.all (fun a => tmovesV a (.anyValue .bool)) then
              ({ w with σ := σ' }, Bool.true)
            else (w, Bool.true)   -- non-boolean verdict: fell-world
        | [] => (w, Bool.true)
      let stepped := ws.map step
      let ws' := stepped.map Prod.fst
      let anyAssumed := stepped.any Prod.snd
      let desc :=
        match rest.head? with
        | _ => "assert obligation not discharged"
      match checkSeq sigs r ws' rest with
      | .flows fr =>
          if anyAssumed then
            .flows { fr with assumes := desc :: fr.assumes }
          else .flows fr
      | res => res
  | sigs, r, ws, i :: rest =>
      match stepWorlds sigs ws i with
      | none => .reject i "world stack mismatch"
      | some ws' => checkSeq sigs r ws' rest
termination_by _ _ _ is => sizeOf is

def typecheckSeq (sigs : SigTable) (r : Ty) (Γ : TyEnv) (seq : List Instr) : TCResult :=
  checkSeq sigs r [{ Γ := Γ, σ := [], pending := none }] seq

def typecheckAO (sigs : SigTable)
    (name : «String») (params : List «String») (body : List Instr) : Option TCResult :=
  match sigFind sigs name with
  | none =>
      some (.reject (body.head?.getD .kRet)
        (name ++ " has no entry in the signature table"))
  | some (paramTys, ret) =>
      if params.length != paramTys.length then
        some (.reject (body.head?.getD .kRet)
          (name ++ ": registry arity/signature arity mismatch"))
      else match typecheckSeq sigs ret (zipTy params paramTys) body with
        | .flows f => if terminal f then none else some (.flows f)
        | res => some res

def typecheckReg (sigs : SigTable) (reg : AOReg) : Option («String» × TCResult) :=
  match reg with
  | [] => none
  | (name, (params, prog)) :: rest =>
      match typecheckAO sigs name params (compileSteps prog) with
      | some r => some (name, r)
      | none => typecheckReg sigs rest

def typecheckRegOk (sigs : SigTable) (reg : AOReg) : Bool :=
  (typecheckReg sigs reg).isNone
