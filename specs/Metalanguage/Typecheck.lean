import Metalanguage.Grammar

/- # Static typechecking: set-of-constructors types + worlds.

   Types are SETS over a closed constructor universe (bitmasks), plus
   completion wire shapes. The checker tracks a finite set of WORLDS
   (each an abstract stack + variable types). A shape test
   `x is a T` SPLITS the world: then-world x : S ∩ T with verdict
   {trueVal}, else-world x : S - T with verdict {falseVal};
   impossible worlds are dropped. kIte dispatches each world on its
   verdict's type ({trueVal} -> then, {falseVal} -> else, wider ->
   the world fells). Assertions discharge exactly when the split
   leaves no false-world. -/

/- Constructor universe bits -/
def cUndef  : Nat := 1
def cNull   : Nat := 2
def cTrue   : Nat := 4
def cFalse  : Nat := 8
def cNum    : Nat := 16
def cStr    : Nat := 32
def cObj    : Nat := 64
def cList   : Nat := 128
def cDesc   : Nat := 256

def boolV   : Nat := cTrue + cFalse
def langV   : Nat := cUndef + cNull + boolV + cNum + cStr + cObj
def anyV    : Nat := langV + cList + cDesc

inductive STy where
  | val (mask : Nat)          -- a set of value constructors
  | isValue (v : JSValue)     -- exactly this value
  | oneOf (vs : List JSValue) -- one of these values
  | notPresent                -- the variable is not bound (absent argument)
  | union (parts : List STy)  -- finite union (used in signatures)
  | complN (t : STy)          -- normal completion wrapping a payload type
  | complT                    -- a throw
  deriving Repr, BEq, Inhabited

/- ## Set operations on types -/

def valMask : STy → Nat
  | .val m => m
  | _ => 0

/-- Constructor bit of a value — booleans resolve to their exact
   bit, so `isValue (boolean true) ⊑ val cTrue` holds. -/
def ctorBit : JSValue → Nat
  | .undefined => cUndef
  | .null => cNull
  | .boolean Bool.true => cTrue
  | .boolean Bool.false => cFalse
  | .number _ => cNum
  | .str _ => cStr
  | .obj _ => cObj
  | .listV _ => cList
  | .descV _ => cDesc
  | .compl _ _ => 0

/-- Canonical types are SINGLETONS for known values: the canonical
   abstraction must not lose value identity, or mid-execution
   re-typechecks fail where the original certification passed (e.g.
   `set preferredType to ~number~` then calling a oneOf-parameter
   callee: coarse {cStr} ⊄ oneOf ["string","number"]). -/
def typeOfV : JSValue → STy
  | .compl Bool.false v => .complN (typeOfV v)
  | .compl Bool.true _ => .complT
  | v => .isValue v

/- Unions appear only in signatures; flatten to union-free atoms for
   the set operations. -/
def atoms : STy → List STy
  | .union ps => ps.flatMap atoms
  | t => [t]

def ofAtoms : List STy → STy
  | [] => .val 0
  | [t] => t
  | ts => .union ts

mutual
def tyNonemptyList : List STy → Bool
  | [] => Bool.false
  | t :: ts => tyNonempty t || tyNonemptyList ts
termination_by ts => sizeOf ts
decreasing_by all_goals simp_wf <;> omega

def tyNonempty : STy → Bool
  | .val m => m != 0
  | .oneOf vs => !vs.isEmpty
  | .union ps => tyNonemptyList ps
  | _ => true
termination_by t => sizeOf t
decreasing_by all_goals simp_wf <;> omega
end

/-- Meet of union-free types (completions never meet values). -/
def tyMeetAtom : STy → STy → STy
  | .val a, .val b => .val (a &&& b)
  | .isValue v, .isValue w => if v == w then .isValue v else .val 0
  | .isValue v, .oneOf ws => if ws.contains v then .isValue v else .val 0
  | .oneOf vs, .isValue w => if vs.contains w then .isValue w else .val 0
  | .isValue v, .val m =>
      if ((ctorBit v) &&& m) != 0 then .isValue v else .val 0
  | .oneOf vs, .val m =>
      let kept := vs.filter (fun v => ((ctorBit v) &&& m) != 0)
      if kept.isEmpty then .val 0 else .oneOf kept
  | .oneOf vs, .oneOf ws => .oneOf (vs.filter ws.contains)
  | .notPresent, .notPresent => .notPresent
  | _, _ => .val 0

def tyMeet (t t' : STy) : STy :=
  ofAtoms ((atoms t).flatMap (fun a =>
    (atoms t').filterMap (fun b =>
      let m := tyMeetAtom a b
      if tyNonempty m then some m else none)))

/-- Difference of union-free types. Masks cannot be punctured by value
   tests: removing a value from a constructor set keeps the whole set
   (sound over-approximation; precise signatures lose nothing). -/
def tyRemoveAtom : STy → STy → STy
  | .val a, .val b => .val (a - (a &&& b))
  | .isValue v, .isValue w => if v == w then .val 0 else .isValue v
  | .isValue v, .oneOf ws => if ws.contains v then .val 0 else .isValue v
  | .oneOf vs, .isValue v => .oneOf (vs.filter (fun w => !(w == v)))
  | .oneOf vs, .oneOf ws => .oneOf (vs.filter (fun v => !ws.contains v))
  | .val a, .isValue _ => .val a            -- conservative: no puncturing
  | .val a, .oneOf _ => .val a              -- conservative
  | .notPresent, .notPresent => .val 0
  | t, _ => t

def tyRemove (t t' : STy) : STy :=
  ofAtoms ((atoms t).filterMap (fun a =>
    let r := (atoms t').foldl (fun acc b => tyRemoveAtom acc b) a
    if tyNonempty r then some r else none))

def tmovesAtom : STy → STy → Bool
  | .val 0, _ => Bool.true          -- the empty type is below everything
  | .val a, .val b => (a - (a &&& b)) == 0
  | .isValue v, .isValue w => v == w
  | .isValue v, .oneOf ws => ws.contains v
  | .isValue v, .val m => ((ctorBit v) &&& m) != 0
  | .oneOf vs, .oneOf ws => vs.all ws.contains
  | .oneOf vs, .val m =>
      vs.all (fun v => ((ctorBit v) &&& m) != 0)
  | .oneOf vs, .isValue v => vs.length == 1 && vs.contains v
  | .notPresent, .notPresent => Bool.true
  | .complN a, .complN b => tmovesAtom a b
  | t, t' => t == t'

/-- Subtyping (covariant under complN), distributed over union atoms;
   a val straddling a union is conservatively NOT a subtype. -/
def tmoves (t t' : STy) : Bool :=
  (atoms t).all (fun a => (atoms t').any (fun b => tmovesAtom a b))

def leList : List STy → List STy → Bool
  | [], [] => Bool.true
  | t :: ts, t' :: ts' => tmoves t t' && leList ts ts'
  | _, _ => Bool.false


abbrev SigTable := List («String» × (List STy × STy))

def sigFind : SigTable → «String» → Option (List STy × STy)
  | [], _ => none
  | (n, s) :: rest, f => if n == f then some s else sigFind rest f

def sigParams (sigs : SigTable) (name : «String») : List STy :=
  match sigFind sigs name with
  | some (ps, _) => ps
  | none => []

def sigRetTy (sigs : SigTable) (name : «String») : STy :=
  match sigFind sigs name with
  | some (_, ret) => ret
  | none => .val anyV

abbrev TyEnv := List («String» × STy)

def zipTy : List «String» → List STy → TyEnv
  | [], [] => []
  | x :: xs, t :: ts => (x, t) :: zipTy xs ts
  | _, _ => []

def tyLookup : TyEnv → «String» → Option STy
  | [], _ => none
  | (n, t) :: r, x => if n == x then some t else tyLookup r x

def mopArity : «String» → Option Nat
  | "Get" => some 2
  | "GetOwnProperty" => some 1
  | "GetPrototypeOf" => some 0
  | _ => none

def mopResult : «String» → STy
  | "Get" => .val langV          -- [[Get]] delivers a language value
  | "GetPrototypeOf" => .val (cNull + cObj)
  | "Value" | "Getter" | "Setter" => .val langV
  | "Writable" | "Enumerable" | "Configurable" => .val boolV
  | _ => .val anyV                -- [[GetOwnProperty]]: descriptor | undefined

/- ## Worlds -/

structure World where
  Γ : TyEnv
  σ : List STy
  deriving Repr

abbrev Worlds := List World

/- ## Expression typing (no side conditions; the is-family refines
   only via the kEval split below) -/

mutual
def typesOf (sigs : SigTable) (Γ : TyEnv) : List Expr → Option (List STy)
  | [] => some []
  | x :: xs =>
      match typeOfE sigs Γ x, typesOf sigs Γ xs with
      | some t, some ts => some (t :: ts)
      | _, _ => none
termination_by es => sizeOf es

def typeOfE (sigs : SigTable) (Γ : TyEnv) : Expr → Option STy
  | .nv x => tyLookup Γ x
  | .nat n => some (.isValue (.number n.toFloat))
  | .const v => some (.isValue v)
  | .varNotPresent _ => some (.val boolV)
  | .call f as =>
      match sigFind sigs f with
      | some (ps, ret) =>
          match typesOf sigs Γ as with
          | some ts =>
              if leList ts ps
                 || (as.length == ps.length - 1
                     && leList ts (ps.dropLast))
              then some ret else none
          | none => none
      | none => none
  | .imeth nm recv args =>
      match mopArity nm with
      | some k =>
          if args.length == k && typeOfE sigs Γ recv == some (.val cObj)
             && (typesOf sigs Γ args).isSome
          then some (mopResult nm) else none
      | none => none
  | .ifield nm x =>
      -- the zero-arg-MOP deviation: o.[[GetPrototypeOf]] is
      -- semantically the call; other fields are dynamic guards
      if (typeOfE sigs Γ x).isSome then some (mopResult nm) else none
  | .listE es =>
      if (typesOf sigs Γ es).isSome then some (.val cList) else none
  | .isObject x | .isNotObject x | .isNotUndefined x | .hasCall x
  | .hasCtor x | .isU x | .isBoolVal _ x | .isStrVal _ x
  | .isNullOrUnd x | .isNull x | .isType _ x | .hasField _ x =>
      if (typeOfE sigs Γ x).isSome then some (.val boolV) else none
termination_by e => sizeOf e
end

/- ## Flows and results -/

structure Flows where
  exits : Bool
  falls : Worlds          -- worlds that ran off the end of the list
  /- Assert obligations that could not be discharged by the splits:
     each recorded assumption is a proof debt (caller contracts, spec
     editor claims); the certificate is RELATIVE to them. Discharged
     asserts (impossible false-worlds) leave no trace. -/
  assumes : List «String»
  deriving Repr

/-- Frame-level demand: every world exits (returns), none falls
   through. -/
def terminal (f : Flows) : Bool :=
  f.exits && f.falls.isEmpty

inductive TCResult where
  | flows (f : Flows)
  | reject (site : Instr) (why : «String»)
  deriving Repr

/- ## Stack operations -/

def popTy (t : STy) (σ : List STy) : Option (List STy) :=
  match σ with
  | t' :: σ' => if tmoves t' t then some σ' else none
  | [] => none

def popTyN : Nat → STy → List STy → Option (List STy)
  | 0, _, σ => some σ
  | k + 1, t, σ =>
      match popTy t σ with
      | some σ' => popTyN k t σ'
      | none => none

def popArgs (ps σ : List STy) : Bool :=
  σ.length ≥ ps.length && leList ps.reverse (σ.take ps.length).reverse

def primTys (p : Prim) : Option (STy × STy) :=
  match p with
  | .pThrowC => some (.val anyV, .complT)
  | .pIsObj | .pIsNotObj | .pIsNotU | .pHasCall | .pHasCtor | .pIsU
  | .pIsTrue | .pIsFalse | .pNullOrUnd | .pIsNull
  | .pIsType _ | .pHasField _ | .pIsStr _ => some (.val anyV, .val boolV)
  | .pDescField _ => some (.val anyV, .val anyV)
  | .pWrapC => none                     -- t ↦ complN t, inline

/- ## Shape tests: the mask a test's THEN side asserts -/

def typeMask : «String» → Nat
  | "Boolean" => boolV
  | "Number" => cNum
  | "String" => cStr
  | "Symbol" => 0        -- no such constructor in our universe
  | "BigInt" => 0
  | _ => 0

/-- The type a test's THEN world restricts the tested value to.
   none = non-splitting predicate (no refinement). -/
def testType : Expr → Option STy
  | .isObject _ => some (.val cObj)
  | .isNotObject _ => some (.val (anyV - cObj))
  | .isU _ => some (.val cUndef)
  | .isNotUndefined _ => some (.val (anyV - cUndef))
  | .isNull _ => some (.val cNull)
  | .isNullOrUnd _ => some (.val (cUndef + cNull))
  | .isBoolVal b _ => some (.isValue (.boolean b))
  | .isStrVal s _ => some (.isValue (.str s))
  | .isType ty _ => some (.val (typeMask ty))
  | .varNotPresent _ => some .notPresent
  | _ => none

/-- The variable a shape test inspects, if any. -/
def testedVar : Expr → Option «String»
  | .isObject (.nv x) | .isNotObject (.nv x) | .isU (.nv x)
  | .isNotUndefined (.nv x) | .isNull (.nv x) | .isNullOrUnd (.nv x)
  | .isBoolVal _ (.nv x) | .isStrVal _ (.nv x) | .isType _ (.nv x)
  | .varNotPresent x => some x
  | _ => none

/- ## The world-stepping checker

   checkSeq processes one instruction list against a SET of worlds.
   Shape tests split worlds (dropping impossible ones); kIte sends
   each world down its verdict's path; falls collect worlds. -/

/-- Step every world through one stack instruction (no control
   flow). Fails (none) if any world's stack does not match. -/
def stepWorlds (sigs : SigTable) (ws : Worlds) (i : Instr) : Option Worlds :=
  match i with
  | .kPrim1 .pWrapC =>
      ws.mapM (fun w =>
        match w.σ with
        | t :: σ' => some { w with σ := .complN t :: σ' }
        | [] => none)
  | .kPrim1 p =>
      match primTys p with
      | some (tin, tout) =>
          ws.mapM (fun w => match popTy tin w.σ with
            | some σ' => some { w with σ := tout :: σ' }
            | none => none)
      | none => some ws
  | .kCall f n =>
      match sigFind sigs f with
      | some (ps, ret) =>
          if ps.length == n && ws.all (fun w => popArgs ps w.σ) then
            some (ws.map (fun w => { w with σ := .complN ret :: w.σ.drop n }))
          else none
      | none => none
  | .kSet x =>
      ws.mapM (fun w =>
        match w.σ with
        | t :: σ' => some { Γ := (x, t) :: w.Γ, σ := σ' }
        | [] => none)
  | .kPop =>
      ws.mapM (fun w =>
        match w.σ with
        | _ :: σ' => some { w with σ := σ' }
        | [] => none)
  | .kTest =>
      -- verdict is EXACT: complN -> falseVal (not abrupt), complT -> trueVal
      ws.mapM (fun w =>
        match w.σ with
        | .complN t :: σ' => some { w with σ := .val cFalse :: .complN t :: σ' }
        | .complT :: σ' => some { w with σ := .val cTrue :: .complT :: σ' }
        | _ => none)
  | .kUnwrap =>
      ws.mapM (fun w =>
        match w.σ with
        | .complN t :: σ' => some { w with σ := t :: σ' }
        | .complT :: σ' => some { w with σ := .val anyV :: σ' }  -- dead path
        | _ => none)
  | .kIMeth nm n =>
      if mopArity nm == some n then
        ws.mapM (fun w =>
          match popTyN n (.val anyV) w.σ with
          | some σ' =>
              match popTy (.val cObj) σ' with
              | some σ'' => some { w with σ := .complN (mopResult nm) :: σ'' }
              | none => none
          | none => none)
      else none
  | .kMkList n =>
      ws.mapM (fun w =>
        match popTyN n (.val anyV) w.σ with
        | some σ' => some { w with σ := .val cList :: σ' }
        | none => none)
  | .kNewSlot sn =>
      if (slotOfName sn).isSome then
        ws.mapM (fun w =>
          match popTy (.val anyV) w.σ with
          | some σ' => some { w with σ := .val cObj :: σ' }
          | none => none)
      else none
  | _ => some ws

/-- Split worlds at a test of x with then-type T. -/
def splitWorlds (x : «String») (T : STy) (ws : Worlds) : Option Worlds :=
  match ws.mapM (fun (w : World) =>
    match tyLookup w.Γ x with
    | none => none
    | some S =>
        let thenS := tyMeet S T
        let elseS := tyRemove S T
        -- at least one side must be possible; emit verdict + refined Γ
        let out : List World :=
          (if tyNonempty thenS then [{ Γ := (x, thenS) :: w.Γ, σ := .val cTrue :: w.σ }] else [])
          ++ (if tyNonempty elseS then [{ Γ := (x, elseS) :: w.Γ, σ := .val cFalse :: w.σ }] else [])
        if out.isEmpty then none else (some out : Option (List World))) with
  | none => none
  | some wss => some (List.flatten wss)

/- Loop join: every falls-world must come back to the loop-entry
   stack (neutrality); the continuation runs from those worlds. -/
def checkLoopBody (rbody : TCResult) (site : Instr)
    (σ₀ : List STy) (k : Worlds → TCResult) : TCResult :=
  match rbody with
  | .reject site' why => .reject site' why
  | .flows fb =>
      let neutral := fb.falls.all (fun w => w.σ == σ₀)
      if neutral then
        match k fb.falls with
        | .flows fr => .flows { exits := fb.exits || fr.exits, falls := fr.falls, assumes := fb.assumes ++ fr.assumes }
        | res => res
      else .reject site "loop body is not stack-neutral"

def checkSeq : SigTable → STy → Worlds → List Instr → TCResult
  | _, _, ws, [] => .flows { exits := Bool.false, falls := ws, assumes := [] }
  | _, r, ws, .kRet :: _ =>
      -- every world returns: complN payload ⊑ r, or a throw
      if ws.all (fun w =>
        match w.σ with
        | .complN t :: _ => tmoves t r
        | .complT :: _ => Bool.true
        | _ => Bool.false) then
        .flows { exits := Bool.true, falls := [], assumes := [] }
      else .reject .kRet "kRet: payload does not match the frame's destiny r"
  | sigs, r, ws, .kIte t e :: rest =>
      -- dispatch each world on its verdict; split both-verdict worlds
      let dispatch (w : World) : Option (Worlds × Worlds) :=
        match w.σ with
        | .isValue (.boolean Bool.true) :: σ' => some ([{ w with σ := σ' }], [])
        | .isValue (.boolean Bool.false) :: σ' => some ([], [{ w with σ := σ' }])
        | .val m :: σ' =>
            if m == cTrue then some ([{ w with σ := σ' }], [])
            else if m == cFalse then some ([], [{ w with σ := σ' }])
            else if (m - (m &&& boolV)) == 0 then
              some ([{ w with σ := σ' }], [{ w with σ := σ' }])
            else none
        | _ => none
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
  | sigs, r, ws, .kEval ex :: rest =>
      -- tests on a variable SPLIT the worlds
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
        | some t => tmoves t (.val boolV)
        | none => Bool.false) then
        checkLoopBody (checkSeq sigs r ws body) (.kRepeatWhile c body)
          (ws.head?.map World.σ |>.getD []) (fun wsf => checkSeq sigs r wsf rest)
      else .reject (.kRepeatWhile c body) "loop condition is not boolean"
  | sigs, r, ws, .kRepeatTest c body :: rest =>
      match ws.mapM (fun (w : World) => popTy (.val boolV) w.σ) with
      | none => .reject (.kRepeatTest c body) "loop verdict is not boolean"
      | some ws' =>
          let ws'' := ws.zip ws' |>.map (fun (w, σ') => { w with σ := σ' })
          checkLoopBody (checkSeq sigs r ws'' body) (.kRepeatTest c body)
            (ws''.head?.map World.σ |>.getD []) (fun wsf => checkSeq sigs r wsf rest)
  | sigs, r, ws, .kForStart x body :: rest =>
      match ws.mapM (fun (w : World) => popTy (.val cList) w.σ) with
      | none => .reject (.kForStart x body) "for-each over a non-list"
      | some ws' =>
          let ws'' := (ws.zip ws').map (fun (w, σ') =>
            { w with Γ := (x, .val langV) :: w.Γ, σ := σ' })
          checkLoopBody (checkSeq sigs r ws'' body) (.kForStart x body)
            (ws''.head?.map World.σ |>.getD []) (fun wsf => checkSeq sigs r wsf rest)
  | sigs, r, ws, .kForBody x _ body :: rest =>
      let ws' := ws.map (fun w => { w with Γ := (x, .val langV) :: w.Γ })
      checkLoopBody (checkSeq sigs r ws' body) (.kForBody x [] body)
        (ws'.head?.map World.σ |>.getD []) (fun wsf => checkSeq sigs r wsf rest)
  | sigs, r, ws, .kAssert :: rest =>
      -- asserts: the trueVal worlds continue; falseVal worlds are
      -- ASSUMED away (proof debt recorded); a both-verdict world
      -- continues with its false side assumed away
      let rec step (w : World) : World × Bool :=
        match w.σ with
        | .isValue (.boolean Bool.true) :: σ' => ({ w with σ := σ' }, Bool.false)
        | .val m :: σ' =>
            if m == cTrue then ({ w with σ := σ' }, Bool.false)
            else ({ w with σ := σ' }, Bool.true)
        | _ => (w, Bool.true)   -- non-boolean verdict: fell-world
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

def typecheckSeq (sigs : SigTable) (r : STy) (Γ : TyEnv) (seq : List Instr) : TCResult :=
  checkSeq sigs r [{ Γ := Γ, σ := [] }] seq

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
