import Metalanguage.Grammar
/- # Static typechecking of compiled instruction sequences. -/

/- ## Static typing of compiled instruction sequences
   Types classify the PAYLOAD; delivery is always a completion.
   `typeOfE (call f as)`: check each argument against `paramTys(f)`,
   push `retTy(f)` — the runtime self-test (propagate-or-unwrap) is
   implicit in that one rule. -/

/- Refinement: leaves mirror JSValue constructors exactly (number,
   boolean, str, obj, listV, descV); `any` is the top of the value
   lattice (an ECMAScript language value of unknown shape). Demands
   are strict only where the runtime contract is unconditional
   (kIte/kAssert/kRepeatTest pop .boolean; kTest's verdict). -/
inductive STy where
  | any | number | boolean | str | obj | list | descV
  | complOf (t : STy)   -- a completion wrapping a t-typed payload
  | unit
  deriving Repr, BEq, DecidableEq

/-- Subtyping: covariant under complOf, `any` absorbs. -/
def tmoves : STy → STy → Bool
  | .complOf a, .complOf b => tmoves a b
  | _, .any => Bool.true
  | t, t' => t == t'

def leList : List STy → List STy → Bool
  | [], [] => Bool.true
  | t :: ts, t' :: ts' => tmoves t t' && leList ts ts'
  | _, _ => Bool.false

def typeOfV : JSValue → STy
  | .boolean _ => .boolean
  | .obj _ => .obj
  | .listV _ => .list
  | .compl _ v => .complOf (typeOfV v)
  | _ => .any

abbrev SigTable := List («String» × (List STy × STy))

def sigFind : SigTable → «String» → Option (List STy × STy)
  | [], _ => none
  | (n, s) :: rest, f => if n == f then some s else sigFind rest f

abbrev TyEnv := List («String» × STy)

def zipTy : List «String» → List STy → TyEnv
  | [], [] => []
  | x :: xs, t :: ts => (x, t) :: zipTy xs ts
  | _, _ => []

def tyLookup : TyEnv → «String» → Option STy
  | [], _ => none
  | (n, t) :: r, x => if n == x then some t else tyLookup r x

def mopArity : «String» → Option Nat   -- MOP internal methods (receiver excluded)
  | "Get" => some 2
  | "GetOwnProperty" => some 1
  | "GetPrototypeOf" => some 0
  | _ => none

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
  | .nat _ => some STy.any
  | .const v => some (typeOfV v)
  | .varNotPresent _ => some .boolean
  | .call f as =>
      match sigFind sigs f with
      | some (ps, ret) =>
          -- pointwise subtyping; trailing parameter optional (spec:
          -- Call(F, V) elides the arguments List)
          match typesOf sigs Γ as with
          | some ts =>
              -- args/arity checked; the RESULT is the callee's
              -- declared retTy: justified because the callee body is
              -- certified ⊢_retTy (every exit returns complOf retTy)
              if leList ts ps
                 || (as.length == ps.length - 1
                     && leList ts (ps.dropLast))
              then some ret else none
          | none => none
      | none => none
  | .imeth nm recv args =>
      -- MOP: receiver/args dynamically tested at runtime; payload any
      match mopArity nm with
      | some k =>
          if args.length == k && (typeOfE sigs Γ recv).isSome
             && (typesOf sigs Γ args).isSome
          then some .any else none
      | none => none
  | .listE es =>
      if (typesOf sigs Γ es).isSome then some .list else none
  | .ifield _ x =>
      -- field reads yield a VALUE (or undefined on non-descriptors):
      -- pDescField is a dynamic guard, so the result is `any`
      if (typeOfE sigs Γ x).isSome then some STy.any else none
  | .isObject x | .isNotObject x | .isNotUndefined x | .hasCall x | .hasCtor x
  | .isU x | .isBoolVal _ x | .isStrVal _ x | .isNullOrUnd x | .isNull x
  | .isType _ x | .hasField _ x =>
      -- predicate forms are Boolean; the prim inputs are dynamic (any)
      if (typeOfE sigs Γ x).isSome then some .boolean else none
termination_by e => sizeOf e
end

/-- Summary of the terminating behaviors of a path set:
   - exits: some path returns (kRet — the frame delivers to its caller)
   - breaks: some path breaks out of the ENCLOSING loop, with the
     stack/env at the break point (neutrality forces these to equal
     the loop-entry stack)
   - falls: some path runs off the end of the list, with stack/env.
   Divergence is silent: an infinite loop contributes no outcome. -/
structure Flows where
  exits  : Bool
  breaks : Option (List STy × TyEnv)
  falls  : Option (List STy × TyEnv)
  deriving Repr, BEq

/- Result of checking an instruction list: the flow summary, or a
   rejection AT an instruction with a reason and abstract stack. -/
inductive TCResult where
  | flows (f : Flows)
  | reject (site : Instr) (why : «String») (σ : List STy)
  deriving Repr

/-- Frame-level demand: every path returns, nothing falls through,
   no unconsumed break (a break at frame top has no loop to join). -/
def terminal (f : Flows) : Bool :=
  f.exits && f.breaks.isNone && f.falls.isNone

def isOk (r : TCResult) : Bool :=
  match r with
  | .reject _ _ _ => Bool.false
  | _ => Bool.true


def popTy (t : STy) (σ : List STy) : Option (List STy) :=
  match σ with
  | t' :: σ' => if tmoves t' t then some σ' else none
  | [] => none

/-- Input/output types of the one-input prims. pWrapC is
   input-dependent (`t ↦ complOf t`) and handled inline in checkSeq. -/
def primTys (p : Prim) : Option (STy × STy) :=
  match p with
  | .pThrowC => some (.any, .complOf .any)
  -- bedrock predicates: any -> boolean (runtime tests are dynamic)
  | .pIsObj | .pIsNotObj | .pIsNotU | .pHasCall | .pHasCtor | .pIsU
  | .pIsTrue | .pIsFalse | .pNullOrUnd | .pIsNull
  | .pIsType _ | .pHasField _ | .pIsStr _ => some (.any, .boolean)
  | .pDescField _ => some (.any, .any)  -- dynamic desc guard
  | .pWrapC => none                     -- t ↦ complOf t, inline

def popTyN : Nat → STy → List STy → Option (List STy)
  | 0, _, σ => some σ
  | k + 1, t, σ =>
      match popTy t σ with
      | some σ' => popTyN k t σ'
      | none => none


/- Branch join for variable types: names bound on ALL falling paths
   survive (intersection); a name bound in both joins at the LUB. -/
def lub (t t' : STy) : STy := if t == t' then t else .any

def ΓUnion : TyEnv → TyEnv → TyEnv
  | [], _ => []
  | (n, t) :: r, Γ₂ =>
      match tyLookup Γ₂ n with
      | some t' => (n, lub t t') :: ΓUnion r Γ₂
      | none => ΓUnion r Γ₂

/- After a continuation is checked from the join point, the breaks it
   reports target loops OUTSIDE the construct; combine with the
   construct's own pending breaks (stacks agree by neutrality). -/
def orBreaks (b₁ b₂ : Option (List STy × TyEnv)) : Option (List STy × TyEnv) :=
  match b₁, b₂ with
  | some (σ₁, Γ₁), some (σ₂, Γ₂) =>
      if σ₁ == σ₂ then some (σ₁, ΓUnion Γ₁ Γ₂) else none
  | some b, none | none, some b => some b
  | none, none => none

/- Branch join: exits are absorbed (a returning path contributes
   nothing to the continuation); stacks must agree; envs join at the
   intersection-with-lub (a name bound on one path only does not
   survive). -/
def joinFlows (f₁ f₂ : Flows) : Option Flows :=
  let join (b₁ b₂ : Option (List STy × TyEnv)) :
      Option (Option (List STy × TyEnv)) :=
    match b₁, b₂ with
    | some (σ₁, Γ₁), some (σ₂, Γ₂) =>
        if σ₁ == σ₂ then some (some (σ₁, ΓUnion Γ₁ Γ₂)) else none
    | some b, none | none, some b => some (some b)
    | none, none => some none
  match join f₁.breaks f₂.breaks, join f₁.falls f₂.falls with
  | none, _ | _, none => none
  | some breaks, some falls =>
      some { exits := f₁.exits || f₂.exits, breaks := breaks, falls := falls }

/- Loop join: the body's iteration-completion (falls) and breaks must
   be neutral — equal to the loop-entry stack — since both land at the
   continuation (exhaustion and break respectively) with that stack.
   Exits pass through; breaks are CONSUMED by this loop; the
   continuation's own breaks (to an outer loop) survive. -/
def checkLoopBody (rbody : TCResult) (site : Instr)
    (σ : List STy) (k : TyEnv → List STy → TCResult) : TCResult :=
  match rbody with
  | .reject site' why s => .reject site' why s
  | .flows fb =>
      let fallOk := fb.falls.isNone || (fb.falls.isEqSome (σ, fb.falls.get!.2))
      let brkOk := fb.breaks.isNone || (fb.breaks.get!.1 == σ)
      if fallOk && brkOk then
        -- continuation entered from the loop-entry stack, with the
        -- bindings of the fall/break paths (they agree on the stack;
        -- envs are unioned if both present)
        let Γnext := match fb.falls, fb.breaks with
          | some (_, Γ₁), some (_, Γ₂) => ΓUnion Γ₁ Γ₂
          | some (_, Γ₁), none => Γ₁
          | none, some (_, Γ₁) => Γ₁
          | none, none => none
        match Γnext, k with
        | _, _ => -- dispatch manually below
            match Γnext with
            | none => .flows { exits := fb.exits, breaks := none, falls := none }
            | some Γ' =>
                match k Γ' σ with
                | .flows fr => .flows { exits := fb.exits || fr.exits, breaks := fr.breaks, falls := fr.falls }
                | res => res
      else .reject site "loop body not neutral at falls/breaks" σ

/-- Do the top `ps.length` entries satisfy `ps`? The head of the
   stack is the LAST argument, so compare against reversed ps. -/
def popArgs (ps σ : List STy) : Bool :=
  σ.length ≥ ps.length && leList ps.reverse (σ.take ps.length).reverse

/- `checkSeq sigs r Γ is σ`: walk instruction list `is` with ambient
   return type r (the frame's destiny), variable types Γ, abstract
   stack σ. kRet demands `complOf r` — exit uniformity, typed. -/


def checkSeq : SigTable → STy → TyEnv → List Instr → List STy → TCResult
  | _, _, Γ, [], σ => .flows { exits := Bool.false, breaks := none, falls := some (σ, Γ) }
  | sigs, r, Γ, .kEval e :: rest, σ =>
      match typeOfE sigs Γ e with
      | some t => checkSeq sigs r Γ rest (t :: σ)
      | none => .reject (.kEval e) "ill-typed expression (unbound variable, unknown operation, or argument type mismatch)" σ
  | sigs, r, Γ, .kPrim1 .pWrapC :: rest, σ =>
      match σ with
      | t :: σ' => checkSeq sigs r Γ rest (.complOf t :: σ')
      | [] => .reject (.kPrim1 .pWrapC) "pWrapC on empty stack" σ
  | sigs, r, Γ, .kPrim1 p :: rest, σ =>
      match primTys p with
      | some (tin, tout) =>
          match popTy tin σ with
          | some σ' => checkSeq sigs r Γ rest (tout :: σ')
          | none => .reject (.kPrim1 p) "prim expects a different top-of-stack type" σ
      | none => .reject (.kPrim1 p) "unreachable (pWrapC above)" σ
  | sigs, r, Γ, .kCall f n :: rest, σ =>
      match sigFind sigs f with
      | some (ps, ret) =>
          if ps.length == n then
            -- args are checked against the signature HERE (pointwise
            -- subtyping), so the callee receives a certified env
            if popArgs ps σ then
              checkSeq sigs r Γ rest (.complOf ret :: σ.drop n)
            else .reject (.kCall f n) "call: argument types do not match signature" σ
          else .reject (.kCall f n) "call arity does not match signature" σ
      | none => .reject (.kCall f n) "no signature for callee" σ
  | sigs, r, Γ, .kSet x :: rest, σ =>
      match σ with
      | t :: σ' => checkSeq sigs r ((x, t) :: Γ) rest σ'
      | [] => .reject (.kSet x) "kSet on empty stack" σ
  | sigs, r, Γ, .kPop :: rest, σ =>
      match σ with
      | _ :: σ' => checkSeq sigs r Γ rest σ'
      | [] => .reject .kPop "kPop on empty stack" σ
  | sigs, r, Γ, .kIte t e :: rest, σ =>
      match popTy .boolean σ with
      | none => .reject (.kIte t e) "kIte: condition is not boolean" σ
      | some σ' =>
          match checkSeq sigs r Γ t σ', checkSeq sigs r Γ e σ' with
          | .reject site why s, _ => .reject site why s
          | _, .reject site why s => .reject site why s
          | .flows f₁, .flows f₂ =>
              match joinFlows f₁ f₂ with
              | none => .reject (.kIte t e) "branches diverge (stacks differ at falls/breaks)" σ'
              | some fj =>
                  match fj.falls with
                  | some (σⱼ, Γⱼ) =>
                      match checkSeq sigs r Γⱼ rest σⱼ with
                      | .flows fr => .flows { fr with breaks := orBreaks fj.breaks fr.breaks, exits := fj.exits || fr.exits }
                      | res => res
                  | none =>
                      -- no path falls through: remaining flows are exits ∪ breaks
                      .flows { exits := fj.exits, breaks := fj.breaks, falls := none }
  | sigs, r, Γ, .kAssert :: rest, σ =>
      match popTy .boolean σ with
      | some σ' => checkSeq sigs r Γ rest σ'
      | none => .reject .kAssert "kAssert: top is not boolean" σ
  | _, r, _, .kRet :: _, .complOf t' :: _ =>
      if tmoves t' r then .flows { exits := Bool.true, breaks := none, falls := none }
      else .reject .kRet "kRet: returned payload does not match the frame's destiny r" (.complOf t' :: [])
  | _, _, _, .kRet :: _, σ =>
      .reject .kRet "kRet: top of stack is not complOf r" σ
  | sigs, r, Γ, .kTest :: rest, .complOf t :: σ' =>
      checkSeq sigs r Γ rest (.boolean :: .complOf t :: σ')
  | _, _, _, .kTest :: _, σ =>
      .reject .kTest "kTest: top of stack is not a completion" σ
  | sigs, r, Γ, .kUnwrap :: rest, .complOf t :: σ' =>
      checkSeq sigs r Γ rest (t :: σ')
  | _, _, _, .kUnwrap :: _, σ =>
      .reject .kUnwrap "kUnwrap: top of stack is not a completion" σ
  | sigs, r, Γ, .kIMeth nm n :: rest, σ =>
      if mopArity nm == some n then
        match popTyN (n + 1) .any σ with
        | some σ' => checkSeq sigs r Γ rest (.complOf .any :: σ')
        | none => .reject (.kIMeth nm n) "MOP dispatch: receiver/args stack mismatch" σ
      else .reject (.kIMeth nm n) "unknown MOP method or wrong arity" σ
  | _, _, Γ, .kBreak :: _, σ =>
      -- break out of the enclosing loop: neutral control transfer;
      -- the loop join consumes it (a break at frame top rejects in
      -- the terminal demand)
      .flows { exits := Bool.false, breaks := some (σ, Γ), falls := none }
  | sigs, r, Γ, .kMkList n :: rest, σ =>
      match popTyN n .any σ with
      | some σ' => checkSeq sigs r Γ rest (.list :: σ')
      | none => .reject (.kMkList n) "kMkList: element stack mismatch" σ
  | sigs, r, Γ, .kNewSlot sn :: rest, σ =>
      match popTy .any σ with
      | some σ' => checkSeq sigs r Γ rest (.obj :: σ')
      | none => .reject (.kNewSlot sn) "kNewSlot on empty stack" σ
  | sigs, r, Γ, .kRepeatWhile c body :: rest, σ =>
      if typeOfE sigs Γ c != some .boolean
      then .reject (.kRepeatWhile c body) "loop condition is not boolean" σ
      else checkLoopBody (checkSeq sigs r Γ body σ) (.kRepeatWhile c body) σ
        (fun Γ' σ' => checkSeq sigs r Γ' rest σ')
  | sigs, r, Γ, .kRepeatTest c body :: rest, σ =>
      -- pops the boolean verdict: loop (body neutral) or fall through
      match popTy .boolean σ with
      | none => .reject (.kRepeatTest c body) "loop verdict is not boolean" σ
      | some σ' => checkLoopBody (checkSeq sigs r Γ body σ') (.kRepeatTest c body) σ'
        (fun Γ' σ'' => checkSeq sigs r Γ' rest σ'')
  | sigs, r, Γ, .kForStart x body :: rest, σ =>
      match popTy .any σ with
      | none => .reject (.kForStart x body) "for-each over empty stack" σ
      | some σ' => checkLoopBody (checkSeq sigs r ((x, .any) :: Γ) body σ')
        (.kForStart x body) σ'
        (fun Γ' σ'' => checkSeq sigs r Γ' rest σ'')
  | sigs, r, Γ, .kForBody x _ body :: rest, σ =>
      checkLoopBody (checkSeq sigs r ((x, .any) :: Γ) body σ)
        (.kForBody x [] body) σ
        (fun Γ' σ'' => checkSeq sigs r Γ' rest σ'')

/- A frame is well typed if every path exits via kRet (falling off the
   end is the runtime's loud `fell`). -/
def typecheckSeq (sigs : SigTable) (r : STy) (Γ : TyEnv) (seq : List Instr) : TCResult :=
  checkSeq sigs r Γ seq []

/- Check one AO: params get their declared types from the signature
   table; arity must agree with the registry. Result: none = well
   typed; some r = the first rejection (with reason and stack). -/
def typecheckAO (sigs : SigTable)
    (name : «String») (params : List «String») (body : List Instr) : Option TCResult :=
  match sigFind sigs name with
  | none =>
      some (.reject (body.head?.getD .kRet)
        (name ++ " has no entry in the signature table") [])
  | some (paramTys, ret2) =>
      if params.length != paramTys.length then
        some (.reject (body.head?.getD .kRet)
          (name ++ ": registry arity ≠ signature arity") [])
      else match typecheckSeq sigs ret2 (zipTy params paramTys) body with
        | .flows f => if terminal f then none else some (.flows f)
        | r => some r

/- First ill-typed AO in the registry, by name. none = all well typed. -/
def typecheckReg (sigs : SigTable) (reg : AOReg) : Option («String» × TCResult) :=
  match reg with
  | [] => none
  | (name, (params, prog)) :: rest =>
      match typecheckAO sigs name params (compileSteps prog) with
      | some r => some (name, r)
      | none => typecheckReg sigs rest

def typecheckRegOk (sigs : SigTable) (reg : AOReg) : Bool :=
  (typecheckReg sigs reg).isNone

