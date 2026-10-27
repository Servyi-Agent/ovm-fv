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
  | compl | unit
  deriving Repr, BEq, DecidableEq

/-- `t ≤ t'` in the value lattice: `any` absorbs. Defined via
   DecidableEq so that simp/omega can reason under it. -/
def tmoves (t t' : STy) : Bool :=
  decide (t = t' ∨ t' = STy.any)

def leList : List STy → List STy → Bool
  | [], [] => Bool.true
  | t :: ts, t' :: ts' => tmoves t t' && leList ts ts'
  | _, _ => Bool.false

def typeOfV : JSValue → STy
  | .boolean _ => .boolean
  | .obj _ => .obj
  | .listV _ => .list
  | .compl _ _ => .compl
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
              -- args/arity checked; the RESULT is typed `any`: the
              -- machine's self-test decomposition nets any, and a
              -- refined result would not be preserved by steps
              if leList ts ps
                 || (as.length == ps.length - 1
                     && leList ts (ps.dropLast))
              then some STy.any else none
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

/- Result of checking a path: exited via kRet, fell through with the
   given abstract stack, or rejected AT an instruction with a reason
   and the abstract stack at that point. -/
inductive TCResult where
  | exits
  | falls (σ : List STy) (Γ : TyEnv)
  | reject (site : Instr) (why : «String») (σ : List STy)
  deriving Repr

/- Branch join for variable types: names bound on ALL falling paths
   survive (intersection); a name bound in both joins at the LUB.
   One-sided bindings are dropped — the machine takes one branch, so
   the other's bindings do not exist at runtime, and the continuation
   must not rely on them. -/
def lub (t t' : STy) : STy := if t == t' then t else .any

def ΓUnion : TyEnv → TyEnv → TyEnv
  | [], _ => []
  | (n, t) :: r, Γ₂ =>
      match tyLookup Γ₂ n with
      | some t' => (n, lub t t') :: ΓUnion r Γ₂
      | none => ΓUnion r Γ₂

def popTy (t : STy) (σ : List STy) : Option (List STy) :=
  match σ with
  | t' :: σ' => if tmoves t' t then some σ' else none
  | [] => none

def primSig (p : Prim) : STy × STy :=
  match p with
  | .pWrapC | .pThrowC => (.any, .compl)
  -- bedrock predicates: any -> boolean (runtime tests are dynamic)
  | .pIsObj | .pIsNotObj | .pIsNotU | .pHasCall | .pHasCtor | .pIsU
  | .pIsTrue | .pIsFalse | .pNullOrUnd | .pIsNull
  | .pIsType _ | .pHasField _ | .pIsStr _ => (.any, .boolean)
  | .pDescField _ => (.any, .any)   -- dynamic desc guard, else undefined

def popTyN : Nat → STy → List STy → Option (List STy)
  | 0, _, σ => some σ
  | k + 1, t, σ =>
      match popTy t σ with
      | some σ' => popTyN k t σ'
      | none => none

/- Loop bodies: stack-neutral (loop invariant) or exit via kRet;
   bindings made in the body persist after the loop (kSet is frame
   state at runtime). Inlined into the four loop arms so that every
   recursive call of checkSeq is on a structural subterm. -/
def checkNeutral (rbody : TCResult) (site : Instr)
    (rest : List Instr) (σ : List STy) (k : TyEnv → List STy → TCResult) : TCResult :=
  match rbody with
  | .reject site' why s => .reject site' why s
  | .exits => .exits
  | .falls σ' Γ' =>
      if σ' == σ then k Γ' σ
      else .reject site "loop body is not stack-neutral" σ

/-- Do the top `ps.length` entries satisfy `ps`? The head of the
   stack is the LAST argument, so compare against reversed ps. -/
def popArgs (ps σ : List STy) : Bool :=
  σ.length ≥ ps.length && leList ps.reverse (σ.take ps.length).reverse

/- `checkSeq sigs Γ is σ`: walk instruction list `is` with
   variable types Γ and abstract stack σ. -/
def checkSeq : SigTable → TyEnv → List Instr → List STy → TCResult
  | _, Γ, [], σ => .falls σ Γ
  | sigs, Γ, .kEval e :: rest, σ =>
      match typeOfE sigs Γ e with
      | some t => checkSeq sigs Γ rest (t :: σ)
      | none => .reject (.kEval e) "ill-typed expression (unbound variable, unknown operation, or argument type mismatch)" σ
  | sigs, Γ, .kPrim1 p :: rest, σ =>
      let (tin, tout) := primSig p
      match popTy tin σ with
      | some σ' => checkSeq sigs Γ rest (tout :: σ')
      | none => .reject (.kPrim1 p) "prim expects a different top-of-stack type" σ
  | sigs, Γ, .kCall f n :: rest, σ =>
      match sigFind sigs f with
      | some (ps, _) =>
          if ps.length == n then
            -- args are checked against the signature HERE (pointwise
            -- subtyping), so the callee receives a certified env
            if popArgs ps σ then
              checkSeq sigs Γ rest (.compl :: σ.drop n)
            else .reject (.kCall f n) "call: argument types do not match signature" σ
          else .reject (.kCall f n) "call arity does not match signature" σ
      | none => .reject (.kCall f n) "no signature for callee" σ
  | sigs, Γ, .kSet x :: rest, σ =>
      match σ with
      | t :: σ' => checkSeq sigs ((x, t) :: Γ) rest σ'
      | [] => .reject (.kSet x) "kSet on empty stack" σ
  | sigs, Γ, .kPop :: rest, σ =>
      match σ with
      | _ :: σ' => checkSeq sigs Γ rest σ'
      | [] => .reject .kPop "kPop on empty stack" σ
  | sigs, Γ, .kIte t e :: rest, σ =>
      match popTy .boolean σ with
      | none => .reject (.kIte t e) "kIte: condition is not boolean" σ
      | some σ' =>
          let join (r₁ r₂ : TCResult) : TCResult :=
            match r₁, r₂ with
            | .reject site why s, _ => .reject site why s
            | _, .reject site why s => .reject site why s
            | .exits, r | r, .exits => r
            | .falls σ₁ Γ₁, .falls σ₂ Γ₂ =>
                if σ₁ == σ₂ then .falls σ₁ (ΓUnion Γ₁ Γ₂)
                else .reject (.kIte t e) "branches join with different stacks" σ'
          match join (checkSeq sigs Γ t σ') (checkSeq sigs Γ e σ') with
          | .exits => .exits
          | .falls σⱼ Γⱼ => checkSeq sigs Γⱼ rest σⱼ
          | r => r
  | sigs, Γ, .kAssert :: rest, σ =>
      match popTy .boolean σ with
      | some σ' => checkSeq sigs Γ rest σ'
      | none => .reject .kAssert "kAssert: top is not boolean" σ
  | _, _, .kRet :: _, σ =>
      match σ with
      | .compl :: _ => .exits        -- value return: wire format is compl
      | _ => .reject .kRet "kRet: top of stack is not a completion (or empty/unit return)" σ
  | sigs, Γ, .kTest :: rest, σ =>
      match popTy .compl σ with
      | some σ' => checkSeq sigs Γ rest (.boolean :: .compl :: σ')
      | none => .reject .kTest "kTest: top of stack is not a completion" σ
  | sigs, Γ, .kUnwrap :: rest, σ =>
      -- payload type is not tracked through compl: arrives as any
      match popTy .compl σ with
      | some σ' => checkSeq sigs Γ rest (.any :: σ')
      | none => .reject .kUnwrap "kUnwrap: top of stack is not a completion" σ
  | sigs, Γ, .kIMeth nm n :: rest, σ =>
      if mopArity nm == some n then
        match popTyN (n + 1) .any σ with
        | some σ' => checkSeq sigs Γ rest (.compl :: σ')
        | none => .reject (.kIMeth nm n) "MOP dispatch: receiver/args stack mismatch" σ
      else .reject (.kIMeth nm n) "unknown MOP method or wrong arity" σ
  | sigs, Γ, .kMkList n :: rest, σ =>
      match popTyN n .any σ with
      | some σ' => checkSeq sigs Γ rest (.list :: σ')
      | none => .reject (.kMkList n) "kMkList: element stack mismatch" σ
  | sigs, Γ, .kNewSlot sn :: rest, σ =>
      match popTy .any σ with
      | some σ' => checkSeq sigs Γ rest (.obj :: σ')
      | none => .reject (.kNewSlot sn) "kNewSlot on empty stack" σ
  | sigs, Γ, .kRepeatWhile c body :: rest, σ =>
      if typeOfE sigs Γ c != some .boolean
      then .reject (.kRepeatWhile c body) "loop condition is not boolean" σ
      else checkNeutral (checkSeq sigs Γ body σ) (.kRepeatWhile c body) rest σ
        (fun Γ' σ' => checkSeq sigs Γ' rest σ')
  | sigs, Γ, .kRepeatTest c body :: rest, σ =>
      -- pops the boolean verdict: loop (body neutral) or fall through
      match popTy .boolean σ with
      | none => .reject (.kRepeatTest c body) "loop verdict is not boolean" σ
      | some σ' => checkNeutral (checkSeq sigs Γ body σ') (.kRepeatTest c body) rest σ'
        (fun Γ' σ'' => checkSeq sigs Γ' rest σ'')
  | sigs, Γ, .kForStart x body :: rest, σ =>
      match popTy .any σ with
      | none => .reject (.kForStart x body) "for-each over empty stack" σ
      | some σ' => checkNeutral (checkSeq sigs ((x, .any) :: Γ) body σ')
        (.kForStart x body) rest σ'
        (fun Γ' σ'' => checkSeq sigs Γ' rest σ'')
  | sigs, Γ, .kForBody x _ body :: rest, σ =>
      checkNeutral (checkSeq sigs ((x, .any) :: Γ) body σ)
        (.kForBody x [] body) rest σ
        (fun Γ' σ'' => checkSeq sigs Γ' rest σ'')

/- A frame is well typed if every path exits via kRet (falling off the
   end is the runtime's loud `fell`). -/
def typecheckSeq (sigs : SigTable) (Γ : TyEnv) (seq : List Instr) : TCResult :=
  checkSeq sigs Γ seq []

/- Check one AO: params get their declared types from the signature
   table; arity must agree with the registry. Result: none = well
   typed; some r = the first rejection (with reason and stack). -/
def typecheckAO (sigs : SigTable)
    (name : «String») (params : List «String») (body : List Instr) : Option TCResult :=
  match sigFind sigs name with
  | none =>
      some (.reject (body.head?.getD .kRet)
        (name ++ " has no entry in the signature table") [])
  | some (paramTys, _) =>
      if params.length != paramTys.length then
        some (.reject (body.head?.getD .kRet)
          (name ++ ": registry arity ≠ signature arity") [])
      else match typecheckSeq sigs (zipTy params paramTys) body with
        | .exits => none
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

/-- Non-rejection as a Bool (for the subject-reduction development). -/
def isOk (r : TCResult) : Bool :=
  match r with
  | .reject _ _ _ => Bool.false
  | _ => Bool.true
