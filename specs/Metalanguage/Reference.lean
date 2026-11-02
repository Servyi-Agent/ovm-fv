import Metalanguage.Grammar
import Metalanguage.Semantics

/- # Reference machine: fuel-total big-step, statement granularity.

    The spec-shaped executable reading of a transcription: one `Step`
    = one fuel; expressions evaluate atomically (structural descent is
    free); calls push a callee scope on the LEAN call stack (the env
    is the frame) and consume one fuel; abrupt completions propagate
    through the Except channel (the analog of the machine's
    kTest/kIte/kRet/kUnwrap self-test protocol). Either the fuel
    suffices and you get an answer, or you get `timeout` — which is a
    fuel-budget fact, never a program bug (bugs are `fell`). -/

/-- Function symbols: one per transcribed AO plus the native stubs.
    Calls in test programs go through these (see fnOfName), so the
    callee universe is closed and arity is checkable at construction
    sites. -/
inductive Fn where
  | isCallable | isConstructor | isDataDescriptor | isAccessorDescriptor
  | toPrimitive | ordinaryToPrimitive | toObject | getV | getMethod
  | ordinaryGet
  | get | call          -- native stubs (machine: compl false undefined)

def fnName : Fn → «String»
  | .isCallable => "IsCallable" | .isConstructor => "IsConstructor"
  | .isDataDescriptor => "IsDataDescriptor"
  | .isAccessorDescriptor => "IsAccessorDescriptor"
  | .toPrimitive => "ToPrimitive" | .ordinaryToPrimitive => "OrdinaryToPrimitive"
  | .toObject => "ToObject" | .getV => "GetV" | .getMethod => "GetMethod"
  | .ordinaryGet => "OrdinaryGet" | .get => "Get" | .call => "Call"

def fnOfName : «String» → Option Fn
  | "IsCallable" => some .isCallable | "IsConstructor" => some .isConstructor
  | "IsDataDescriptor" => some .isDataDescriptor
  | "IsAccessorDescriptor" => some .isAccessorDescriptor
  | "ToPrimitive" => some .toPrimitive
  | "OrdinaryToPrimitive" => some .ordinaryToPrimitive
  | "ToObject" => some .toObject | "GetV" => some .getV
  | "GetMethod" => some .getMethod | "OrdinaryGet" => some .ordinaryGet
  | "Get" => some .get | "Call" => some .call
  | _ => none

/-- Native stubs: machine parity is the kCall registry-miss arm
    (nativeOps => push compl false undefined). -/
def fnStub : Fn → Bool
  | .get | .call => Bool.true
  | _ => Bool.false

/-- Raw outcome. `fall` = ran off the end of THIS list (mid-loop that
    is normal continuation; at top level it becomes `fell`). -/
inductive RRaw where
  | fall (env : Env) (heap : Heap) (nl : Nat)
  | ok (v : JSValue) (heap : Heap) (nl : Nat)
  | abrupt (v : JSValue) (heap : Heap) (nl : Nat)
  | stuck (heap : Heap) (nl : Nat)
  | timeout

inductive RResult where
  | done (v : JSValue) (heap : Heap) (nl : Nat)
  | threw (v : JSValue) (heap : Heap) (nl : Nat)
  | fell (heap : Heap) (nl : Nat)
  | timeout

/-- The registry: bodies for the transcribed AOs (`none` = not
    registered; combined with fnStub this reproduces the machine's
    registry-then-native dispatch). -/
abbrev RefReg := Fn → Option (List «String» × Prog)

mutual
  /-- Statement level. One Step = one fuel. -/
  def revStep (reg : RefReg) : Nat → List Step → Env → Heap → Nat → RRaw
    | 0, _, _, heap, nl => .timeout
    | _ + 1, [], env, heap, nl => .fall env heap nl
    | n + 1, .ret v :: rest, env, heap, nl =>
        match revExpr reg n v env heap nl with
        | .ok v' heap' nl' => .ok v' heap' nl'
        | r => r
    | n + 1, .retE e :: rest, env, heap, nl =>
        match revExpr reg n e env heap nl with
        | .ok v' heap' nl' => .ok v' heap' nl'
        | r => r
    | n + 1, .retNewSlot sn vv :: rest, env, heap, nl =>
        match slotOfName sn, revExpr reg n (.nv vv) env heap nl with
        | some ord, .ok v heap' nl' =>
            .ok (.obj nl') (heapSet heap' nl'
              {(objWith .ordinary none) with slots := [(ord, v)]}) (nl' + 1)
        | none, .ok _ heap' nl' => .stuck heap' nl'
        | _, r => r
    | n + 1, .throw :: _, _, heap, nl =>
        .abrupt JSValue.undefined heap nl
    | n + 1, .setE x e :: rest, env, heap, nl =>
        match revExpr reg n e env heap nl with
        | .ok v heap' nl' => revStep reg n rest ((x, v) :: env) heap' nl'
        | r => r
    | n + 1, .letE x e :: rest, env, heap, nl =>
        match revExpr reg n e env heap nl with
        | .ok v heap' nl' => revStep reg n rest ((x, v) :: env) heap' nl'
        | r => r
    | n + 1, .assertE e :: rest, env, heap, nl =>
        match revExpr reg n e env heap nl with
        | .ok (.boolean Bool.true) heap' nl' =>
            revStep reg n rest env heap' nl'
        | .ok _ heap' nl' => .stuck heap' nl'
        | r => r
    | n + 1, .ifS c t e :: rest, env, heap, nl =>
        match revExpr reg n c env heap nl with
        | .ok (.boolean b) heap' nl' =>
            revStep reg n (if b then t ++ rest else e ++ rest) env heap' nl'
        | .ok _ heap' nl' => .stuck heap' nl'
        | r => r
    | n + 1, .forEach x e body :: rest, env, heap, nl =>
        match revExpr reg n e env heap nl with
        | .ok (.listV vs) heap' nl' =>
            revForEach reg n x vs body rest env heap' nl'
        | .ok _ heap' nl' => .stuck heap' nl'
        | r => r
    | n + 1, .elseM _ :: rest, env, heap, nl =>
        revStep reg n rest env heap nl
  termination_by n _ _ _ _ => (Prod.mk n 0 : Nat × Nat)

  /-- forEach iteration: bindings from each body run persist into the
      next (machine: kForBody re-arms with the current env); a body
      that RETURNS ends the whole frame. -/
  def revForEach : RefReg → Nat → «String» → List JSValue →
      List Step → List Step → Env → Heap → Nat → RRaw
    | reg, n + 1, _, [], _, rest, env, heap, nl =>
        revStep reg n rest env heap nl
    | _, 0, _, _, _, _, _, _, _ => .timeout
    | reg, n' + 1, x, v :: vs', body, rest, env, heap, nl =>
        match revStep reg n' body ((x, v) :: env) heap nl with
        | .fall env' heap'' nl'' =>
            revForEach reg n' x vs' body rest env' heap'' nl''
        | r => r
  termination_by _ n _ _ _ _ _ _ _ => (Prod.mk n 0 : Nat × Nat)

  /-- Expression level: structural descent (free); calls and
      method dispatch drop into the statement level at fuel-1. -/
  def revExpr (reg : RefReg) : Nat → Expr → Env → Heap → Nat → RRaw
    | _, .const v, _, heap, nl => .ok v heap nl
    | _, .nat n, _, heap, nl => .ok (.number ↑n) heap nl
    | _, .nv x, env, heap, nl =>
        match lookup env x with
        | some v => .ok v heap nl
        | none => .stuck heap nl
    | _, .varNotPresent x, env, heap, nl =>
        .ok (.boolean (lookup env x).isNone) heap nl
    | n, .isObject e, env, heap, nl =>
        match revExpr reg n e env heap nl with
        | .ok v heap' nl' => .ok (applyPrim heap' .pIsObj v) heap' nl'
        | r => r
    | n, .isNotObject e, env, heap, nl =>
        match revExpr reg n e env heap nl with
        | .ok v heap' nl' => .ok (applyPrim heap' .pIsNotObj v) heap' nl'
        | r => r
    | n, .isNotUndefined e, env, heap, nl =>
        match revExpr reg n e env heap nl with
        | .ok v heap' nl' => .ok (applyPrim heap' .pIsNotU v) heap' nl'
        | r => r
    | n, .hasCall e, env, heap, nl =>
        match revExpr reg n e env heap nl with
        | .ok v heap' nl' => .ok (applyPrim heap' .pHasCall v) heap' nl'
        | r => r
    | n, .hasCtor e, env, heap, nl =>
        match revExpr reg n e env heap nl with
        | .ok v heap' nl' => .ok (applyPrim heap' .pHasCtor v) heap' nl'
        | r => r
    | n, .isU e, env, heap, nl =>
        match revExpr reg n e env heap nl with
        | .ok v heap' nl' => .ok (applyPrim heap' .pIsU v) heap' nl'
        | r => r
    | n, .isBoolVal b e, env, heap, nl =>
        match revExpr reg n e env heap nl with
        | .ok v heap' nl' =>
            .ok (applyPrim heap' (if b then .pIsTrue else .pIsFalse) v)
              heap' nl'
        | r => r
    | n, .isStrVal s e, env, heap, nl =>
        match revExpr reg n e env heap nl with
        | .ok v heap' nl' => .ok (applyPrim heap' (.pIsStr s) v) heap' nl'
        | r => r
    | n, .isNullOrUnd e, env, heap, nl =>
        match revExpr reg n e env heap nl with
        | .ok v heap' nl' => .ok (applyPrim heap' .pNullOrUnd v) heap' nl'
        | r => r
    | n, .isNull e, env, heap, nl =>
        match revExpr reg n e env heap nl with
        | .ok v heap' nl' => .ok (applyPrim heap' .pIsNull v) heap' nl'
        | r => r
    | n, .isType ty e, env, heap, nl =>
        match revExpr reg n e env heap nl with
        | .ok v heap' nl' => .ok (applyPrim heap' (.pIsType ty) v) heap' nl'
        | r => r
    | n, .hasField nm e, env, heap, nl =>
        match revExpr reg n e env heap nl with
        | .ok v heap' nl' => .ok (applyPrim heap' (.pHasField nm) v) heap' nl'
        | r => r
    | n, .ifield nm e, env, heap, nl =>
        match revExpr reg n e env heap nl with
        | .ok v heap' nl' => .ok (applyPrim heap' (.pDescField nm) v) heap' nl'
        | r => r
    | n, .listE es, env, heap, nl =>
        revList reg n es env heap nl []
    | n, .imeth nm recv args, env, heap, nl =>
        match revExpr reg n recv env heap nl with
        | .ok (.obj loc) heap' nl' =>
            if args.length == 1 || nm == "GetPrototypeOf" then
              match nm, args, loc with
              | "Get", [p], _ =>
                  match revExpr reg n p env heap' nl' with
                  | .ok pv heap'' nl'' =>
                      revCall reg n .ordinaryGet [(.obj loc), pv, .obj loc]
                        env heap'' nl''
                  | r => r
              | "GetOwnProperty", [p], loc' =>
                  match revExpr reg n p env heap' nl' with
                  | .ok (.str s) heap'' nl'' =>
                      match heap'' loc' with
                      | some o =>
                          let k := PKey.str s
                          let d := (o.props.find? (fun (pk, _) => pk == k))
                            |>.map (·.2)
                          .ok (d.map JSValue.descV |>.getD JSValue.undefined)
                            heap'' nl''
                      | none => .stuck heap'' nl''
                  | .ok _ heap'' nl'' => .stuck heap'' nl''
                  | r => r
              | "GetPrototypeOf", [], loc' =>
                  match heap' loc' with
                  | some o =>
                      match o.proto with
                      | some l => .ok (.obj l) heap' nl'
                      | none => .ok JSValue.null heap' nl'
                  | none => .stuck heap' nl'
              | _, _, _ => .stuck heap' nl'
            else .stuck heap' nl'
        | .ok _ heap' nl' => .stuck heap' nl'
        | r => r
    | n, .call fname args, env, heap, nl =>
        match fnOfName fname with
        | some f => revArgs reg n args env heap nl f []
        | none => .stuck heap nl
  termination_by n e _ _ _ => (n, sizeOf e)


  /-- Argument evaluation in order; then dispatch to the callee body
      (registry hit), the native stub, or fell (unknown). -/
  def revArgs : RefReg → Nat → List Expr → Env → Heap → Nat →
      Fn → List JSValue → RRaw
    | _, 0, _, _, _, _, _, _ => .timeout
    | reg, n' + 1, [], _, heap, nl, f, acc =>
        match reg f, fnStub f with
        | some (ps, body), _ =>
            revStep reg n' body (ps.zip acc.reverse) heap nl
        | none, Bool.true => .ok JSValue.undefined heap nl
        | none, _ => .stuck heap nl
    | reg, n' + 1, e :: es, env, heap, nl, f, acc =>
        match revExpr reg n' e env heap nl with
        | .ok v heap' nl' => revArgs reg n' es env heap' nl' f (v :: acc)
        | r => r
  termination_by _ n es _ _ _ _ => (Prod.mk n (sizeOf es) : Nat × Nat)

  def revCall : RefReg → Nat → Fn → List JSValue →
      Env → Heap → Nat → RRaw
    | _, 0, _, _, _, _, _ => .timeout
    | reg, n' + 1, f, args, _, heap, nl =>
        match reg f, fnStub f with
        | some (ps, body), _ =>
            revStep reg n' body (ps.zip args) heap nl
        | none, Bool.true => .ok JSValue.undefined heap nl
        | none, _ => .stuck heap nl
  termination_by _ n _ _ _ _ _ => (Prod.mk n 0 : Nat × Nat)

  def revList : RefReg → Nat → List Expr → Env → Heap → Nat →
      List JSValue → RRaw
    | _, _, [], _, heap, nl, acc => .ok (.listV acc.reverse) heap nl
    | reg, n, e :: es, env, heap, nl, acc =>
        match revExpr reg n e env heap nl with
        | .ok v heap' nl' => revList reg n es env heap' nl' (v :: acc)
        | r => r
  termination_by _ n es _ _ _ _ => (Prod.mk n (sizeOf es) : Nat × Nat)
  decreasing_by
    all_goals first
      | (simp_wf; omega)
      | (exfalso; simp_all)
      | omega
end

/-- Top level: run off the end is a fell (the frame had no kRet). -/
def refRun (reg : RefReg) (n : Nat) (p : Prog) (env : Env)
    (heap : Heap) (nl : Nat) : RResult :=
  match revStep reg n p env heap nl with
  | .ok v h l => .done v h l
  | .abrupt v h l => .threw v h l
  | .stuck h l => .fell h l
  | .fall _ h l => .fell h l
  | .timeout => .timeout
