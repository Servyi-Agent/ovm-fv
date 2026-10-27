import Metalanguage.Grammar
/- # Semantics: big-step interpreter, SOS reference semantics, FM
   frame machine (heap, completions-as-values). -/

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

/- Property keys: String or Symbol (symbolic here). -/
inductive PKey where
  | str (s : «String»)
  | sym (id : Nat)
  deriving Repr, BEq

/- Object kinds — the interpreter dispatches on this tag. -/
inductive Kind where
  | ordinary
  | builtin (params : List String) (body : Prog)
  | string (s : «String»)                   -- String exotic
  deriving Repr

structure JsObj where
  kind       : Kind
  proto      : Option Nat                 -- [[Prototype]] (none = null)
  extensible : Bool                       -- [[Extensible]]
  slots      : List (Nat × JSValue)       -- sparse internal slots (slotOrd-keyed)
  props      : List (PKey × Descriptor)   -- ordered own properties
  deriving Repr


def objWith (kind : Kind) (proto : Option Nat) : JsObj where
  kind := kind
  proto := proto
  extensible := Bool.true
  slots := []
  props := []

/- Heap: object locations → objects, as a function (user's choice). -/
abbrev Heap := Nat → Option JsObj

def emptyHeap : Heap := fun _ => none

instance : Repr Heap := ⟨fun _ _ => "<heap>"⟩

def heapSet (h : Heap) (loc : Nat) (o : JsObj) : Heap :=
  fun l => if l == loc then some o else h l

instance : Inhabited JSValue := ⟨.undefined⟩





abbrev Env := List («String» × JSValue)

def lookup : Env → «String» → Option JSValue
  | [], _ => none
  | (k, v) :: r, k' => if k == k' then some v else lookup r k'

def truthy : JSValue → Bool
  | .undefined => Bool.false
  | .null => Bool.false
  | .boolean b => b
  | .number n => n != 0
  | .str s => !s.isEmpty
  | .listV _ => Bool.true
  | .compl _ _ => Bool.true
  | .obj _ => Bool.true
  | .descV _ => Bool.true

/- Bedrock predicates on values (no objects in this universe yet). -/
def isUndV : JSValue → Bool
  | .undefined => Bool.true
  | _ => Bool.false

def isObjV : JSValue → Bool
  | .obj _ => Bool.true
  | _ => Bool.false

def hasCallV (h : Heap) : JSValue → Bool
  | .obj loc => match h loc with
    | some o => match o.kind with | .builtin _ _ => Bool.true | _ => Bool.false
    | none => Bool.false
  | _ => Bool.false

def hasCtorV (_h : Heap) : JSValue → Bool := fun _ => Bool.false
def isNullV : JSValue → Bool
  | .null => Bool.true
  | _ => Bool.false

/- Toy semantics: no objects in this value universe, primitives
   return undefined. Calls are machine-only: the big-step evaluator
   cannot enter the registry. -/

def applyPrim (h : Heap) : Prim → JSValue → JSValue
  | .pIsObj, v => .boolean (isObjV v)
  | .pIsNotObj, v => .boolean (!isObjV v)
  | .pIsNotU, v => .boolean (!isUndV v)
  | .pHasCall, v => .boolean (hasCallV h v)
  | .pHasCtor, v => .boolean (hasCtorV h v)
  | .pIsU, v => .boolean (isUndV v)
  | .pIsTrue, v => .boolean (v == .boolean Bool.true)
  | .pIsFalse, v => .boolean (v == .boolean Bool.false)
  | .pIsStr s, v => .boolean (v == .str s)
  | .pNullOrUnd, v => .boolean (isUndV v || isNullV v)
  | .pWrapC, v => .compl Bool.false v
  | .pThrowC, v => .compl Bool.true v
  | .pIsNull, v => .boolean (isNullV v)
  | .pIsType s, v =>
      .boolean (
        match s with
        | "Boolean" => match v with | .boolean _ => Bool.true | _ => Bool.false
        | "Number" => match v with | .number _ => Bool.true | _ => Bool.false
        | "String" => match v with | .str _ => Bool.true | _ => Bool.false
        | "Symbol" => Bool.false   -- no Symbol values in this universe yet
        | "BigInt" => Bool.false   -- no BigInt values yet
        | _ => Bool.false)
  | .pHasField s, v =>
      .boolean (
        match v with
        | .descV (.mk value writable getter setter enumerable configurable) =>
            if s == "Value" then value.isSome
            else if s == "Writable" then writable.isSome
            else if s == "Getter" then getter.isSome
            else if s == "Setter" then setter.isSome
            else if s == "Enumerable" then enumerable.isSome
            else if s == "Configurable" then configurable.isSome
            else Bool.false
        | _ => Bool.false)
  | .pDescField s, v =>
      -- record field read on a descriptor value (undefined if absent)
      match v with
      | .descV (.mk value writable getter setter enumerable configurable) =>
          let natToObj (o : Option Nat) : JSValue :=
            match o with | some l => .obj l | none => JSValue.undefined
          let boolToVal (o : Option Bool) : JSValue :=
            match o with | some b => .boolean b | none => JSValue.undefined
          if s == "Value" then value.getD JSValue.undefined
          else if s == "Getter" then natToObj getter
          else if s == "Setter" then natToObj setter
          else if s == "Writable" then boolToVal writable
          else if s == "Enumerable" then boolToVal enumerable
          else if s == "Configurable" then boolToVal configurable
          else JSValue.undefined
      | _ => JSValue.undefined


mutual
def evalListE (h : Heap) (env : Env) : List E2 → Option (List JSValue)
  | [] => some []
  | e :: rest =>
      match evalE2 h env e, evalListE h env rest with
      | some v, some vs => some (v :: vs)
      | _, _ => none
termination_by es => sizeOf es

def evalE2 (h : Heap) (env : Env) : E2 → Option JSValue
  | .nv n => lookup env n
  | .listE es =>
      match evalListE h env es with
      | some vs => some (.listV vs)
      | none => none
  | .nat n => some (.number n.toFloat)
  | .const v => some v
  | .isObject e =>
      match evalE2 h env e with
      | some v => some (.boolean (isObjV v))
      | none => none
  | .isNotObject e =>
      match evalE2 h env e with
      | some v => some (.boolean (!isObjV v))
      | none => none
  | .hasCall e =>
      match evalE2 h env e with
      | some v => some (.boolean (hasCallV h v))
      | none => none
  | .hasCtor e =>
      match evalE2 h env e with
      | some v => some (.boolean (hasCtorV h v))
      | none => none
  | .isU e =>
      match evalE2 h env e with
      | some v => some (.boolean (isUndV v))
      | none => none
  | .isBoolVal b e =>
      match evalE2 h env e with
      | some v => some (.boolean (v == .boolean b))
      | none => none
  | .isNullOrUnd e =>
      match evalE2 h env e with
      | some v => some (.boolean (isUndV v || isNullV v))
      | none => none
  | .isNull e =>
      match evalE2 h env e with
      | some v => some (.boolean (isNullV v))
      | none => none
  | .hasField nm e =>
      match evalE2 h env e with
      | some v => some (applyPrim h (.pHasField nm) v)
      | none => none
  | .isType ty e =>
      match evalE2 h env e with
      | some v => some (applyPrim h (.pIsType ty) v)
      | none => none
  | .imeth _ _ _ => none     -- machine-level (MOP dispatch)
  | .ifield _ _ => none      -- machine-level (record field read)
  | .isStrVal s e =>
      match evalE2 h env e with
      | some v => some (.boolean (v == .str s))
      | none => none
  | .varNotPresent n => some (.boolean (lookup env n).isNone)
  | .call _ _ => none
  | .isNotUndefined e =>
      match evalE2 h env e with
      | some .undefined => some (.boolean Bool.false)
      | some _ => some (.boolean Bool.true)
      | none => none
termination_by e => sizeOf e
end

def evalP2 : P2 → Option JSValue
  | .call _ _ _ => some .undefined      -- stub until Call/heap
  | _ => some .undefined

inductive Outcome where
  | ret (v : JSValue)
  | thrown
  | fall
  deriving Repr

/- Spec semantics: sub-step variables persist for the rest of the
   algorithm; a branch that falls through continues with the next
   step, carrying its bindings. -/
def run : Env → List Step → Outcome × Env
  | env, [] => (.fall, env)
  | env, .ret v :: _ =>
      match evalE2 emptyHeap env v with
      | some v => (.ret v, env)
      | none => (.fall, env)
  | env, .throw :: _ => (.thrown, env)
  | env, .forEach _ _ _ :: _ => (.fall, env)   -- loops are machine-level (kstep)
  | env, .assertE e :: rest =>
      match evalE2 emptyHeap env e with
      | some (.boolean Bool.true) => run env rest
      | _ => (.fall, env)
  | env, .retNewSlot _ _ :: _ => (.fall, env)   -- heap-allocating: machine-level
  | env, .retE e :: _ =>
      match evalE2 emptyHeap env e with
      | some v => (.ret v, env)
      | none => (.fall, env)
  | env, .retQ op :: _ =>
      match evalP2 op with
      | some v => (.ret v, env)
      | none => (.fall, env)
  | env, .setE n e :: rest =>
      match evalE2 emptyHeap env e with
      | some v => run ((n, v) :: env) rest
      | none => (.fall, env)
  | env, .letQ n op :: rest =>
      match evalP2 op with
      | some v => run ((n, v) :: env) rest
      | none => (.fall, env)
  | env, .letE n e :: rest =>
      match evalE2 emptyHeap env e with
      | some v => run ((n, v) :: env) rest
      | none => (.fall, env)
  | env, .ifS c t e :: rest =>
      match evalE2 emptyHeap env c with
      | some v =>
          if truthy v then
            let (out, env') := run env t
            match out with
            | .fall => run env' rest
            | _ => (out, env')
          else
            let (out, env') := run env e
            match out with
            | .fall => run env' rest
            | _ => (out, env')
      | none => (.fall, env)
  | env, .elseM _ :: _ => (.fall, env)

/- ===== kEval machine: small-step with evaluation states woven into
   the statement sequence. The continuation is defunctionalized INTO
   the list: the tail is the SOS continuation, the k-markers are
   suspended consumers, kRestoreS is a frame. Calls enter registered
   transcribed algorithms (IsCallable, ...) with a fresh env. ===== -/



inductive SState where
  | srun (p : Prog) (env : Env)
  | sret (v : JSValue)
  | sthrown
  | sfell
  deriving Repr

def sosStep : SState → SState
  | .sret v => .sret v
  | .sthrown => .sthrown
  | .sfell => .sfell
  | .srun [] _ => .sfell
  | .srun ((.ret v) :: _) env =>
      match evalE2 emptyHeap env v with
      | some v => .sret v
      | none => .sfell
  | .srun (.throw :: _) _ => .sthrown
  | .srun ((.forEach x e body) :: rest) env =>
      match evalE2 emptyHeap env e with
      | some (.listV l) =>
          -- finite unroll: set the binder before each copy of the body
          .srun (l.flatMap (fun v => .setE x (E2.const v) :: body) ++ rest) env
      | _ => .sfell
  | .srun (.assertE e :: rest) env =>
      match evalE2 emptyHeap env e with
      | some (.boolean Bool.true) => .srun rest env
      | _ => .sfell
  | .srun (.retNewSlot _ _ :: _) _env => .sfell   -- heap-allocating: machine-level
  | .srun (.retE e :: _) env =>
      match evalE2 emptyHeap env e with
      | some v => .sret v
      | none => .sfell
  | .srun (.retQ op :: _) _env =>
      match evalP2 op with
      | some v => .sret v
      | none => .sfell
  | .srun ((.setE n e) :: rest) env =>
      match evalE2 emptyHeap env e with
      | some v => .srun rest ((n, v) :: env)
      | none => .sfell
  | .srun ((.letE n e) :: rest) env =>
      match evalE2 emptyHeap env e with
      | some v => .srun rest ((n, v) :: env)
      | none => .sfell
  | .srun ((.letQ n op) :: rest) env =>
      match evalP2 op with
      | some v => .srun rest ((n, v) :: env)
      | none => .sfell
  | .srun ((.ifS c t e) :: rest) env =>
      match evalE2 emptyHeap env c with
      | some (.boolean b) => .srun (if b then t ++ rest else e ++ rest) env
      | _ => .sfell        -- non-Boolean condition: stuck, not coerced
  | .srun ((.elseM _) :: rest) env => .srun rest env

def sosSteps : Nat → SState → SState
  | 0, s => s
  | n + 1, s => sosSteps n (sosStep s)

/- Outcome-level agreement: SOS and the machine step at different
   granularity, so compare terminals after enough steps for both. -/




structure Fr where
  stmts : List Rt2
  env   : Env
  eval  : List JSValue
  deriving Repr

inductive FM where
  | frames (fs : List Fr) (heap : Heap) (nextLoc : Nat)
  | fdone (v : JSValue) (fs : List Fr) (heap : Heap) (nextLoc : Nat) (n : Nat)
  | fell (fs : List Fr) (heap : Heap) (nextLoc : Nat) (n : Nat)
  deriving Repr
  -- fdone/fell RETAIN the final machine state and count further
  -- (absorbing) transitions: `step (done k n) = done k (1+n)`. This is
  -- what makes step-indexed composition lemmas expressible (issue #2)
  -- and gives fell a debugging payload (issue #3).

/- Statement compilation (expressions stay as data; only statements
   become instruction sequences). -/

def fmOf (p : Prog) : FM := .frames [⟨compileSteps p, [], []⟩] emptyHeap 0

def fstep (reg : AOReg) : FM → FM
  | .fdone v fs heap nl n => .fdone v fs heap nl (n + 1)
  | .fell fs heap nl n => .fell fs heap nl (n + 1)
  | .frames [] heap nl => .fell [] heap nl 0
  | .frames (f :: fs) heap nl =>
    let done : List Fr → FM := fun fs' => .frames fs' heap nl
    match f.stmts, f.env, f.eval with
    | [], _, _ => .fell (f :: fs) heap nl 0    -- fell through without kRet
    | .kEval (.const v) :: rest, env, eval => done (⟨rest, env, v :: eval⟩ :: fs)
    | .kEval (.nat n) :: rest, env, eval =>
        done (⟨rest, env, .number n.toFloat :: eval⟩ :: fs)
    | .kEval (.nv x) :: rest, env, eval =>
        match lookup env x with
        | some v => done (⟨rest, env, v :: eval⟩ :: fs)
        | none => .fell (f :: fs) heap nl 0     -- unbound: stuck, loudly
    | .kEval (.varNotPresent x) :: rest, env, eval =>
        done (⟨rest, env, .boolean (lookup env x).isNone :: eval⟩ :: fs)
    | .kEval (.isObject e) :: _rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 .pIsObj :: f.stmts.tail!, f.env, f.eval⟩ :: fs)
    | .kEval (.isNotObject e) :: _rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 .pIsNotObj :: f.stmts.tail!, f.env, f.eval⟩ :: fs)
    | .kEval (.isNotUndefined e) :: _rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 .pIsNotU :: f.stmts.tail!, f.env, f.eval⟩ :: fs)
    | .kEval (.isU e) :: _rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 .pIsU :: f.stmts.tail!, f.env, f.eval⟩ :: fs)
    | .kEval (.hasCall e) :: _rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 .pHasCall :: f.stmts.tail!, f.env, f.eval⟩ :: fs)
    | .kEval (.hasCtor e) :: _rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 .pHasCtor :: f.stmts.tail!, f.env, f.eval⟩ :: fs)
    | .kEval (.isBoolVal b e) :: _rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 (if b then .pIsTrue else .pIsFalse)
                    :: f.stmts.tail!, f.env, f.eval⟩ :: fs)
    | .kEval (.isStrVal s e) :: _rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 (.pIsStr s) :: f.stmts.tail!, f.env, f.eval⟩ :: fs)
    | .kEval (.hasField nm e) :: rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 (.pHasField nm) :: rest, f.env, f.eval⟩ :: fs)
    | .kEval (.isType ty e) :: rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 (.pIsType ty) :: rest, f.env, f.eval⟩ :: fs)
    | .kEval (.isNull e) :: rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 .pIsNull :: rest, f.env, f.eval⟩ :: fs)
    | .kEval (.imeth nm recv args) :: rest, _, _ =>
        -- MOP dispatch: receiver first, then args, then the dispatch op
        done (⟨.kEval recv :: args.map Rt2.kEval
                    ++ [.kIMeth nm args.length, .kTest, .kIte [.kRet] [.kUnwrap]] ++ rest,
                    f.env, f.eval⟩ :: fs)
    | .kEval (.ifield nm e) :: rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 (.pDescField nm) :: rest, f.env, f.eval⟩ :: fs)
    | .kEval (.isNullOrUnd e) :: _rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 .pNullOrUnd :: f.stmts.tail!, f.env, f.eval⟩ :: fs)
    | .kEval (.call fname args) :: rest, env, eval =>
        -- bare and ? calls behave identically: test, propagate, extract.
        -- Completion(...) is the distinct no-test form (callC, to come).
        done (⟨args.map Rt2.kEval
                    ++ [.kCall fname args.length, .kTest, .kIte [.kRet] [.kUnwrap]]
                    ++ rest, env, eval⟩ :: fs)
    | .kEval (.listE es) :: rest, env, eval =>
        done (⟨es.map Rt2.kEval ++ [.kMkList es.length] ++ rest, env, eval⟩ :: fs)
    | .kPrim1 p :: rest, env, v :: eval =>
        done (⟨rest, env, applyPrim heap p v :: eval⟩ :: fs)
    | .kPrim1 _ :: _, _, [] => .fell (f :: fs) heap nl 0  -- stack underflow: loud
    | .kPrimQ op :: rest, env, eval =>
        match evalP2 op with
        | some v => done (⟨rest, env, .compl Bool.false v :: eval⟩ :: fs)
        | none => .fell (f :: fs) heap nl 0
    | .kCall fname n :: rest, env, eval =>
        if eval.length < n then .fell (f :: fs) heap nl 0
        else
          let popped := eval.take n
          let older := eval.drop n
          match findAO reg fname with
          | some (ps, body) =>
              done (⟨compileSteps body, ps.zip popped.reverse, []⟩
                       :: ⟨rest, env, older⟩ :: fs)
          | none =>
              -- registry miss: prim-named calls (GetV/Get/Call/…)
              -- evaluate natively (stub: undefined), all others loud
              if ["GetV", "Get", "Call", "GetMethod", "OrdinaryToPrimitive"].contains fname
              then done (⟨rest, env, .compl Bool.false JSValue.undefined :: older⟩ :: fs)
              else .fell (f :: fs) heap nl 0
    | .kSet x :: rest, env, v :: eval => done (⟨rest, (x, v) :: env, eval⟩ :: fs)
    | .kSet _ :: _, _, [] => .fell (f :: fs) heap nl 0
    | .kPop :: rest, env, _ :: eval => done (⟨rest, env, eval⟩ :: fs)
    | .kPop :: _, _, [] => .fell (f :: fs) heap nl 0
    | .kIte t e :: rest, env, .boolean b :: eval =>
        done (⟨(if b then t else e) ++ rest, env, eval⟩ :: fs)
    | .kIte _ _ :: _, _, _ => .fell (f :: fs) heap nl 0  -- non-bool condition: loud
    | .kAssert :: rest, env, .boolean Bool.true :: eval => done (⟨rest, env, eval⟩ :: fs)
    | .kAssert :: _, _, _ => .fell (f :: fs) heap nl 0   -- failed assert: loud
    | .kRet :: _, _, v :: _ =>
        match fs with
        | caller :: fs' => done (⟨caller.stmts, caller.env, v :: caller.eval⟩ :: fs')
        | [] => .fdone v [] heap nl 0
    | .kRet :: _, _, [] =>
        /- return with nothing on the eval stack: allowed, no push -/
        match fs with
        | caller :: fs' => done (⟨caller.stmts, caller.env, caller.eval⟩ :: fs')
        | [] => .fell (f :: fs) heap nl 0
    | .kIMeth nm n :: rest, env, eval =>
        -- stack: [argn..arg1, recv, ...older] (receiver pushed FIRST,
        -- args on top; receiver at index n from the top)
        if eval.length < n + 1 then .fell (f :: fs) heap nl 0
        else
          let argsw := eval.take n
          let recvv := eval.getD n JSValue.undefined
          let older := eval.drop (n + 1)
          match nm, argsw.reverse, recvv with
          | "Get", [p, rcv], .obj _loc =>
              match findAO reg "OrdinaryGet" with
              | some (ps, body) =>
                  done (⟨compileSteps body, ps.zip [recvv, p, rcv], []⟩ :: ⟨rest, env, older⟩ :: fs)
              | none => .fell (f :: fs) heap nl 0
          | "GetOwnProperty", [p], .obj loc =>
              match heap loc with
              | some o =>
                  let k := match p with | .str s => PKey.str s | _ => PKey.str "?"
                  let d := (o.props.find? (fun (pk, _) => pk == k)).map (·.2)
                  done (⟨rest, env, .compl Bool.false (d.map JSValue.descV |>.getD JSValue.undefined) :: older⟩ :: fs)
              | none => .fell (f :: fs) heap nl 0
          | "GetPrototypeOf", [], .obj loc =>
              match heap loc with
              | some o =>
                  let pv := match o.proto with | some l => .obj l | none => JSValue.null
                  done (⟨rest, env, .compl Bool.false pv :: older⟩ :: fs)
              | none => .fell (f :: fs) heap nl 0
          | _, _, _ => .fell (f :: fs) heap nl 0              -- unknown method / non-object receiver: loud
    | .kNewSlot _ :: _, _, [] => .fell (f :: fs) heap nl 0
    | .kNewSlot sn :: rest, env, v :: eval =>
        match slotOfName sn with
        | some ord =>
            let obj := { (objWith .ordinary none) with
                          slots := [(ord, v)] }
            done (⟨rest, env, .obj nl :: eval⟩ :: fs)
            |> fun m => match m with
              | .frames fs' heap _nl' =>
                  .frames fs' (heapSet heap nl obj) (nl + 1)
              | m => m
        | none => .fell (f :: fs) heap nl 0
    | .kMkList n :: rest, env, eval =>
        if eval.length < n then .fell (f :: fs) heap nl 0
        else done (⟨rest, env, .listV (eval.take n).reverse :: eval.drop n⟩ :: fs)
    | .kTest :: rest, env, .compl abrupt v :: eval =>
        -- peek: the completion STAYS under the pushed boolean
        done (⟨rest, env, .boolean abrupt :: .compl abrupt v :: eval⟩ :: fs)
    | .kTest :: _, _, _ => .fell (f :: fs) heap nl 0          -- top not a completion: loud
    | .kUnwrap :: rest, env, .compl _ v :: eval =>
        done (⟨rest, env, v :: eval⟩ :: fs)
    | .kUnwrap :: _, _, _ => .fell (f :: fs) heap nl 0        -- top not a completion: loud
    | .kRepeatWhile c body :: rest, env, eval =>
        done (⟨.kEval c :: .kRepeatTest c body :: rest, env, eval⟩ :: fs)
    | .kRepeatTest c body :: rest, env, .boolean b :: eval =>
        -- loop continuation must PRESERVE rest (issue #1): the
        -- re-armed kRepeatWhile re-enters with the same tail.
        done (⟨(if b then body ++ [.kRepeatWhile c body] ++ rest else rest), env, eval⟩ :: fs)
    | .kRepeatTest _ _ :: _, _, _ => .fell (f :: fs) heap nl 0
    | .kForStart _x _body :: rest, env, .listV [] :: eval =>
        done (⟨rest, env, eval⟩ :: fs)
    | .kForStart x body :: rest, env, .listV (v :: vs) :: eval =>
        done (⟨.kEval (.const v) :: .kSet x :: body
                    ++ [.kForBody x vs body] ++ rest, env, eval⟩ :: fs)
    | .kForStart _ _ :: _, _, _ => .fell (f :: fs) heap nl 0           -- For each over non-List: loud
    | .kForBody x (v :: vs) body :: rest, env, eval =>
        done (⟨.kEval (.const v) :: .kSet x :: body
                    ++ [.kForBody x vs body] ++ rest, env, eval⟩ :: fs)
    | .kForBody _ [] _ :: rest, env, eval => done (⟨rest, env, eval⟩ :: fs)

def fsteps (reg : AOReg) : Nat → FM → FM
  | 0, m => m
  | n + 1, m => fsteps reg n (fstep reg m)

def sameOutcome2 : SState → FM → Bool
  | .sret v, .fdone (.compl Bool.false v') _ _ _ _ => v == v'
  | .sret v, .fdone v' _ _ _ _ => v == v'   -- bare value (never through a call)
  | .sthrown, .fdone (.compl Bool.true _) _ _ _ _ => Bool.true
  | .sfell, .fell _ _ _ _ => Bool.true
  | _, _ => Bool.false

def agree2 (reg : AOReg) (p : Prog) : Bool :=
  sameOutcome2 (sosSteps 200 (.srun p [])) (fsteps reg 500 (fmOf p))

def ftrace2 (reg : AOReg) : Nat → FM → List FM
  | 0, _ => []
  | n + 1, m => m :: ftrace2 reg n (fstep reg m)

