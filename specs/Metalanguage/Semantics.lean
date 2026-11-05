import Metalanguage.Grammar
/- # Semantics: big-step interpreter, SOS reference semantics, FM
   frame machine (heap, completions-as-values). -/


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
  -- pWrapC/pThrowC never reach here: they park, not push (the
  -- dedicated kPrim1 arms intercept before applyPrim)
  | .pWrapC, _ => JSValue.undefined
  | .pThrowC, _ => JSValue.undefined
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
  | .pIsNull, v => .boolean (isNullV v)
  | .pPred f b, v =>
      -- native correlated predicates (the predDecide stratum)
      .boolean (b ==
        match f with
        | "IsDataDescriptor" =>
            match v with
            | .descV ⟨v', w', _, _, _, _⟩ => v'.isSome || w'.isSome
            | _ => Bool.false
        | "IsAccessorDescriptor" =>
            match v with
            | .descV ⟨_, _, g', s', _, _⟩ => g'.isSome || s'.isSome
            | _ => Bool.false
        | _ => Bool.false)
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
      -- record field read on a descriptor value (undefined if absent);
      -- the GetPrototypeOf deviation: the zero-arg MOP, written in
      -- field-read form, actually dispatches (the heap is in scope)
      if s == "GetPrototypeOf" then
        match v with
        | .obj l =>
            match h l with
            | some o => match o.proto with
              | some p => .obj p
              | none => JSValue.null
            | none => JSValue.undefined
        | _ => JSValue.undefined
      else
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
def evalListE (h : Heap) (env : Env) : List Expr → Option (List JSValue)
  | [] => some []
  | e :: rest =>
      match evalE2 h env e, evalListE h env rest with
      | some v, some vs => some (v :: vs)
      | _, _ => none
termination_by es => sizeOf es

def evalE2 (h : Heap) (env : Env) : Expr → Option JSValue
  | .nv n => lookup env n
  | .listE es =>
      match evalListE h env es with
      | some vs => some (.listV vs)
      | none => none
  | .nat n => some (.number (↑n : Int))
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
  | env, .setE n e :: rest =>
      match evalE2 emptyHeap env e with
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
          .srun (l.flatMap (fun v => .setE x (Expr.const v) :: body) ++ rest) env
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
  | .srun ((.setE n e) :: rest) env =>
      match evalE2 emptyHeap env e with
      | some v => .srun rest ((n, v) :: env)
      | none => .sfell
  | .srun ((.letE n e) :: rest) env =>
      match evalE2 emptyHeap env e with
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




/- Runtime pending completion. Completions are NEVER values on
   eval or in env: produced (calls, wraps, returns) they park in
   the frame's pending field; consumed by the self-test idiom
   (kTest peeks, kIte branches, kUnwrap/kRet resolve). The static
   world's `pending` abstracts this field directly. -/
inductive PendV where
  | normal (v : JSValue)
  | throw
  deriving Repr

structure Fr where
  stmts  : List Instr
  env    : Env
  eval   : List JSValue
  /- Which AO's body this frame is running ("«top»" = the top-level
     program). This is the frame's DESTINY: the static return type of
     the name, and — from below — the type of the completion a caller
     anticipates while this frame runs. -/
  ret    : «String»
  /- The frame's undelivered completion (never an eval atom). -/
  pend   : Option PendV
  deriving Repr

inductive FM where
  | frames (fs : List Fr) (heap : Heap) (nextLoc : Nat)
  | fdone (p : PendV) (fs : List Fr) (heap : Heap) (nextLoc : Nat) (n : Nat)
  | fell (fs : List Fr) (heap : Heap) (nextLoc : Nat) (n : Nat)
  deriving Repr
  -- fdone/fell RETAIN the final machine state and count further
  -- (absorbing) transitions: `step (done k n) = done k (1+n)`. This is
  -- what makes step-indexed composition lemmas expressible (issue #2)
  -- and gives fell a debugging payload (issue #3).

/- Statement compilation (expressions stay as data; only statements
   become instruction sequences). -/

def fmOf (p : Prog) : FM :=
  .frames [⟨compileSteps p, [], [], "«top»", none⟩] emptyHeap 0

def fstep (reg : AOReg) : FM → FM
  | .fdone p fs heap nl n => .fdone p fs heap nl (n + 1)
  | .fell fs heap nl n => .fell fs heap nl (n + 1)
  | .frames [] heap nl => .fell [] heap nl 0
  | .frames (f :: fs) heap nl =>
    let done : List Fr → FM := fun fs' => .frames fs' heap nl
    match f.stmts, f.env, f.eval with
    | [], _, _ => .fell (f :: fs) heap nl 0    -- fell through without kRet
    | .kEval (.const (.compl Bool.false pv)) :: rest, env, eval =>
        -- completion literals PARK (never an eval atom)
        match f.pend with
        | none => done (⟨rest, env, eval, f.ret, some (.normal pv)⟩ :: fs)
        | some _ => .fell (f :: fs) heap nl 0    -- double park: loud
    | .kEval (.const (.compl Bool.true _)) :: rest, env, eval =>
        match f.pend with
        | none => done (⟨rest, env, eval, f.ret, some PendV.throw⟩ :: fs)
        | some _ => .fell (f :: fs) heap nl 0    -- double park: loud
    | .kEval (.const v) :: rest, env, eval => done (⟨rest, env, v :: eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.nat n) :: rest, env, eval =>
        done (⟨rest, env, .number (↑n : Int) :: eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.nv x) :: rest, env, eval =>
        match lookup env x with
        | some v => done (⟨rest, env, v :: eval, f.ret, f.pend⟩ :: fs)
        | none => .fell (f :: fs) heap nl 0     -- unbound: stuck, loudly
    | .kEval (.varNotPresent x) :: rest, env, eval =>
        done (⟨rest, env, .boolean (lookup env x).isNone :: eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.isObject (.nv x)) :: rest, env, _ =>
        -- FUSED variable test: one step, no expansion - the static
        -- split keeps its Γ-correlation through the machine step
        done (⟨.kTestVar x .pIsObj :: rest, env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.isObject e) :: _rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 .pIsObj :: f.stmts.tail!, f.env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.isNotObject (.nv x)) :: rest, env, _ =>
        done (⟨.kTestVar x .pIsNotObj :: rest, env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.isNotObject e) :: _rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 .pIsNotObj :: f.stmts.tail!, f.env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.isNotUndefined (.nv x)) :: rest, env, _ =>
        done (⟨.kTestVar x .pIsNotU :: rest, env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.isNotUndefined e) :: _rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 .pIsNotU :: f.stmts.tail!, f.env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.isU (.nv x)) :: rest, env, _ =>
        done (⟨.kTestVar x .pIsU :: rest, env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.isU e) :: _rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 .pIsU :: f.stmts.tail!, f.env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.hasCall (.nv x)) :: rest, env, _ =>
        done (⟨.kTestVar x .pHasCall :: rest, env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.hasCall e) :: _rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 .pHasCall :: f.stmts.tail!, f.env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.hasCtor (.nv x)) :: rest, env, _ =>
        done (⟨.kTestVar x .pHasCtor :: rest, env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.hasCtor e) :: _rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 .pHasCtor :: f.stmts.tail!, f.env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.isBoolVal b (.call fname [.nv x])) :: rest, env, _ =>
        -- correlated AO predicate of a variable: the descriptor
        -- predicates fuse natively (the predDecide stratum); other
        -- callees expand through the general call dust
        if fname == "IsDataDescriptor" || fname == "IsAccessorDescriptor"
        then done (⟨.kTestVar x (.pPred fname b) :: rest, env, f.eval, f.ret, f.pend⟩ :: fs)
        else done (⟨.kEval (.call fname [.nv x]) :: .kPrim1 (if b then .pIsTrue else .pIsFalse)
                        :: rest, env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.isBoolVal b (.nv x)) :: rest, env, _ =>
        done (⟨.kTestVar x (if b then .pIsTrue else .pIsFalse) :: rest, env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.isBoolVal b e) :: _rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 (if b then .pIsTrue else .pIsFalse)
                    :: f.stmts.tail!, f.env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.isStrVal sv (.nv x)) :: rest, env, _ =>
        done (⟨.kTestVar x (.pIsStr sv) :: rest, env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.isStrVal sv e) :: _rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 (.pIsStr sv) :: f.stmts.tail!, f.env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.hasField nm (.nv x)) :: rest, env, _ =>
        done (⟨.kTestVar x (.pHasField nm) :: rest, env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.hasField nm e) :: rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 (.pHasField nm) :: rest, f.env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.isType ty e) :: rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 (.pIsType ty) :: rest, f.env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.isNull e) :: rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 .pIsNull :: rest, f.env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.imeth nm recv args) :: rest, _, _ =>
        -- MOP dispatch: receiver first, then args, then the dispatch op
        done (⟨.kEval recv :: args.map Instr.kEval
                    ++ [.kIMeth nm args.length, .kTest, .kIte [.kRet] [.kUnwrap]] ++ rest,
                    f.env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.ifield nm e) :: rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 (.pDescField nm) :: rest, f.env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.isNullOrUnd (.nv x)) :: rest, env, _ =>
        done (⟨.kTestVar x .pNullOrUnd :: rest, env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.isNullOrUnd e) :: _rest, _, _ =>
        done (⟨.kEval e :: .kPrim1 .pNullOrUnd :: f.stmts.tail!, f.env, f.eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.call fname args) :: rest, env, eval =>
        -- bare and ? calls behave identically: test, propagate, extract.
        -- Completion(...) is the distinct no-test form (callC, to come).
        done (⟨args.map Instr.kEval
                    ++ [.kCall fname args.length, .kTest, .kIte [.kRet] [.kUnwrap]]
                    ++ rest, env, eval, f.ret, f.pend⟩ :: fs)
    | .kEval (.listE es) :: rest, env, eval =>
        done (⟨es.map Instr.kEval ++ [.kMkList es.length] ++ rest, env, eval, f.ret, f.pend⟩ :: fs)
    | .kPrim1 .pWrapC :: rest, env, v :: eval =>
        -- wrap the payload into a parked normal completion
        match f.pend with
        | none => done (⟨rest, env, eval, f.ret, some (.normal v)⟩ :: fs)
        | some _ => .fell (f :: fs) heap nl 0    -- double park: loud
    | .kPrim1 .pThrowC :: rest, env, _v :: eval =>
        match f.pend with
        | none => done (⟨rest, env, eval, f.ret, some PendV.throw⟩ :: fs)
        | some _ => .fell (f :: fs) heap nl 0    -- double park: loud
    | .kPrim1 p :: rest, env, v :: eval =>
        done (⟨rest, env, applyPrim heap p v :: eval, f.ret, f.pend⟩ :: fs)
    | .kPrim1 _ :: _, _, [] => .fell (f :: fs) heap nl 0  -- stack underflow: loud
    | .kCall fname n :: rest, env, eval =>
        if eval.length < n then .fell (f :: fs) heap nl 0
        else
          let popped := eval.take n
          let older := eval.drop n
          match findAO reg fname with
          | some (ps, body) =>
              done (⟨compileSteps body, ps.zip popped.reverse, [], fname, none⟩
                       :: ⟨rest, env, older, f.ret, f.pend⟩ :: fs)
          | none =>
              -- registry miss: prim-named calls (GetV/Get/Call/…)
              -- evaluate natively (stub: undefined), all others loud
              if nativeOps.contains fname
              then
                match f.pend with
                | none =>
                    done (⟨rest, env, older, f.ret, some (.normal JSValue.undefined)⟩ :: fs)
                | some _ => .fell (f :: fs) heap nl 0
              else .fell (f :: fs) heap nl 0
    | .kSet x :: rest, env, v :: eval => done (⟨rest, (x, v) :: env, eval, f.ret, f.pend⟩ :: fs)
    | .kSet _ :: _, _, [] => .fell (f :: fs) heap nl 0
    | .kTestVar x p :: rest, env, eval =>
        match lookup env x with
        | some v => done (⟨rest, env, applyPrim heap p v :: eval, f.ret, f.pend⟩ :: fs)
        | none => .fell (f :: fs) heap nl 0      -- unbound: stuck, loudly
    | .kPop :: rest, env, _ :: eval => done (⟨rest, env, eval, f.ret, f.pend⟩ :: fs)
    | .kPop :: _, _, [] => .fell (f :: fs) heap nl 0
    | .kIte t e :: rest, env, .boolean b :: eval =>
        done (⟨(if b then t else e) ++ rest, env, eval, f.ret, f.pend⟩ :: fs)
    | .kIte _ _ :: _, _, _ => .fell (f :: fs) heap nl 0  -- non-bool condition: loud
    | .kAssert :: rest, env, .boolean Bool.true :: eval => done (⟨rest, env, eval, f.ret, f.pend⟩ :: fs)
    | .kAssert :: _, _, _ => .fell (f :: fs) heap nl 0   -- failed assert: loud
    | .kRet :: _, _, _ =>
        -- return the PENDING; a caller receives it into ITS pending
        -- (the caller sits at the self-test idiom by frameOk's
        -- above-discipline)
        match f.pend with
        | some p =>
            match fs with
            | caller :: fs' =>
                done (⟨caller.stmts, caller.env, caller.eval, caller.ret, some p⟩ :: fs')
            | [] => .fdone p [] heap nl 0
        | none => .fell (f :: fs) heap nl 0     -- nothing to return: loud
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
                  done (⟨compileSteps body, ps.zip [recvv, p, rcv], [], "OrdinaryGet", none⟩
                          :: ⟨rest, env, older, f.ret, f.pend⟩ :: fs)
              | none => .fell (f :: fs) heap nl 0
          | "GetOwnProperty", [p], .obj loc =>
              match heap loc with
              | some o =>
                  let k := match p with | .str s => PKey.str s | _ => PKey.str "?"
                  let d := (o.props.find? (fun (pk, _) => pk == k)).map (·.2)
                  match f.pend with
                  | none =>
                      done (⟨rest, env, older, f.ret,
                              some (.normal (d.map JSValue.descV |>.getD JSValue.undefined))⟩ :: fs)
                  | some _ => .fell (f :: fs) heap nl 0
              | none => .fell (f :: fs) heap nl 0
          | "GetPrototypeOf", [], .obj loc =>
              match heap loc with
              | some o =>
                  let pv := match o.proto with | some l => .obj l | none => JSValue.null
                  match f.pend with
                  | none => done (⟨rest, env, older, f.ret, some (.normal pv)⟩ :: fs)
                  | some _ => .fell (f :: fs) heap nl 0
              | none => .fell (f :: fs) heap nl 0
          | _, _, _ => .fell (f :: fs) heap nl 0              -- unknown method / non-object receiver: loud
    | .kNewSlot _ :: _, _, [] => .fell (f :: fs) heap nl 0
    | .kNewSlot sn :: rest, env, v :: eval =>
        match slotOfName sn with
        | some ord =>
            let obj := { (objWith .ordinary none) with
                          slots := [(ord, v)] }
            done (⟨rest, env, .obj nl :: eval, f.ret, f.pend⟩ :: fs)
            |> fun m => match m with
              | .frames fs' heap _nl' =>
                  .frames fs' (heapSet heap nl obj) (nl + 1)
              | m => m
        | none => .fell (f :: fs) heap nl 0
    | .kMkList n :: rest, env, eval =>
        if eval.length < n then .fell (f :: fs) heap nl 0
        else done (⟨rest, env, .listV (eval.take n).reverse :: eval.drop n, f.ret, f.pend⟩ :: fs)
    | .kTest :: rest, env, eval =>
        -- peek the PENDING (never an eval atom): the completion
        -- stays parked; the verdict is the only thing pushed
        match f.pend with
        | some (.normal _) =>
            done (⟨rest, env, .boolean Bool.false :: eval, f.ret, f.pend⟩ :: fs)
        | some PendV.throw =>
            done (⟨rest, env, .boolean Bool.true :: eval, f.ret, f.pend⟩ :: fs)
        | none => .fell (f :: fs) heap nl 0      -- nothing parked: loud
    | .kUnwrap :: rest, env, eval =>
        match f.pend with
        | some (.normal v) => done (⟨rest, env, v :: eval, f.ret, none⟩ :: fs)
        | _ => .fell (f :: fs) heap nl 0        -- nothing (or a throw) parked: loud
    | .kRepeatWhile c body :: rest, env, eval =>
        done (⟨.kEval c :: .kRepeatTest c body :: rest, env, eval, f.ret, f.pend⟩ :: fs)
    | .kRepeatTest c body :: rest, env, .boolean b :: eval =>
        -- loop continuation must PRESERVE rest (issue #1): the
        -- re-armed kRepeatWhile re-enters with the same tail.
        done (⟨(if b then body ++ [.kRepeatWhile c body] ++ rest else rest), env, eval, f.ret, f.pend⟩ :: fs)
    | .kRepeatTest _ _ :: _, _, _ => .fell (f :: fs) heap nl 0
    | .kForStart _x _body :: rest, env, .listV [] :: eval =>
        done (⟨rest, env, eval, f.ret, f.pend⟩ :: fs)
    | .kForStart x body :: rest, env, .listV (v :: vs) :: eval =>
        done (⟨.kEval (.const v) :: .kSet x :: body
                    ++ [.kForBody x vs body] ++ rest, env, eval, f.ret, f.pend⟩ :: fs)
    | .kForStart _ _ :: _, _, _ => .fell (f :: fs) heap nl 0           -- For each over non-List: loud
    | .kForBody x (v :: vs) body :: rest, env, eval =>
        done (⟨.kEval (.const v) :: .kSet x :: body
                    ++ [.kForBody x vs body] ++ rest, env, eval, f.ret, f.pend⟩ :: fs)
    | .kForBody _ [] _ :: rest, env, eval => done (⟨rest, env, eval, f.ret, f.pend⟩ :: fs)

def fsteps (reg : AOReg) : Nat → FM → FM
  | 0, m => m
  | n + 1, m => fsteps reg n (fstep reg m)

def sameOutcome2 : SState → FM → Bool
  | .sret v, .fdone (.normal v') _ _ _ _ => v == v'
  | .sthrown, .fdone PendV.throw _ _ _ _ => Bool.true
  | .sfell, .fell _ _ _ _ => Bool.true
  | _, _ => Bool.false

def agree2 (reg : AOReg) (p : Prog) : Bool :=
  sameOutcome2 (sosSteps 200 (.srun p [])) (fsteps reg 500 (fmOf p))

def ftrace2 (reg : AOReg) : Nat → FM → List FM
  | 0, _ => []
  | n + 1, m => m :: ftrace2 reg n (fstep reg m)

