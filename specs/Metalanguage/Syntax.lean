import Lean
import Metalanguage.Grammar
/- # Surface syntax: the emu-alg grammar and the macros elaborating
   it into the label-carrying AST. Registers spec words as tokens —
   import this AFTER grammar-dependent modules, or escape with «». -/

declare_syntax_cat stmt
declare_syntax_cat fstep
declare_syntax_cat algExpr
/- Spec variables whose names collide with keyword atoms ("method"
   from "internal method") live here — the explicit extension list is
   part of the audit. -/
declare_syntax_cat var
syntax ident : var
syntax "method" : var
declare_syntax_cat kwIf
declare_syntax_cat kwElse
declare_syntax_cat kwLet
declare_syntax_cat kwReturn
declare_syntax_cat kwThrow
declare_syntax_cat kwThen
declare_syntax_cat kwSet
declare_syntax_cat kwAssert
declare_syntax_cat kwFor

syntax var : algExpr
syntax "%" ident "%" : algExpr
syntax "true" : algExpr
syntax "false" : algExpr
syntax "undefined" : algExpr
syntax num : algExpr
syntax scientific : algExpr
syntax str : algExpr
syntax "~" ident "~" : algExpr
syntax "~" "string" "~" : algExpr
syntax "~" "number" "~" : algExpr
/- `x is …` — every choice level is first-token-disjoint (alternatives
   sharing more than a first token don't backtrack). -/
declare_syntax_cat notPred
syntax "an" "Object" : notPred
syntax "undefined" : notPred
syntax "present" : notPred
declare_syntax_cat isTail
syntax "an" "Object" : isTail
syntax "not" notPred : isTail
syntax "undefined" : isTail
syntax "true" : isTail
syntax "false" : isTail
syntax "~" ident "~" : isTail
syntax "a" "Boolean" : isTail
syntax "a" "Number" : isTail
syntax "a" "String" : isTail
syntax "a" "Symbol" : isTail
syntax "a" "BigInt" : isTail
syntax "~" "string" "~" : isTail
syntax "~" "number" "~" : isTail
syntax "either" "undefined" "or" "null" : isTail
syntax "null" : isTail
syntax "string" : isTail
syntax "number" : isTail
syntax algExpr "has" "a" "[[Call]]" "internal" "method" : algExpr
syntax algExpr "has" "a" "[[Construct]]" "internal" "method" : algExpr
/- n-ary calls: zero or more comma-separated arguments. Heads accept
   identifiers PLUS keyword-colliding names (the primitive-declared
   operation names) — same explicit-list discipline as `var`. -/
declare_syntax_cat callArgs
syntax algExpr : callArgs
syntax callArgs "," algExpr : callArgs
declare_syntax_cat aoName
/- "has a [[Value]] field" — descriptor field presence. -/
declare_syntax_cat hasTail
syntax "a" "[" "[" aoName "]" "]" "field" : hasTail
syntax ident : aoName
syntax "OrdinaryToPrimitive" : aoName
syntax "GetMethod" : aoName
syntax "GetV" : aoName
syntax "Get" : aoName
syntax "Call" : aoName
syntax aoName "(" ")" : algExpr
syntax aoName "(" callArgs ")" : algExpr
/- Internal-method calls: obj.[[Get]](P, receiver) — MOP dispatch. -/
/- ".[[" and "]]" as single tokens avoid the shared-prefix commit on "."
   (which would break every statement's trailing period). -/
/- Field read declared last; paren forms first so `]] (` commits there. -/
/- 1+-arg calls parse and pattern-match; ZERO-arg internal-method calls
   cannot be pattern-matched (empty parens are grouping in patterns), so
   the sole zero-arg case, [[GetPrototypeOf]], is written in field-read
   form — documented deviation at each transcription site. -/
syntax algExpr ".[[" aoName "]" "]" "(" callArgs ")" : algExpr
/- Record field read: desc.[[Value]]. -/
syntax algExpr ".[[" aoName "]" "]" : algExpr

/- `x is not …` — the tail is its own category so alternatives differ
   at the first token (shared prefixes past one token don't backtrack). -/
syntax algExpr "has" hasTail : algExpr
syntax algExpr "is" isTail : algExpr
syntax "number" : algExpr
syntax "string" : algExpr


/- Deviation: the spec's « argList » — Lean lexes « » as identifier
   delimiters, so the list brackets are dropped (single arg for now). -/

syntax "If" : kwIf
syntax "if" : kwIf
syntax "Else" : kwElse
syntax "else" : kwElse
syntax "Let" : kwLet
syntax "let" : kwLet
syntax "Return" : kwReturn
syntax "return" : kwReturn
syntax "Throw" : kwThrow
syntax "throw" : kwThrow
syntax "then" : kwThen
syntax "Set" : kwSet
syntax "set" : kwSet
syntax "Assert" : kwAssert
syntax "assert" : kwAssert
syntax "For" : kwFor
syntax "for" : kwFor

/- Statements: ifs and elses carry NO body — the body is the run of
   deeper-marked steps that follows, recovered by `renest`. -/
/- Terminal statements carry the spec's trailing period — except when
   the expression ends in a numeral, whose dot the lexer glues into the
   scientific token; those period-free variants come first. -/
syntax kwLet var "be" scientific : stmt
syntax kwReturn scientific : stmt
syntax kwSet var "to" scientific : stmt
syntax kwLet var "be" "?" algExpr "." : stmt
syntax kwLet var "be" algExpr "." : stmt
syntax kwReturn algExpr "." : stmt
syntax kwReturn "?" algExpr "." : stmt
syntax kwThrow "." : stmt
syntax kwThrow "a" "TypeError" "exception" "." : stmt
syntax kwAssert ":" algExpr "." : stmt
/- "Return a new Boolean object whose [[BooleanData]] internal slot is
   set to arg." — the wrapper-creation form (ToObject). -/
declare_syntax_cat typeName
syntax ident : typeName
syntax "Boolean" : typeName
syntax "Number" : typeName
syntax "String" : typeName
syntax "Symbol" : typeName
syntax "BigInt" : typeName
syntax kwReturn "a" "new" typeName "object" "whose" "[" "[" aoName "]" "]"
    "internal" "slot" "is" "set" "to" var "." : stmt
/- Loop: "For each element x of list, do" + sub-steps. The list is a
   spec List value; the body is the run of deeper steps. -/
syntax kwFor "each" "element" var "of" algExpr "," "do" : stmt
syntax kwSet var "to" algExpr "." : stmt
/- Block forms (sub-steps follow, deeper). The spec writes "If c, then";
   after the comma, block (then) and inline (statement) diverge, so the
   tail is its own first-token-disjoint category. -/
declare_syntax_cat ifTail
syntax kwThen : ifTail
syntax stmt : ifTail
syntax kwIf algExpr "," ifTail : stmt
/- Else-tails, first-token-disjoint: "Else, stmt." / "Else," (block) /
   "Else if c, then" (chain guard; the deeper block is wrapped by the
   guard and fused into the preceding if's else-end). -/
declare_syntax_cat elseTail
syntax "," ifTail : elseTail
syntax "," : elseTail
syntax kwIf algExpr "," kwThen : elseTail
syntax kwElse elseTail : stmt

/- Depth markers: a run of ┊ tokens, freely spaced (many1 recovers
   cleanly at any non-┊ token, so runs end without commit errors). -/
declare_syntax_cat label
syntax ident : label
/- `a` is a keyword (from "has a [[Call]]") and a sub-step label. -/
syntax "a" : label

/- A flat step: markers, a label, a statement. -/
/- Numeric labels: Lean's numeral lexer consumes an adjacent dot into a
   single scientific token ("1."), so numeric labels parse as scientific
   (dot included) and the elaborator strips it. -/
syntax ("┊")+ scientific stmt : fstep
syntax scientific stmt : fstep
syntax ("┊")+ label "." stmt : fstep
syntax label "." stmt : fstep

declare_syntax_cat fsteps
syntax fstep : fsteps
syntax fsteps fstep : fsteps

syntax "[alg|" fsteps "]" : term
syntax "[f|" fstep "]" : term
syntax "[e|" algExpr "]" : term
syntax "[ca|" callArgs "]" : term
syntax "[s|" stmt "]" : term

/- The numeral lexer glues a trailing dot into one scientific token
   ("1."), so numeric labels and integer literals both arrive as
   scientific tokens; strip the dot to recover the Nat. -/
open Lean in
def sciNat (n : TSyntax `scientific) : Nat :=
  let strip : «String» → Nat := fun v => («String».ofList (v.toList.dropLast)).toNat?.getD 0
  match n.raw with
  | .atom _ v => strip v
  | .node _ _ args =>
    match (args[0]? : Option Lean.Syntax) with
    | some (Lean.Syntax.atom _ v) => strip v
    | _ => 0
  | _ => 0

/- « "a", "b" » literals: the macro encodes the elements as one
   unit-separated string; this decodes at runtime. -/
open Lean in
def aoNameOf (x : TSyntax `aoName) : «String» :=
  let inner (w : Lean.Syntax) : «String» :=
    match w with
    | .ident _ t _ _ => t.toString
    | .atom _ v => v
    | _ => "?"
  match x.raw with
  | .ident _ s _ _ => s.toString
  | .atom _ v => v
  | .node _ _ args =>
    match (args[0]? : Option Lean.Syntax) with
    | some w => inner w
    | none => "?"
  | _ => "?"

open Lean in
def varName (x : TSyntax `var) : «String» :=
  let inner : Lean.Syntax → «String» :=
    fun s => match s with
      | .ident _ t _ _ => t.toString
      | .atom _ "method" => "method"
      | _ => "?"
  match x.raw with
  | .ident _ s _ _ => s.toString
  | .atom _ "method" => "method"
  | .node _ _ args =>
    match (args[0]? : Option Lean.Syntax) with
    | some w => inner w
    | none => "?"
  | _ => "?"

def listOfStrings (s : «String») : JSValue :=
  .listV ((s.splitOn "\x1f").map JSValue.str)

def listOfNvs (s : «String») : List Expr :=
  ((s.splitOn "\x1f").map Expr.nv)

open Lean in
macro_rules
  | `([e| $f:aoName ( )]) =>
      ``(Expr.call $(quote (aoNameOf f)) [])
  | `([e| $f:aoName ( $as:callArgs )]) =>
      ``(Expr.call $(quote (aoNameOf f)) [ca| $as])
  | `([e| $x:var]) =>
      /- A « … » token lexes as ONE bracketed identifier. Quoted
         elements (« "a", "b" ») become a spec-List literal; a single
         unquoted element (« hint ») is the argument-list notation for
         a variable. -/
      let strDL (s : «String») : «String» := «String».ofList (s.toList.dropLast)
      let strDF (s : «String») : «String» := «String».ofList (s.toList.drop 1)
      let strTW (s : «String») : «String» :=
        «String».ofList ((s.toList.dropWhile Char.isWhitespace).reverse
          |>.dropWhile Char.isWhitespace |>.reverse)
      let idTxt (w : Lean.Syntax) : «String» :=
        match w with
        | .ident _ t _ _ => t.toString
        | _ => "?"
      let txt := match x.raw with
        | .ident _ ss _ _ => ss.toString
        | .node _ _ args =>
          match (args[0]? : Option Lean.Syntax) with
          | some w => idTxt w
          | none => "?"
        | _ => "?"
      if txt.startsWith "«" && txt.contains "\"" && !txt.contains "~"
      then
        let inner := strDF (strDL txt)
        let elems := (inner.splitOn ",").map (fun q => strDL (strDF (strTW q)))
        ``(Expr.const (listOfStrings $(quote («String».intercalate "\x1f" elems))))
      else if txt.startsWith "«" && txt.endsWith "»"
      then
        /- `« a, b »` without quotes: a List of VARIABLES.
           (Singleton `« hint »` is the spec's arguments-List form.) -/
        let inner0 := strDF (strDL txt)
        let inner := «String».ofList ((inner0.toList.drop 1).dropLast)
        let elems := (String.splitOn inner ",").map strTW
        ``(Expr.listE (listOfNvs $(quote («String».intercalate "\x1f" elems))))
      else ``(Expr.nv $(quote (varName x)))
  | `([e| undefined]) => ``(Expr.const JSValue.undefined)
  | `([e| true]) => ``(Expr.const (JSValue.boolean Bool.true))
  | `([e| false]) => ``(Expr.const (JSValue.boolean Bool.false))
  | `([e| $n:num]) => ``(Expr.nat ($n : Nat))
  | `([e| $n:scientific]) => ``(Expr.nat $(quote (sciNat n)))
  | `([e| $s:str]) => ``(Expr.const (JSValue.str $s))
  | `([e| $r:algExpr .[[ $m:aoName ] ] ( $as:callArgs )]) =>
      ``(Expr.imeth $(quote (aoNameOf m)) [e| $r] [ca| $as])
  | `([e| $r:algExpr .[[ $m:aoName ] ]]) =>
      ``(Expr.ifield $(quote (aoNameOf m)) [e| $r])
  | `([e| ~ string ~]) => ``(Expr.const (JSValue.str "string"))
  | `([e| ~ number ~]) => ``(Expr.const (JSValue.str "number"))
  | `([e| ~ $v:ident ~]) => ``(Expr.const (JSValue.str $(quote (toString v.getId))))
  | `([e| $x:var is null]) => ``(Expr.isNull (Expr.nv $(quote (varName x))))
  | `([e| $e:algExpr is either undefined or null]) =>
      ``(Expr.isNullOrUnd [e| $e])
  | `([e| $e:algExpr is string]) =>
      ``(Expr.isStrVal "string" [e| $e])
  | `([e| $e:algExpr is number]) =>
      ``(Expr.isStrVal "number" [e| $e])
  | `([e| $e:algExpr is ~ string ~]) =>
      ``(Expr.isStrVal "string" [e| $e])
  | `([e| $e:algExpr is ~ number ~]) =>
      ``(Expr.isStrVal "number" [e| $e])
  | `([e| $e:algExpr is ~ $v:ident ~]) =>
      ``(Expr.isStrVal $(quote (toString v.getId)) [e| $e])
  | `([e| $e:algExpr has a [ [$m:aoName ] ] field]) =>
      ``(Expr.hasField $(quote (aoNameOf m)) [e| $e])
  | `([e| $e:algExpr is an Object]) => ``(Expr.isObject [e| $e])
  | `([e| $e:algExpr is a Boolean]) => ``(Expr.isType "Boolean" [e| $e])
  | `([e| $e:algExpr is a Number]) => ``(Expr.isType "Number" [e| $e])
  | `([e| $e:algExpr is a String]) => ``(Expr.isType "String" [e| $e])
  | `([e| $e:algExpr is a Symbol]) => ``(Expr.isType "Symbol" [e| $e])
  | `([e| $e:algExpr is a BigInt]) => ``(Expr.isType "BigInt" [e| $e])
  | `([e| $e:algExpr is not an Object]) => ``(Expr.isNotObject [e| $e])
  | `([e| $e:algExpr is not undefined]) => ``(Expr.isNotUndefined [e| $e])
  | `([e| $e:algExpr has a [[Call]] internal method]) => ``(Expr.hasCall [e| $e])
  | `([e| $e:algExpr has a [[Construct]] internal method]) => ``(Expr.hasCtor [e| $e])
  | `([e| $e:algExpr is undefined]) => ``(Expr.isU [e| $e])
  | `([e| $e:algExpr is true]) => ``(Expr.isBoolVal Bool.true [e| $e])
  | `([e| $e:algExpr is false]) => ``(Expr.isBoolVal Bool.false [e| $e])
  | `([e| $e:algExpr is not present]) =>
      let name := match e.raw with
        | .ident _ s _ _ => s.toString
        | _ => "?"
      ``(Expr.varNotPresent $(quote name))
  | `([e| % $x:ident % ]) =>
      ``(Expr.const (JSValue.str $(quote ("%" ++ toString x.getId ++ "%"))))
  | `([e| number]) => ``(Expr.const (JSValue.str "number"))
  | `([e| string]) => ``(Expr.const (JSValue.str "string"))

open Lean in
macro_rules
  | `([ca| $x:algExpr]) => `([[e| $x] ])
  | `([ca| $xs:callArgs , $x:algExpr]) => `([ca| $xs] ++ [[e| $x] ])

open Lean in
macro_rules
  | `([s| $__l:kwLet $x:var be $n:scientific]) =>
      ``(FBody.letE $(quote (varName x)) (Expr.nat $(quote (sciNat n))))
  | `([s| $_r:kwReturn $n:scientific]) =>
      ``(FBody.ret (Expr.nat $(quote (sciNat n))))
  | `([s| $_s:kwSet $x:var to $n:scientific]) =>
      ``(FBody.setE $(quote (varName x)) (Expr.nat $(quote (sciNat n))))
  | `([s| $_l:kwLet $x:var be ? $e:algExpr .]) =>
      ``(FBody.letE $(quote (varName x)) [e| $e])
  | `([s| $_l:kwLet $x:var be $e:algExpr .]) =>
      ``(FBody.letE $(quote (varName x)) [e| $e])
  | `([s| $_r:kwReturn ? $e:algExpr .]) =>
      ``(FBody.retE [e| $e])
  | `([s| $_r:kwReturn a new $_t:typeName object whose [ [ $s:aoName ] ]
      internal slot is set to $x:var .]) =>
      ``(FBody.retNewSlot $(quote (aoNameOf s)) $(quote (varName x)))
  | `([s| $_t:kwThrow a TypeError exception .]) =>
      ``(FBody.throw)
  | `([s| $_s:kwSet $x:var to $e:algExpr .]) =>
      ``(FBody.setE $(quote (varName x)) [e| $e])
  | `([s| $_k:kwIf $c:algExpr , $s:stmt]) =>
      ``(FBody.ifI [e| $c] [s| $s])
  | `([s| $_e:kwElse , $s:stmt]) =>
      ``(FBody.elseI [s| $s])
  | `([s| $_r:kwReturn $x:var .]) =>
      ``(FBody.ret (Expr.nv $(quote (varName x))))
  | `([s| $_r:kwReturn undefined .]) =>
      ``(FBody.ret (Expr.const JSValue.undefined))
  | `([s| $_r:kwReturn true .]) =>
      ``(FBody.ret (Expr.const (JSValue.boolean Bool.true)))
  | `([s| $_r:kwReturn false .]) =>
      ``(FBody.ret (Expr.const (JSValue.boolean Bool.false)))
  | `([s| $_r:kwReturn $e:algExpr .]) =>
      ``(FBody.ret [e| $e])
  | `([s| $_t:kwThrow .]) =>
      ``(FBody.throw)
  | `([s| $_k:kwIf $c:algExpr , $_t:kwThen]) =>
      ``(FBody.ifS [e| $c])
  | `([s| $_e:kwElse ,]) =>
      ``(FBody.elseM)
  | `([s| $_e:kwElse if $c:algExpr , then]) =>
      ``(FBody.elseG [e| $c])
  | `([s| Assert : $e:algExpr .]) =>
      ``(FBody.assertE [e| $e])
  | `([s| $_f:kwFor each element $x:var of $e:algExpr , do]) =>
      ``(FBody.forEach $(quote (varName x)) [e| $e])

/- Layout recovery: the flat stream (depth, label, body) is re-nested
   by bar count — takeBody collects the run of strictly deeper steps
   following an if/else; renest recurses into it. -/
/- Inline bodies ("If c, stmt.") have no labelled sub-steps; they
   desugar to a singleton branch labelled "a" — the label the step
   would have carried as a sub-step, keeping the audit meaningful. -/
def inlineBody : FBody → LBody
  | .ret v => .ret v
  | .retE e => .retE e
  | .retNewSlot sn vv => .retNewSlot sn vv
  | .throw => .throw
  | .assertE e => .assertE e
  | .setE n e => .setE n e
  | .ifI c s => .ifS c [("a", inlineBody s)] []
  | .elseI s => .elseM [("a", inlineBody s)]
  -- block if/else cannot appear as an inline body (they need deeper
  -- steps); total for Lean, loud in review if it ever shows up
  | .ifS _ => .throw
  | .elseM => .throw
  | .elseG _ => .throw
  | .forEach _ _ => .throw
  | .letE n e => .letE n e

def takeBody : Nat → List FStep → List FStep × List FStep
  | _, [] => ([], [])
  | d, s :: rest =>
      if s.1 > d then
        let (b, r) := takeBody d rest
        (s :: b, r)
      else ([], s :: rest)

/- Structural on fuel: each step consumes one unit; if/else bodies
   and remainders never exceed the remaining fuel, so the 0-arm is
   unreachable when fuel = length of the input. -/
def renestGo : Nat → List FStep → List LStep
  | 0, _ => []
  | _ + 1, [] => []
  | f + 1, (d, l, .ifS c) :: rest =>
      (l, LBody.ifS c (renestGo f (takeBody d rest).1) []) ::
        renestGo f (takeBody d rest).2
  | f + 1, (d, l, .elseM) :: rest =>
      (l, LBody.elseM (renestGo f (takeBody d rest).1)) ::
        renestGo f (takeBody d rest).2
  | f + 1, (_d, l, .ret v) :: rest => (l, LBody.ret v) :: renestGo f rest
  | f + 1, (_d, l, .throw) :: rest => (l, LBody.throw) :: renestGo f rest
  | f + 1, (_d, l, .retE e) :: rest => (l, LBody.retE e) :: renestGo f rest
  | f + 1, (_d, l, .retNewSlot sn vv) :: rest =>
      (l, LBody.retNewSlot sn vv) :: renestGo f rest
  | f + 1, (_d, l, .setE n e) :: rest => (l, LBody.setE n e) :: renestGo f rest
  | f + 1, (_d, l, .ifI c s) :: rest =>
      (l, LBody.ifS c [("a", inlineBody s)] []) :: renestGo f rest
  | f + 1, (_d, l, .elseI s) :: rest =>
      (l, LBody.elseM [("a", inlineBody s)]) :: renestGo f rest
  | f + 1, (d, l, .elseG c) :: rest =>
      let (t, rest2) := takeBody d rest
      (l, LBody.elseM [("a", LBody.ifS c (renestGo f t) [])]) :: renestGo f rest2
  | f + 1, (_d, l, .assertE e) :: rest =>
      (l, LBody.assertE e) :: renestGo f rest
  | f + 1, (d, l, .forEach x e) :: rest =>
      let (t, rest2) := takeBody d rest
      (l, LBody.forEach x e (renestGo f t)) :: renestGo f rest2
  | f + 1, (_d, l, .letE n e) :: rest =>
      (l, LBody.letE n e) :: renestGo f rest
termination_by f _ => f

def renest (fs : List FStep) : List LStep := renestGo fs.length fs

def build (fs : List FStep) : Prog := strip (fuseL (renest fs))

open Lean in
macro_rules
  | `([f| $n:scientific $s:stmt]) =>
      let lbl := match n.raw with
        | .atom _ v => «String».ofList (v.toList.dropLast)
        | .node _ _ args =>
          match (args[0]? : Option Lean.Syntax) with
          | some (Lean.Syntax.atom _ v) => «String».ofList (v.toList.dropLast)
          | _ => "?"
        | _ => "?"
      `([(0, $(quote lbl), [s| $s])])
  | `([f| ┊ $n:scientific $s:stmt]) =>
      let lbl := match n.raw with
        | .atom _ v => «String».ofList (v.toList.dropLast)
        | .node _ _ args =>
          match (args[0]? : Option Lean.Syntax) with
          | some (Lean.Syntax.atom _ v) => «String».ofList (v.toList.dropLast)
          | _ => "?"
        | _ => "?"
      `([(1, $(quote lbl), [s| $s])])
  | `([f| ┊ ┊ $n:scientific $s:stmt]) =>
      let lbl := match n.raw with
        | .atom _ v => «String».ofList (v.toList.dropLast)
        | .node _ _ args =>
          match (args[0]? : Option Lean.Syntax) with
          | some (Lean.Syntax.atom _ v) => «String».ofList (v.toList.dropLast)
          | _ => "?"
        | _ => "?"
      `([(2, $(quote lbl), [s| $s])])
  | `([f| ┊ ┊ ┊ $n:scientific $s:stmt]) =>
      let lbl := match n.raw with
        | .atom _ v => «String».ofList (v.toList.dropLast)
        | .node _ _ args =>
          match (args[0]? : Option Lean.Syntax) with
          | some (Lean.Syntax.atom _ v) => «String».ofList (v.toList.dropLast)
          | _ => "?"
        | _ => "?"
      `([(3, $(quote lbl), [s| $s])])
  | `([f| ┊ ┊ ┊ ┊ $n:scientific $s:stmt]) =>
      let lbl := match n.raw with
        | .atom _ v => «String».ofList (v.toList.dropLast)
        | .node _ _ args =>
          match (args[0]? : Option Lean.Syntax) with
          | some (Lean.Syntax.atom _ v) => «String».ofList (v.toList.dropLast)
          | _ => "?"
        | _ => "?"
      `([(4, $(quote lbl), [s| $s])])
  | `([f| ┊ ┊ ┊ ┊ ┊ $n:scientific $s:stmt]) =>
      let lbl := match n.raw with
        | .atom _ v => «String».ofList (v.toList.dropLast)
        | .node _ _ args =>
          match (args[0]? : Option Lean.Syntax) with
          | some (Lean.Syntax.atom _ v) => «String».ofList (v.toList.dropLast)
          | _ => "?"
        | _ => "?"
      `([(5, $(quote lbl), [s| $s])])
  | `([f| ┊ ┊ ┊ ┊ ┊ ┊ $n:scientific $s:stmt]) =>
      let lbl := match n.raw with
        | .atom _ v => «String».ofList (v.toList.dropLast)
        | .node _ _ args =>
          match (args[0]? : Option Lean.Syntax) with
          | some (Lean.Syntax.atom _ v) => «String».ofList (v.toList.dropLast)
          | _ => "?"
        | _ => "?"
      `([(6, $(quote lbl), [s| $s])])
  | `([f| ┊ $x:ident . $s:stmt]) =>
      `([(1, $(quote (toString x.getId)), [s| $s])])
  | `([f| ┊ a . $s:stmt]) => `([(1, "a", [s| $s])])
  | `([f| ┊ ┊ $x:ident . $s:stmt]) =>
      `([(2, $(quote (toString x.getId)), [s| $s])])
  | `([f| ┊ ┊ ┊ $x:ident . $s:stmt]) =>
      `([(3, $(quote (toString x.getId)), [s| $s])])
  | `([f| ┊ ┊ ┊ ┊ $x:ident . $s:stmt]) =>
      `([(4, $(quote (toString x.getId)), [s| $s])])
  | `([f| ┊ ┊ ┊ ┊ ┊ $x:ident . $s:stmt]) =>
      `([(5, $(quote (toString x.getId)), [s| $s])])
  | `([f| ┊ ┊ ┊ ┊ ┊ ┊ $x:ident . $s:stmt]) =>
      `([(6, $(quote (toString x.getId)), [s| $s])])
  | `([f| $x:ident . $s:stmt]) =>
      `([(0, $(quote (toString x.getId)), [s| $s])])

open Lean in
macro_rules
  | `([alg| $s:fstep]) => `([f| $s])
  | `([alg| $fs:fsteps $s:fstep]) => `([alg| $fs] ++ [f| $s])


/- ===== A small interpreter over the clean Prog ===== -/

