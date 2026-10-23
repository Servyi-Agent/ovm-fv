/- # ovm-fv metalanguage

   The ECMA-262 emu-alg metalanguage: surface grammar (`┊` depth
   markers, spec numbering), label-carrying elaboration, audits
   (numbering consecutiveness), SOS and kEval small-step semantics
   (frames for control boundaries), and the operation-registry
   protocol. Spec transcriptions live under spec/<clause>/spec.lean
   and are assembled into a registry by tools/build_corpus.py. -/

/- Numbered-step grammar with exact ECMA-262 tokens AND explicit
depth markers ┊ (one per level below the top):

  1: …          depth 1 (no marker)
  ┊a: …        depth 2
  ┊┊i: …       depth 3
  ┊┊┊1: …      depth 4 (numbers restart — no collision)
  ┊┊┊┊a: …     depth 5

A block at depth n is a maximal run of steps carrying exactly n-1
markers; it ends when a step with fewer markers appears. Since the
restarted depth-4 numbers are `┊┊┊1:` vs top-level `1:` —
different tokens — the greedy swallow of the marker-free design is
structurally impossible. Numbering becomes decoration: identifiers
serve as roman labels (no keyword shadowing), and the consecutiveness
audit remains purely as a typo check. -/

inductive JSValue where
  | undefined | null | boolean (b : Bool) | number (n : Float)
  | str (s : String)
  | listV (l : List JSValue)     -- spec List, injected for the AO layer
  | compl (abrupt : Bool) (v : JSValue)  -- Completion Record, as a value
  deriving Repr, BEq
instance : Inhabited JSValue := ⟨.undefined⟩

inductive E2 where
  | nv (name : String)
  | nat (n : Nat)
  | const (v : JSValue)
  | isObject (e : E2)
  | isNotObject (e : E2)
  | isNotUndefined (e : E2)
  | hasCall (e : E2)
  | hasCtor (e : E2)
  | isU (e : E2)
  | isBoolVal (b : Bool) (e : E2)
  | isStrVal (s : String) (e : E2)
  | isNullOrUnd (e : E2)
  | varNotPresent (name : String)
  | call (name : String) (args : List E2)
  deriving Repr

inductive P2 where
  | getMethod (o : E2) (sym : String)
  | getV (v : E2) (p : E2)
  | call (f : E2) (thisArg : E2) (arg : E2)
  | ordinaryToPrimitive (o : E2) (hint : E2)
  deriving Repr

/- Clean, label-free AST (what the interpreter consumes). -/
inductive Step where
  | ret (v : E2)
  | retQ (op : P2)
  | assertE (e : E2)
  | forEach (x : String) (e : E2) (body : List Step)
  | throw
  | setE (name : String) (e : E2)
  | letQ (name : String) (op : P2)
  | letE (name : String) (e : E2)
  | ifS (c : E2) (t : List Step) (e : List Step)
  | elseM (body : List Step)
  deriving Repr

abbrev Prog := List Step

/- Label-carrying parallel AST (what the audit consumes). -/
inductive LBody where
  | ret (v : E2)
  | retQ (op : P2)
  | assertE (e : E2)
  | forEach (x : String) (e : E2) (body : List (String × LBody))
  | throw
  | setE (name : String) (e : E2)
  | letQ (name : String) (op : P2)
  | letE (name : String) (e : E2)
  | ifS (c : E2) (t : List (String × LBody)) (e : List (String × LBody))
  | elseM (body : List (String × LBody))
  deriving Repr

abbrev LStep := String × LBody

/- Flat stream body: ifs and elses carry no branches here;
   `renest` fills them in from the depth markers. -/
inductive FBody where
  | ret (v : E2)
  | retQ (op : P2)
  | throw
  | setE (name : String) (e : E2)
  | ifI (c : E2) (s : FBody)
  | elseI (s : FBody)
  | elseG (c : E2)
  | assertE (e : E2)
  | forEach (x : String) (e : E2)
  | letQ (name : String) (op : P2)
  | letE (name : String) (e : E2)
  | ifS (c : E2)
  | elseM
  deriving Repr

abbrev FStep := Nat × String × FBody

/- Fuse an ECMA-262 `N. Else,` step into the immediately preceding if.
   A dangling marker is kept in the output — a stray "else" can never
   silently lose its branch; it stays visible for the audit. -/
/- else-if CHAINS nest: an else-step attaches to the end of the last
   if's else-branch, not by overwriting it. A dangling else (no
   preceding if) stays visible. -/
def attach (e : List LStep) : List LStep → List LStep
  | [] => e                                          -- pending else becomes the branch
  | [(l2, LBody.ifS c2 t2 e2)] =>                    -- chain end: nest here
      [(l2, LBody.ifS c2 t2 (attach e e2))]
  | [p] => [p, ("", LBody.elseM e)]                  -- dangling: stays visible
  | s :: rest => s :: attach e rest

def fuseL : List LStep → List LStep
  | [] => []
  | (l, LBody.ifS c t e') :: (_, LBody.elseM e) :: rest =>
      (l, LBody.ifS c t (attach e e')) :: fuseL rest
  | p :: rest => p :: fuseL rest

mutual
def strip : List LStep → Prog
  | [] => []
  | (l, b) :: rest => stripBody b :: strip rest
def stripBody : LBody → Step
  | .ret v => .ret v
  | .throw => .throw
  | .assertE e => .assertE e
  | .forEach x e b => .forEach x e (strip b)
  | .retQ op => .retQ op
  | .setE n e => .setE n e
  | .letQ n op => .letQ n op
  | .letE n e => .letE n e
  | .ifS c t e => .ifS c (strip t) (strip e)
  | .elseM b => .elseM (strip b)
end

/- Fuse else-steps, then strip labels. -/
def toProg (l : List LStep) : Prog := strip (fuseL l)

/- Consecutiveness audit: label ordinals per scheme (1→1, a→1, i→1). -/
def romanOrd : String → Option Nat
  | "i" => some 1 | "ii" => some 2 | "iii" => some 3
  | "iv" => some 4 | "v" => some 5 | "vi" => some 6
  | _ => none

def labelOrd (s : String) : Option Nat :=
  match s.toNat? with
  | some n => some n
  | none =>
    match romanOrd s with
    | some n => some n
    | none =>
      if s.length == 1
          && s.front.toNat ≥ 'a'.toNat && s.front.toNat ≤ 'z'.toNat then
        some (s.front.toNat - 'a'.toNat + 1)
      else none

mutual
/- check l i: the labels of l are i, i+1, i+2, … and every nested
   block (checked recursively) also starts at 1. -/
def check : List LStep → Nat → Bool
  | [], _ => true
  | p :: rest, i =>
      match labelOrd p.1 with
      | some n => n == i && checkBody p.2 && check rest (i + 1)
      | none => false
def checkBody : LBody → Bool
  | .ifS _ t e => check t 1 && check e 1
  | .forEach _ _ b => check b 1
  | .elseM b => check b 1
  | _ => true
end

def checkRun (l : List LStep) : Bool := check l 1

declare_syntax_cat stmt
declare_syntax_cat fstep
declare_syntax_cat algExpr
/- Spec variables whose names collide with keyword atoms ("method"
   from "internal method") live here — the explicit extension list is
   part of the audit. -/
declare_syntax_cat var
syntax ident : var
syntax "method" : var
declare_syntax_cat algPrim
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
syntax "~" "string" "~" : isTail
syntax "~" "number" "~" : isTail
syntax "either" "undefined" "or" "null" : isTail
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
syntax ident : aoName
syntax "OrdinaryToPrimitive" : aoName
syntax "GetMethod" : aoName
syntax "GetV" : aoName
syntax "Get" : aoName
syntax "Call" : aoName
syntax aoName "(" ")" : algExpr
syntax aoName "(" callArgs ")" : algExpr

/- `x is not …` — the tail is its own category so alternatives differ
   at the first token (shared prefixes past one token don't backtrack). -/
syntax algExpr "is" isTail : algExpr
syntax "number" : algExpr
syntax "string" : algExpr


syntax "GetMethod" "(" algExpr "," ident ")" : algPrim
syntax "GetMethod" "(" algExpr "," "%" ident "%" ")" : algPrim
syntax "GetV" "(" algExpr "," algExpr ")" : algPrim
syntax "Get" "(" algExpr "," algExpr ")" : algPrim
syntax "Call" "(" algExpr "," algExpr ")" : algPrim
syntax "GetMethod" "(" algExpr "," "@" "@" ident ")" : algPrim
syntax "OrdinaryToPrimitive" "(" algExpr "," algExpr ")" : algPrim
/- Deviation: the spec's « argList » — Lean lexes « » as identifier
   delimiters, so the list brackets are dropped (single arg for now). -/
syntax "Call" "(" algExpr "," algExpr "," algExpr ")" : algPrim

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
syntax kwLet var "be" "?" algPrim "." : stmt
syntax kwLet var "be" algExpr "." : stmt
syntax kwReturn algExpr "." : stmt
syntax kwReturn "?" algPrim "." : stmt
syntax kwThrow "." : stmt
syntax kwThrow "a" "TypeError" "exception" "." : stmt
syntax kwAssert ":" algExpr "." : stmt
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
syntax "[p|" algPrim "]" : term
syntax "[s|" stmt "]" : term

/- The numeral lexer glues a trailing dot into one scientific token
   ("1."), so numeric labels and integer literals both arrive as
   scientific tokens; strip the dot to recover the Nat. -/
open Lean in
def sciNat (n : TSyntax `scientific) : Nat :=
  let strip : String → Nat := fun v => (String.ofList (v.toList.dropLast)).toNat?.getD 0
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
def aoNameOf (x : TSyntax `aoName) : String :=
  let inner (w : Lean.Syntax) : String :=
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
def varName (x : TSyntax `var) : String :=
  let inner : Lean.Syntax → String :=
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

def listOfStrings (s : String) : JSValue :=
  .listV ((s.splitOn "\x1f").map JSValue.str)

open Lean in
macro_rules
  | `([e| $f:aoName ( )]) =>
      ``(E2.call $(quote (aoNameOf f)) [])
  | `([e| $f:aoName ( $as:callArgs )]) =>
      ``(E2.call $(quote (aoNameOf f)) [ca| $as])
  | `([e| $x:var]) =>
      /- A « … » token lexes as ONE bracketed identifier. Quoted
         elements (« "a", "b" ») become a spec-List literal; a single
         unquoted element (« hint ») is the argument-list notation for
         a variable. -/
      let strDL (s : String) : String := String.ofList (s.toList.dropLast)
      let strDF (s : String) : String := String.ofList (s.toList.drop 1)
      let strTW (s : String) : String :=
        String.ofList ((s.toList.dropWhile Char.isWhitespace).reverse
          |>.dropWhile Char.isWhitespace |>.reverse)
      let idTxt (w : Lean.Syntax) : String :=
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
      if txt.startsWith "«" && txt.contains "\""
      then
        let inner := strDF (strDL txt)
        let elems := (inner.splitOn ",").map (fun q => strDL (strDF (strTW q)))
        ``(E2.const (listOfStrings $(quote (String.intercalate "\x1f" elems))))
      else ``(E2.nv $(quote (varName x)))
  | `([e| undefined]) => ``(E2.const JSValue.undefined)
  | `([e| true]) => ``(E2.const (JSValue.boolean Bool.true))
  | `([e| false]) => ``(E2.const (JSValue.boolean Bool.false))
  | `([e| $n:num]) => ``(E2.nat ($n : Nat))
  | `([e| $n:scientific]) => ``(E2.nat $(quote (sciNat n)))
  | `([e| $s:str]) => ``(E2.const (JSValue.str $s))
  | `([e| ~ string ~]) => ``(E2.const (JSValue.str "string"))
  | `([e| ~ number ~]) => ``(E2.const (JSValue.str "number"))
  | `([e| ~ $v:ident ~]) => ``(E2.const (JSValue.str $(quote (toString v.getId))))
  | `([e| $e:algExpr is either undefined or null]) =>
      ``(E2.isNullOrUnd [e| $e])
  | `([e| $e:algExpr is string]) =>
      ``(E2.isStrVal "string" [e| $e])
  | `([e| $e:algExpr is number]) =>
      ``(E2.isStrVal "number" [e| $e])
  | `([e| $e:algExpr is ~ string ~]) =>
      ``(E2.isStrVal "string" [e| $e])
  | `([e| $e:algExpr is ~ number ~]) =>
      ``(E2.isStrVal "number" [e| $e])
  | `([e| $e:algExpr is ~ $v:ident ~]) =>
      ``(E2.isStrVal $(quote (toString v.getId)) [e| $e])
  | `([e| $e:algExpr is an Object]) => ``(E2.isObject [e| $e])
  | `([e| $e:algExpr is not an Object]) => ``(E2.isNotObject [e| $e])
  | `([e| $e:algExpr is not undefined]) => ``(E2.isNotUndefined [e| $e])
  | `([e| $e:algExpr has a [[Call]] internal method]) => ``(E2.hasCall [e| $e])
  | `([e| $e:algExpr has a [[Construct]] internal method]) => ``(E2.hasCtor [e| $e])
  | `([e| $e:algExpr is undefined]) => ``(E2.isU [e| $e])
  | `([e| $e:algExpr is true]) => ``(E2.isBoolVal Bool.true [e| $e])
  | `([e| $e:algExpr is false]) => ``(E2.isBoolVal Bool.false [e| $e])
  | `([e| $e:algExpr is not present]) =>
      let name := match e.raw with
        | .ident _ s _ _ => s.toString
        | _ => "?"
      ``(E2.varNotPresent $(quote name))
  | `([e| number]) => ``(E2.const (JSValue.str "number"))
  | `([e| string]) => ``(E2.const (JSValue.str "string"))

open Lean in
macro_rules
  | `([ca| $x:algExpr]) => `([[e| $x]])
  | `([ca| $xs:callArgs , $x:algExpr]) => `([ca| $xs] ++ [[e| $x]])

open Lean in
macro_rules
  | `([p| GetMethod ( $o:algExpr , $x:ident )]) =>
      ``(P2.getMethod [e| $o] $(quote (toString x.getId)))
  | `([p| GetMethod ( $o:algExpr , % $x:ident % )]) =>
      ``(P2.getMethod [e| $o] $(quote ("%" ++ toString x.getId ++ "%")))
  | `([p| GetMethod ( $o:algExpr , @ @ $x:ident )]) =>
      ``(P2.getMethod [e| $o] $(quote ("@@" ++ toString x.getId)))
  | `([p| Get ( $o:algExpr , $p:algExpr )]) =>
      ``(P2.getV [e| $o] [e| $p])
  | `([p| Call ( $f:algExpr , $t:algExpr )]) =>
      ``(P2.call [e| $f] [e| $t] (E2.const JSValue.undefined))
  | `([p| GetV ( $v:algExpr , $p:algExpr )]) =>
      ``(P2.getV [e| $v] [e| $p])
  | `([p| OrdinaryToPrimitive ( $o:algExpr , $h:algExpr )]) =>
      ``(P2.ordinaryToPrimitive [e| $o] [e| $h])
  | `([p| Call ( $f:algExpr , $t:algExpr , $x:algExpr )]) =>
      ``(P2.call [e| $f] [e| $t] [e| $x])

open Lean in
macro_rules
  | `([s| $l:kwLet $x:var be $n:scientific]) =>
      ``(FBody.letE $(quote (varName x)) (E2.nat $(quote (sciNat n))))
  | `([s| $r:kwReturn $n:scientific]) =>
      ``(FBody.ret (E2.nat $(quote (sciNat n))))
  | `([s| $s:kwSet $x:var to $n:scientific]) =>
      ``(FBody.setE $(quote (varName x)) (E2.nat $(quote (sciNat n))))
  | `([s| $l:kwLet $x:var be ? $op:algPrim .]) =>
      ``(FBody.letQ $(quote (varName x)) [p| $op])
  | `([s| $l:kwLet $x:var be $e:algExpr .]) =>
      ``(FBody.letE $(quote (varName x)) [e| $e])
  | `([s| $r:kwReturn ? $op:algPrim .]) =>
      ``(FBody.retQ [p| $op])
  | `([s| $t:kwThrow a TypeError exception .]) =>
      ``(FBody.throw)
  | `([s| $s:kwSet $x:var to $e:algExpr .]) =>
      ``(FBody.setE $(quote (varName x)) [e| $e])
  | `([s| $k:kwIf $c:algExpr , $s:stmt]) =>
      ``(FBody.ifI [e| $c] [s| $s])
  | `([s| $e:kwElse , $s:stmt]) =>
      ``(FBody.elseI [s| $s])
  | `([s| $r:kwReturn $x:ident .]) =>
      ``(FBody.ret (E2.nv $(quote (toString x.getId))))
  | `([s| $r:kwReturn undefined .]) =>
      ``(FBody.ret (E2.const JSValue.undefined))
  | `([s| $r:kwReturn true .]) =>
      ``(FBody.ret (E2.const (JSValue.boolean Bool.true)))
  | `([s| $r:kwReturn false .]) =>
      ``(FBody.ret (E2.const (JSValue.boolean Bool.false)))
  | `([s| $t:kwThrow .]) =>
      ``(FBody.throw)
  | `([s| $k:kwIf $c:algExpr , $t:kwThen]) =>
      ``(FBody.ifS [e| $c])
  | `([s| $e:kwElse ,]) =>
      ``(FBody.elseM)
  | `([s| $e:kwElse if $c:algExpr , then]) =>
      ``(FBody.elseG [e| $c])
  | `([s| Assert : $e:algExpr .]) =>
      ``(FBody.assertE [e| $e])
  | `([s| $f:kwFor each element $x:var of $e:algExpr , do]) =>
      ``(FBody.forEach $(quote (varName x)) [e| $e])

/- Layout recovery: the flat stream (depth, label, body) is re-nested
   by bar count — takeBody collects the run of strictly deeper steps
   following an if/else; renest recurses into it. -/
/- Inline bodies ("If c, stmt.") have no labelled sub-steps; they
   desugar to a singleton branch labelled "a" — the label the step
   would have carried as a sub-step, keeping the audit meaningful. -/
def inlineBody : FBody → LBody
  | .ret v => .ret v
  | .retQ op => .retQ op
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
  | .letQ n op => .letQ n op
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
  | f + 1, (d, l, .ret v) :: rest => (l, LBody.ret v) :: renestGo f rest
  | f + 1, (d, l, .throw) :: rest => (l, LBody.throw) :: renestGo f rest
  | f + 1, (d, l, .retQ op) :: rest => (l, LBody.retQ op) :: renestGo f rest
  | f + 1, (d, l, .setE n e) :: rest => (l, LBody.setE n e) :: renestGo f rest
  | f + 1, (d, l, .ifI c s) :: rest =>
      (l, LBody.ifS c [("a", inlineBody s)] []) :: renestGo f rest
  | f + 1, (d, l, .elseI s) :: rest =>
      (l, LBody.elseM [("a", inlineBody s)]) :: renestGo f rest
  | f + 1, (d, l, .elseG c) :: rest =>
      let (t, rest2) := takeBody d rest
      (l, LBody.elseM [("a", LBody.ifS c (renestGo f t) [])]) :: renestGo f rest2
  | f + 1, (d, l, .assertE e) :: rest =>
      (l, LBody.assertE e) :: renestGo f rest
  | f + 1, (d, l, .forEach x e) :: rest =>
      let (t, rest2) := takeBody d rest
      (l, LBody.forEach x e (renestGo f t)) :: renestGo f rest2
  | f + 1, (d, l, .letQ n op) :: rest =>
      (l, LBody.letQ n op) :: renestGo f rest
  | f + 1, (d, l, .letE n e) :: rest =>
      (l, LBody.letE n e) :: renestGo f rest
termination_by f _ => f

def renest (fs : List FStep) : List LStep := renestGo fs.length fs

def build (fs : List FStep) : Prog := strip (fuseL (renest fs))

open Lean in
macro_rules
  | `([f| $n:scientific $s:stmt]) =>
      let lbl := match n.raw with
        | .atom _ v => String.ofList (v.toList.dropLast)
        | .node _ _ args =>
          match (args[0]? : Option Lean.Syntax) with
          | some (Lean.Syntax.atom _ v) => String.ofList (v.toList.dropLast)
          | _ => "?"
        | _ => "?"
      `([(0, $(quote lbl), [s| $s])])
  | `([f| ┊ $n:scientific $s:stmt]) =>
      let lbl := match n.raw with
        | .atom _ v => String.ofList (v.toList.dropLast)
        | .node _ _ args =>
          match (args[0]? : Option Lean.Syntax) with
          | some (Lean.Syntax.atom _ v) => String.ofList (v.toList.dropLast)
          | _ => "?"
        | _ => "?"
      `([(1, $(quote lbl), [s| $s])])
  | `([f| ┊ ┊ $n:scientific $s:stmt]) =>
      let lbl := match n.raw with
        | .atom _ v => String.ofList (v.toList.dropLast)
        | .node _ _ args =>
          match (args[0]? : Option Lean.Syntax) with
          | some (Lean.Syntax.atom _ v) => String.ofList (v.toList.dropLast)
          | _ => "?"
        | _ => "?"
      `([(2, $(quote lbl), [s| $s])])
  | `([f| ┊ ┊ ┊ $n:scientific $s:stmt]) =>
      let lbl := match n.raw with
        | .atom _ v => String.ofList (v.toList.dropLast)
        | .node _ _ args =>
          match (args[0]? : Option Lean.Syntax) with
          | some (Lean.Syntax.atom _ v) => String.ofList (v.toList.dropLast)
          | _ => "?"
        | _ => "?"
      `([(3, $(quote lbl), [s| $s])])
  | `([f| ┊ ┊ ┊ ┊ $n:scientific $s:stmt]) =>
      let lbl := match n.raw with
        | .atom _ v => String.ofList (v.toList.dropLast)
        | .node _ _ args =>
          match (args[0]? : Option Lean.Syntax) with
          | some (Lean.Syntax.atom _ v) => String.ofList (v.toList.dropLast)
          | _ => "?"
        | _ => "?"
      `([(4, $(quote lbl), [s| $s])])
  | `([f| ┊ ┊ ┊ ┊ ┊ $n:scientific $s:stmt]) =>
      let lbl := match n.raw with
        | .atom _ v => String.ofList (v.toList.dropLast)
        | .node _ _ args =>
          match (args[0]? : Option Lean.Syntax) with
          | some (Lean.Syntax.atom _ v) => String.ofList (v.toList.dropLast)
          | _ => "?"
        | _ => "?"
      `([(5, $(quote lbl), [s| $s])])
  | `([f| ┊ ┊ ┊ ┊ ┊ ┊ $n:scientific $s:stmt]) =>
      let lbl := match n.raw with
        | .atom _ v => String.ofList (v.toList.dropLast)
        | .node _ _ args =>
          match (args[0]? : Option Lean.Syntax) with
          | some (Lean.Syntax.atom _ v) => String.ofList (v.toList.dropLast)
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

abbrev Env := List (String × JSValue)

def lookup : Env → String → Option JSValue
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

/- Bedrock predicates on values (no objects in this universe yet). -/
def isUndV : JSValue → Bool
  | .undefined => Bool.true
  | _ => Bool.false

def isObjV : JSValue → Bool := fun _ => Bool.false

def hasCallV : JSValue → Bool := fun _ => Bool.false
def hasCtorV : JSValue → Bool := fun _ => Bool.false
def isNullV : JSValue → Bool
  | .null => Bool.true
  | _ => Bool.false

/- Toy semantics: no objects in this value universe, primitives
   return undefined. Calls are machine-only: the big-step evaluator
   cannot enter the registry. -/
def evalE2 (env : Env) : E2 → Option JSValue
  | .nv n => lookup env n
  | .nat n => some (.number n.toFloat)
  | .const v => some v
  | .isObject e =>
      match evalE2 env e with
      | some v => some (.boolean (isObjV v))
      | none => none
  | .isNotObject e =>
      match evalE2 env e with
      | some v => some (.boolean (!isObjV v))
      | none => none
  | .hasCall e =>
      match evalE2 env e with
      | some v => some (.boolean (hasCallV v))
      | none => none
  | .hasCtor e =>
      match evalE2 env e with
      | some v => some (.boolean (hasCtorV v))
      | none => none
  | .isU e =>
      match evalE2 env e with
      | some v => some (.boolean (isUndV v))
      | none => none
  | .isBoolVal b e =>
      match evalE2 env e with
      | some v => some (.boolean (v == .boolean b))
      | none => none
  | .isNullOrUnd e =>
      match evalE2 env e with
      | some v => some (.boolean (isUndV v || isNullV v))
      | none => none
  | .isStrVal s e =>
      match evalE2 env e with
      | some v => some (.boolean (v == .str s))
      | none => none
  | .varNotPresent n => some (.boolean (lookup env n).isNone)
  | .call _ _ => none
  | .isNotUndefined e =>
      match evalE2 env e with
      | some .undefined => some (.boolean Bool.false)
      | some _ => some (.boolean Bool.true)
      | none => none

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
      match evalE2 env v with
      | some v => (.ret v, env)
      | none => (.fall, env)
  | env, .throw :: _ => (.thrown, env)
  | env, .forEach _ _ _ :: _ => (.fall, env)   -- loops are machine-level (kstep)
  | env, .assertE e :: rest =>
      match evalE2 env e with
      | some (.boolean Bool.true) => run env rest
      | _ => (.fall, env)
  | env, .retQ op :: _ =>
      match evalP2 op with
      | some v => (.ret v, env)
      | none => (.fall, env)
  | env, .setE n e :: rest =>
      match evalE2 env e with
      | some v => run ((n, v) :: env) rest
      | none => (.fall, env)
  | env, .letQ n op :: rest =>
      match evalP2 op with
      | some v => run ((n, v) :: env) rest
      | none => (.fall, env)
  | env, .letE n e :: rest =>
      match evalE2 env e with
      | some v => run ((n, v) :: env) rest
      | none => (.fall, env)
  | env, .ifS c t e :: rest =>
      match evalE2 env c with
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

inductive Arg where
  | ev (v : JSValue)              -- already a value
  | ee (e : E2)                   -- pending expression
  deriving Repr

inductive Prim where              -- bedrock predicates (the axiom stratum)
  | pIsObj | pIsNotObj | pIsNotU | pHasCall
  | pHasCtor | pIsU | pIsTrue | pIsFalse
  | pNullOrUnd
  | pWrapC
  | pThrowC
  | pIsStr (s : String)
  deriving Repr

inductive Kon where
  | kIte (t e : List Step)
  | kEach (x : String) (body : List Step)
  | kBind (n : String)
  | kRet
  | kPrim (p : Prim) (k : Kon)
  | kEnter (f : String) (k : Kon)
  | kSpine (as : List E2) (rs : List JSValue) (k : Kon)
  deriving Repr

inductive Rt where                -- runtime statements: source steps + bookkeeping
  | kLoopS (x : String) (elems : List JSValue) (body : List Rt) (cont : List Rt)
  | step (s : Step)
  | kEvalS (cur : Arg) (as : List E2) (rs : List JSValue) (k : Kon)
  | kEvalNextS (as : List E2) (rs : List JSValue) (k : Kon)
  | kUnwindS
  deriving Repr

/- Control boundaries as frames: the callee REPLACES the current list
   (caller continuation saved in the frame — cannot be spliced wrong),
   and return POPS one frame (no scanning, cannot discard past a
   boundary). break/continue/try later = more Frame kinds. -/
inductive Frame where
  | kRestoreF (ce : Env) (st : List Rt) (k : Kon)
  deriving Repr

inductive KM where
  | krun (cur : List Rt) (env : Env) (stack : List Frame)
  | kdone (v : JSValue)
  | kthrown
  | kfell
  deriving Repr

def applyPrim : Prim → JSValue → JSValue
  | .pIsObj, v => .boolean (isObjV v)
  | .pIsNotObj, v => .boolean (!isObjV v)
  | .pIsNotU, v => .boolean (!isUndV v)
  | .pHasCall, v => .boolean (hasCallV v)
  | .pHasCtor, v => .boolean (hasCtorV v)
  | .pIsU, v => .boolean (isUndV v)
  | .pIsTrue, v => .boolean (v == .boolean Bool.true)
  | .pIsFalse, v => .boolean (v == .boolean Bool.false)
  | .pIsStr s, v => .boolean (v == .str s)
  | .pNullOrUnd, v => .boolean (isUndV v || isNullV v)
  | .pWrapC, v => .compl Bool.false v
  | .pThrowC, v => .compl Bool.true v

/- The transcribed-operation registry (the corpus). -/
abbrev AOReg := List (String × (List String × Prog))

def findAO : AOReg → String → Option (List String × Prog)
  | [], _ => none
  | (n, e) :: r, n' => if n == n' then some e else findAO r n'

def kstep (reg : AOReg) : KM → KM
  | .kdone v => .kdone v
  | .kthrown => .kthrown
  | .kfell => .kfell
  | .krun [] _ _ => .kfell        -- fell off the end: top level, or callee w/o return
  | .krun (.step (.ret v) :: st) env stack =>
      .krun (.kEvalS (.ee v) [] [] .kRet :: st) env stack
  | .krun (.step (.forEach x e body) :: st) env stack =>
      .krun (.kEvalS (.ee e) [] [] (.kEach x body) :: st) env stack
  | .krun (.step (.assertE e) :: st) env stack =>
      match evalE2 env e with
      | some (.boolean Bool.true) => .krun st env stack
      | _ => .kfell               -- failed assert: stuck, loudly (asserts are pure)
  | .krun (.step (.retQ op) :: st) env stack =>
      match evalP2 op with
      | some v => .krun (.kEvalS (.ev v) [] [] .kRet :: st) env stack
      | none => .kfell
  | .krun (.step (.setE n e) :: st) env stack =>
      .krun (.kEvalS (.ee e) [] [] (.kBind n) :: st) env stack
  | .krun (.step .throw :: st) env stack => .krun (.kUnwindS :: st) env stack
  | .krun (.step (.letE n e) :: st) env stack =>
      .krun (.kEvalS (.ee e) [] [] (.kBind n) :: st) env stack
  | .krun (.step (.letQ n op) :: st) env stack =>
      match evalP2 op with
      | some v => .krun st ((n, v) :: env) stack
      | none => .kfell
  | .krun (.step (.ifS c t e) :: st) env stack =>
      .krun (.kEvalS (.ee c) [] [] (.kIte t e) :: st) env stack
  | .krun (.step (.elseM _) :: st) env stack => .krun st env stack
  | .krun (.kEvalS (.ev v) as rs k :: st) env stack =>
      .krun (.kEvalNextS as (v :: rs) k :: st) env stack
  | .krun (.kEvalS (.ee (.nv n)) as rs k :: st) env stack =>
      match lookup env n with
      | some v => .krun (.kEvalS (.ev v) as rs k :: st) env stack
      | none => .kfell
  | .krun (.kEvalS (.ee (.nat n)) as rs k :: st) env stack =>
      .krun (.kEvalS (.ev (.number n.toFloat)) as rs k :: st) env stack
  | .krun (.kEvalS (.ee (.const v)) as rs k :: st) env stack =>
      .krun (.kEvalS (.ev v) as rs k :: st) env stack
  | .krun (.kEvalS (.ee (.isObject e')) as rs k :: st) env stack =>
      .krun (.kEvalS (.ee e') [] [] (.kPrim .pIsObj (.kSpine as rs k)) :: st) env stack
  | .krun (.kEvalS (.ee (.isNotObject e')) as rs k :: st) env stack =>
      .krun (.kEvalS (.ee e') [] [] (.kPrim .pIsNotObj (.kSpine as rs k)) :: st) env stack
  | .krun (.kEvalS (.ee (.isNotUndefined e')) as rs k :: st) env stack =>
      .krun (.kEvalS (.ee e') [] [] (.kPrim .pIsNotU (.kSpine as rs k)) :: st) env stack
  | .krun (.kEvalS (.ee (.hasCall e')) as rs k :: st) env stack =>
      .krun (.kEvalS (.ee e') [] [] (.kPrim .pHasCall (.kSpine as rs k)) :: st) env stack
  | .krun (.kEvalS (.ee (.hasCtor e')) as rs k :: st) env stack =>
      .krun (.kEvalS (.ee e') [] [] (.kPrim .pHasCtor (.kSpine as rs k)) :: st) env stack
  | .krun (.kEvalS (.ee (.isU e')) as rs k :: st) env stack =>
      .krun (.kEvalS (.ee e') [] [] (.kPrim .pIsU (.kSpine as rs k)) :: st) env stack
  | .krun (.kEvalS (.ee (.isNullOrUnd e')) as rs k :: st) env stack =>
      .krun (.kEvalS (.ee e') [] [] (.kPrim .pNullOrUnd (.kSpine as rs k)) :: st) env stack
  | .krun (.kEvalS (.ee (.isStrVal s e')) as rs k :: st) env stack =>
      .krun (.kEvalS (.ee e') [] [] (.kPrim (.pIsStr s) (.kSpine as rs k)) :: st) env stack
  | .krun (.kEvalS (.ee (.isBoolVal b e')) as rs k :: st) env stack =>
      .krun (.kEvalS (.ee e') [] [] (.kPrim (if b then .pIsTrue else .pIsFalse) (.kSpine as rs k)) :: st) env stack
  | .krun (.kEvalS (.ee (.varNotPresent n)) as rs k :: st) env stack =>
      .krun (.kEvalS (.ev (.boolean (lookup env n).isNone)) as rs k :: st) env stack
  | .krun (.kEvalS (.ee (.call f args)) as rs k :: st) env stack =>
      .krun (.kEvalNextS args [] (.kEnter f (.kSpine as rs k)) :: st) env stack
  | .krun (.kEvalNextS (x :: as) rs k :: st) env stack =>
      .krun (.kEvalS (.ee x) as rs k :: st) env stack
  | .krun (.kEvalNextS [] [] _ :: _) _ _ => .kfell
  | .krun (.kEvalNextS [] rs (.kIte t e) :: st) env stack =>
      match rs with
      | .boolean b :: _ => .krun ((if b then t else e).map Rt.step ++ st) env stack
      | _ => .kfell      -- non-Boolean condition: transcription/type error, stuck loudly
  | .krun (.kEvalNextS [] rs (.kEach x body) :: st) env stack =>
      match rs with
      | .listV l :: _ => .krun (.kLoopS x l (body.map Rt.step) st :: st) env stack
      | _ => .kfell     -- For each over a non-List: stuck, loudly
  | .krun (.kLoopS x (v :: rest') body _ :: st) env stack =>
      .krun (body ++ [.kLoopS x rest' body st] ++ st) ((x, v) :: env) stack
  | .krun (.kLoopS x [] _ cont :: st) env stack => .krun cont env stack
  | .krun (.kEvalNextS [] rs (.kBind n) :: st) env stack =>
      match rs with
      | v :: _ => .krun st ((n, v) :: env) stack
      | [] => .kfell
  | .krun (.kEvalNextS [] rs (.kPrim p k) :: st) env stack =>
      match rs with
      | v :: _ => .krun (.kEvalS (.ev (applyPrim p v)) [] [] k :: st) env stack
      | [] => .kfell
  | .krun (.kEvalNextS [] rs (.kSpine as' rs' k) :: st) env stack =>
      match rs with
      | v :: _ => .krun (.kEvalS (.ev v) as' rs' k :: st) env stack
      | [] => .kfell
  | .krun (.kEvalNextS [] rs (.kEnter f k) :: st) env stack =>
      match findAO reg f with
      | some (ps, body) =>
          .krun (body.map Rt.step) (ps.zip rs.reverse) (.kRestoreF env st k :: stack)
      | none => .kfell             -- unknown operation: stuck, loudly
  /- returning: pop exactly one frame — everything in cur belongs to
     the callee and is discarded wholesale. -/
  | .krun (.kEvalNextS [] (v :: _) .kRet :: _) _ (.kRestoreF ce st' k' :: stack') =>
      .krun (.kEvalS (.ev v) [] [] k' :: st') ce stack'
  | .krun (.kEvalNextS [] (v :: _) .kRet :: _) _ [] => .kdone v
  /- unwinding: statements one per step, then through frames. -/
  | .krun (.kUnwindS :: _ :: st) env stack => .krun (.kUnwindS :: st) env stack
  | .krun [.kUnwindS] _ (.kRestoreF ce st' _ :: stack') =>
      .krun (.kUnwindS :: st') ce stack'
  | .krun [.kUnwindS] _ [] => .kthrown

def ksteps (reg : AOReg) : Nat → KM → KM
  | 0, m => m
  | n + 1, m => ksteps reg n (kstep reg m)

def ktrace (reg : AOReg) : Nat → KM → List KM
  | 0, _ => []
  | n + 1, m => m :: ktrace reg n (kstep reg m)

/- ===== SOS semantics: state = (remaining program, env).
   The if-rule splices the branch:  ifS c t e :: rest → (t ++ rest | e ++ rest).
   One SOS step = one whole statement (conditions/expressions evaluate atomically).
   Reference semantics closest to the spec prose; agreement with the machine
   above is the next theorem. ===== -/

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
      match evalE2 env v with
      | some v => .sret v
      | none => .sfell
  | .srun (.throw :: _) _ => .sthrown
  | .srun ((.forEach x e body) :: rest) env =>
      match evalE2 env e with
      | some (.listV l) =>
          -- finite unroll: set the binder before each copy of the body
          .srun (l.flatMap (fun v => .setE x (E2.const v) :: body) ++ rest) env
      | _ => .sfell
  | .srun (.assertE e :: rest) env =>
      match evalE2 env e with
      | some (.boolean Bool.true) => .srun rest env
      | _ => .sfell
  | .srun (.retQ op :: _) env =>
      match evalP2 op with
      | some v => .sret v
      | none => .sfell
  | .srun ((.setE n e) :: rest) env =>
      match evalE2 env e with
      | some v => .srun rest ((n, v) :: env)
      | none => .sfell
  | .srun ((.letE n e) :: rest) env =>
      match evalE2 env e with
      | some v => .srun rest ((n, v) :: env)
      | none => .sfell
  | .srun ((.letQ n op) :: rest) env =>
      match evalP2 op with
      | some v => .srun rest ((n, v) :: env)
      | none => .sfell
  | .srun ((.ifS c t e) :: rest) env =>
      match evalE2 env c with
      | some (.boolean b) => .srun (if b then t ++ rest else e ++ rest) env
      | _ => .sfell        -- non-Boolean condition: stuck, not coerced
  | .srun ((.elseM _) :: rest) env => .srun rest env

def sosSteps : Nat → SState → SState
  | 0, s => s
  | n + 1, s => sosSteps n (sosStep s)

def kmOf (p : Prog) : KM := .krun (p.map Rt.step) [] []

/- Outcome-level agreement: SOS and the machine step at different
   granularity, so compare terminals after enough steps for both. -/
def sameOutcome : SState → KM → Bool
  | .sret v, .kdone v' => v == v'
  | .sthrown, .kthrown => Bool.true
  | .sfell, .kfell => Bool.true
  | _, _ => Bool.false

def agree (reg : AOReg) (p : Prog) : Bool :=
  sameOutcome (sosSteps 200 (.srun p [])) (ksteps reg 200 (kmOf p))

/- ===== Frame machine: eval stack + frames + in-list loop markers.
   LoopFrame IS the statement list; the final marker is the redo
   instruction (user's design). Expressions decompose at runtime:

     kEval (call f [a1..an]) :: rt  =>  kEval a1 :: … :: kEval an :: kCall f n :: rt
     kEval (isObject e)      :: rt  =>  kEval e :: kPrim1 pIsObj :: rt

   Consumers pop the eval stack (top of stack = LAST pushed operand):
     kCall f n : pop n -> new frame (env = params.zip popped.reverse)
     kRet      : top of eval -> caller's eval, pop frame (stuck if empty)
     kThrow    : pop one frame per step, kThrow at the caller's head
     kSet/kDrop/kBranch/kAssert: pop 1
   Invariant (lemma, not type): eval stack empty at statement boundaries. -/

inductive Rt2 where
  | kEval (e : E2)
  | kPrim1 (p : Prim)
  | kPrimQ (op : P2)
  | kCall (f : String) (n : Nat)
  | kSet (x : String)
  | kPop
  | kIte (t e : List Rt2)
  | kAssert
  | kRet
  | kTest
  | kUnwrap
  | kRepeatWhile (c : E2) (body : List Rt2)
  | kRepeatTest (c : E2) (body : List Rt2)
  | kForStart (x : String) (body : List Rt2)
  | kForBody (x : String) (elems : List JSValue) (body : List Rt2)
  deriving Repr

structure Fr where
  stmts : List Rt2
  env   : Env
  eval  : List JSValue
  deriving Repr

inductive FM where
  | frames (fs : List Fr)
  | fdone (v : JSValue)
  | fell
  deriving Repr

/- Statement compilation (expressions stay as data; only statements
   become instruction sequences). -/

def compileSteps : List Step → List Rt2
  | [] => []
  | .ret v :: rest => .kEval v :: .kPrim1 .pWrapC :: .kRet :: compileSteps rest
  | .retQ op :: rest => .kPrimQ op :: .kRet :: compileSteps rest
  | .throw :: rest =>
      .kEval (.const JSValue.undefined) :: .kPrim1 .pThrowC :: .kRet
        :: compileSteps rest
  | .setE n e :: rest => .kEval e :: .kSet n :: compileSteps rest
  | .letQ n op :: rest =>
      .kPrimQ op :: .kTest :: .kIte [.kRet] [.kUnwrap] :: .kSet n :: compileSteps rest
  | .letE n e :: rest => .kEval e :: .kSet n :: compileSteps rest
  | .assertE e :: rest => .kEval e :: .kAssert :: compileSteps rest
  | .forEach x e body :: rest =>
      .kEval e :: .kForStart x (compileSteps body) :: compileSteps rest
  | .ifS c t e :: rest =>
      .kEval c :: .kIte (compileSteps t) (compileSteps e) :: compileSteps rest
  | .elseM _ :: rest => compileSteps rest   -- unreachable post-fuseL

def fmOf (p : Prog) : FM := .frames [⟨compileSteps p, [], []⟩]

def fstep (reg : AOReg) : FM → FM
  | .fdone v => .fdone v
  | .fell => .fell
  | .frames [] => .fell
  | .frames (⟨[], _, _⟩ :: _) => .fell        -- fell through without kRet
  | .frames (f :: fs) =>
    match f.stmts, f.env, f.eval with
    | [], _, _ => .fell
    | .kEval (.const v) :: rest, env, eval => .frames (⟨rest, env, v :: eval⟩ :: fs)
    | .kEval (.nat n) :: rest, env, eval =>
        .frames (⟨rest, env, .number n.toFloat :: eval⟩ :: fs)
    | .kEval (.nv x) :: rest, env, eval =>
        match lookup env x with
        | some v => .frames (⟨rest, env, v :: eval⟩ :: fs)
        | none => .fell                        -- unbound: stuck, loudly
    | .kEval (.varNotPresent x) :: rest, env, eval =>
        .frames (⟨rest, env, .boolean (lookup env x).isNone :: eval⟩ :: fs)
    | .kEval (.isObject e) :: rest, _, _ =>
        .frames (⟨.kEval e :: .kPrim1 .pIsObj :: f.stmts.tail!, f.env, f.eval⟩ :: fs)
    | .kEval (.isNotObject e) :: rest, _, _ =>
        .frames (⟨.kEval e :: .kPrim1 .pIsNotObj :: f.stmts.tail!, f.env, f.eval⟩ :: fs)
    | .kEval (.isNotUndefined e) :: rest, _, _ =>
        .frames (⟨.kEval e :: .kPrim1 .pIsNotU :: f.stmts.tail!, f.env, f.eval⟩ :: fs)
    | .kEval (.isU e) :: rest, _, _ =>
        .frames (⟨.kEval e :: .kPrim1 .pIsU :: f.stmts.tail!, f.env, f.eval⟩ :: fs)
    | .kEval (.hasCall e) :: rest, _, _ =>
        .frames (⟨.kEval e :: .kPrim1 .pHasCall :: f.stmts.tail!, f.env, f.eval⟩ :: fs)
    | .kEval (.hasCtor e) :: rest, _, _ =>
        .frames (⟨.kEval e :: .kPrim1 .pHasCtor :: f.stmts.tail!, f.env, f.eval⟩ :: fs)
    | .kEval (.isBoolVal b e) :: rest, _, _ =>
        .frames (⟨.kEval e :: .kPrim1 (if b then .pIsTrue else .pIsFalse)
                    :: f.stmts.tail!, f.env, f.eval⟩ :: fs)
    | .kEval (.isStrVal s e) :: rest, _, _ =>
        .frames (⟨.kEval e :: .kPrim1 (.pIsStr s) :: f.stmts.tail!, f.env, f.eval⟩ :: fs)
    | .kEval (.isNullOrUnd e) :: rest, _, _ =>
        .frames (⟨.kEval e :: .kPrim1 .pNullOrUnd :: f.stmts.tail!, f.env, f.eval⟩ :: fs)
    | .kEval (.call fname args) :: rest, env, eval =>
        -- bare and ? calls behave identically: test, propagate, extract.
        -- Completion(...) is the distinct no-test form (callC, to come).
        .frames (⟨args.map Rt2.kEval
                    ++ [.kCall fname args.length, .kTest, .kIte [.kRet] [.kUnwrap]]
                    ++ rest, env, eval⟩ :: fs)
    | .kPrim1 p :: rest, env, v :: eval =>
        .frames (⟨rest, env, applyPrim p v :: eval⟩ :: fs)
    | .kPrim1 _ :: _, _, [] => .fell            -- stack underflow: loud
    | .kPrimQ op :: rest, env, eval =>
        match evalP2 op with
        | some v => .frames (⟨rest, env, .compl Bool.false v :: eval⟩ :: fs)
        | none => .fell
    | .kCall fname n :: rest, env, eval =>
        if eval.length < n then .fell
        else
          let popped := eval.take n
          let older := eval.drop n
          match findAO reg fname with
          | some (ps, body) =>
              .frames (⟨compileSteps body, ps.zip popped.reverse, []⟩
                       :: ⟨rest, env, older⟩ :: fs)
          | none => .fell                          -- unknown operation: loud
    | .kSet x :: rest, env, v :: eval => .frames (⟨rest, (x, v) :: env, eval⟩ :: fs)
    | .kSet _ :: _, _, [] => .fell
    | .kPop :: rest, env, _ :: eval => .frames (⟨rest, env, eval⟩ :: fs)
    | .kPop :: _, _, [] => .fell
    | .kIte t e :: rest, env, .boolean b :: eval =>
        .frames (⟨(if b then t else e) ++ rest, env, eval⟩ :: fs)
    | .kIte _ _ :: _, _, _ => .fell                -- non-bool condition: loud
    | .kAssert :: rest, env, .boolean Bool.true :: eval => .frames (⟨rest, env, eval⟩ :: fs)
    | .kAssert :: _, _, _ => .fell                 -- failed assert: loud
    | .kRet :: _, _, v :: _ =>
        match fs with
        | caller :: fs' => .frames (⟨caller.stmts, caller.env, v :: caller.eval⟩ :: fs')
        | [] => .fdone v
    | .kRet :: _, _, [] =>
        /- return with nothing on the eval stack: allowed, no push -/
        match fs with
        | caller :: fs' => .frames (⟨caller.stmts, caller.env, caller.eval⟩ :: fs')
        | [] => .fell
    | .kTest :: rest, env, .compl abrupt v :: eval =>
        -- peek: the completion STAYS under the pushed boolean
        .frames (⟨rest, env, .boolean abrupt :: .compl abrupt v :: eval⟩ :: fs)
    | .kTest :: _, _, _ => .fell          -- top not a completion: loud
    | .kUnwrap :: rest, env, .compl _ v :: eval =>
        .frames (⟨rest, env, v :: eval⟩ :: fs)
    | .kUnwrap :: _, _, _ => .fell        -- top not a completion: loud
    | .kRepeatWhile c body :: rest, env, eval =>
        .frames (⟨.kEval c :: .kRepeatTest c body :: rest, env, eval⟩ :: fs)
    | .kRepeatTest c body :: rest, env, .boolean b :: eval =>
        .frames (⟨(if b then body ++ [.kRepeatWhile c body] else rest), env, eval⟩ :: fs)
    | .kRepeatTest _ _ :: _, _, _ => .fell
    | .kForStart x body :: rest, env, .listV [] :: eval =>
        .frames (⟨rest, env, eval⟩ :: fs)
    | .kForStart x body :: rest, env, .listV (v :: vs) :: eval =>
        .frames (⟨.kEval (.const v) :: .kSet x :: body
                    ++ [.kForBody x vs body] ++ rest, env, eval⟩ :: fs)
    | .kForStart _ _ :: _, _, _ => .fell           -- For each over non-List: loud
    | .kForBody x (v :: vs) body :: rest, env, eval =>
        .frames (⟨.kEval (.const v) :: .kSet x :: body
                    ++ [.kForBody x vs body] ++ rest, env, eval⟩ :: fs)
    | .kForBody _ [] _ :: rest, env, eval => .frames (⟨rest, env, eval⟩ :: fs)

def fsteps (reg : AOReg) : Nat → FM → FM
  | 0, m => m
  | n + 1, m => fsteps reg n (fstep reg m)

def sameOutcome2 : SState → FM → Bool
  | .sret v, .fdone (.compl Bool.false v') => v == v'
  | .sret v, .fdone v' => v == v'          -- bare value (never through a call)
  | .sthrown, .fdone (.compl Bool.true _) => Bool.true
  | .sfell, .fell => Bool.true
  | _, _ => Bool.false

def agree2 (reg : AOReg) (p : Prog) : Bool :=
  sameOutcome2 (sosSteps 200 (.srun p [])) (fsteps reg 500 (fmOf p))

def ftrace2 (reg : AOReg) : Nat → FM → List FM
  | 0, _ => []
  | n + 1, m => m :: ftrace2 reg n (fstep reg m)
