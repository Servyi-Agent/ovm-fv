import metalanguage

/- ES 7.4.7 IteratorComplete ( iteratorResult ) -  text-equal (tools/diff_spec.py).

   DEVIATION (documented): the spec's `? Get(...)` inside the return
   is a nested ? in an expression position; the metalanguage's ? is
   statement-level, so the return is written as the two-step
   let-then-return the compiler produces. -/

def iteratorComplete7_4_7 : List FStep := [alg|
  1. Let done be ? Get(iteratorResult, "done").
  2. Return ToBoolean(done).
]

def AO_IteratorComplete : AOReg :=
  [("IteratorComplete", (["iteratorResult"], build iteratorComplete7_4_7))]

#eval checkRun (renest iteratorComplete7_4_7)
