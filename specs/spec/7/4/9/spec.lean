import metalanguage

/- ES 7.4.9 IteratorStep ( iteratorRecord ) -  text-equal (tools/diff_spec.py). -/

def iteratorStep7_4_9 : List FStep := [alg|
  1. Let result be ? IteratorNext(iteratorRecord).
  2. Let done be Completion(IteratorComplete(result)).
  3. If done is a throw completion, then
    ┊ a. Set iteratorRecord.[[Done]] to true.
    ┊ b. Return ? done.
  4. Set done to ! done.
  5. If done is true, then
    ┊ a. Set iteratorRecord.[[Done]] to true.
    ┊ b. Return done.
  6. Return result.
]

def AO_IteratorStep : AOReg :=
  [("IteratorStep", (["iteratorRecord"], build iteratorStep7_4_9))]

#eval checkRun (renest iteratorStep7_4_9)
