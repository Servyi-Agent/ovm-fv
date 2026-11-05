import metalanguage

/- ES 7.4.6 IteratorNext ( iteratorRecord [ , value ] ) -  text-equal (tools/diff_spec.py).

   Deviation: the spec's « value » list-literal argument is written
   bare (Lean lexes « » as identifier delimiters) — the documented
   corpus-wide deviation. -/

def iteratorNext7_4_6 : List FStep := [alg|
  1. If value is not present, then
    ┊ a. Let result be Completion(Call(iteratorRecord.[[NextMethod]], iteratorRecord.[[Iterator]])).
  2. Else,
    ┊ a. Let result be Completion(Call(iteratorRecord.[[NextMethod]], iteratorRecord.[[Iterator]], value)).
  3. If result is a throw completion, then
    ┊ a. Set iteratorRecord.[[Done]] to true.
    ┊ b. Return ? result.
  4. Set result to ! result.
  5. If result is not an Object, then
    ┊ a. Set iteratorRecord.[[Done]] to true.
    ┊ b. Throw a TypeError exception.
  6. Return result.
]

def AO_IteratorNext : AOReg :=
  [("IteratorNext", (["iteratorRecord", "value"], build iteratorNext7_4_6))]

#eval checkRun (renest iteratorNext7_4_6)
