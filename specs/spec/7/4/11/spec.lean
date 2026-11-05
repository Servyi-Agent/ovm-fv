import metalanguage

/- ES 7.4.11 IteratorClose ( iteratorRecord, completion ) -  text-equal (tools/diff_spec.py).

   THE first-class-completion showcase: `completion` arrives as a
   completion-typed PARAMETER, `innerResult` is a completion-typed
   local, both are live simultaneously, tested, merged — and
   returned with `?` applied to a completion-typed variable. -/

def iteratorClose7_4_11 : List FStep := [alg|
  1. Assert: iteratorRecord.[[Iterator]] is an Object.
  2. Let iterator be iteratorRecord.[[Iterator]].
  3. Let innerResult be Completion(GetMethod(iterator, "return")).
  4. If innerResult is a normal completion, then
    ┊ a. Let return be innerResult.[[Value]].
    ┊ b. If return is undefined, return ? completion.
    ┊ c. Set innerResult to Completion(Call(return, iterator)).
  5. If completion is a throw completion, return ? completion.
  6. If innerResult is a throw completion, return ? innerResult.
  7. If innerResult.[[Value]] is not an Object, throw a TypeError exception.
  8. Return ? completion.
]

def AO_IteratorClose : AOReg :=
  [("IteratorClose", (["iteratorRecord", "completion"], build iteratorClose7_4_11))]

#eval checkRun (renest iteratorClose7_4_11)
