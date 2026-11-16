import metalanguage

/- ES 7.3.13 Call ( func, thisValue [ , argList ] ) - text-equal
   (tools/diff_spec.py). The registry-backed body replaces the old
   native stub: step 3's func.[[Call]] dispatches to the heap
   object's builtin code. -/

def call7_3_13 : List FStep := [alg|
  1. If argList is not present, set argList to a new empty List.
  2. If IsCallable(func) is false, throw a TypeError exception.
  3. Return ? func.[[Call]](thisValue, argList).
]

def AO_Call : AOReg :=
  [("Call", (["func", "thisValue", "argList"], build call7_3_13))]

#eval checkRun (renest call7_3_13)
