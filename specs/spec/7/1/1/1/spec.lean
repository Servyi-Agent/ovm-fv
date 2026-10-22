import metalanguage

/- ES 7.1.1.1 OrdinaryToPrimitive ( O, hint ) - text-equal. Get and
   Call are stubs until the heap; For each iterates a spec List. -/

def ordinaryToPrimitive7_1_1_1 : List FStep := [alg|
  1. If hint is ~string~, then
    ┊ a. Let methodNames be « "toString", "valueOf" ».
  2. Else,
    ┊ a. Let methodNames be « "valueOf", "toString" ».
  3. For each element name of methodNames, do
    ┊ a. Let method be ? Get(obj, name).
    ┊ b. If IsCallable(method) is true, then
    ┊ ┊ i. Let result be ? Call(method, obj).
    ┊ ┊ ii. If result is not an Object, return result.
  4. Throw a TypeError exception.
]

def AO_OrdinaryToPrimitive : AOReg :=
  [("OrdinaryToPrimitive", (["obj", "hint"], build ordinaryToPrimitive7_1_1_1))]

#eval checkRun (renest ordinaryToPrimitive7_1_1_1)
