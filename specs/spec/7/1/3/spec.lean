import metalanguage

/- ES 7.1.3 ToNumeric ( arg ) - text-equal. ToNumber is a native stub
   (undefined) until the number tower lands; no BigInt values exist
   in this universe, so step 2 is statically dead. -/

def toNumeric7_1_3 : List FStep := [alg|
  1. Let primitiveValue be ? ToPrimitive(arg, number).
  2. If primitiveValue is a BigInt, return primitiveValue.
  3. Return ? ToNumber(primitiveValue).
]

def AO_ToNumeric : AOReg :=
  [("ToNumeric", (["arg"], build toNumeric7_1_3))]

#eval checkRun (renest toNumeric7_1_3)