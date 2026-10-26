import metalanguage

/- ES 7.1.13 ToObject ( argument ) - text-equal. -/

def toObject7_1_13 : List FStep := [alg|
  1. If arg is either undefined or null, throw a TypeError exception.
  2. If arg is a Boolean, return a new Boolean object whose [[BooleanData]] internal slot is set to arg.
  3. If arg is a Number, return a new Number object whose [[NumberData]] internal slot is set to arg.
  4. If arg is a String, return a new String object whose [[StringData]] internal slot is set to arg.
  5. If arg is a Symbol, return a new Symbol object whose [[SymbolData]] internal slot is set to arg.
  6. If arg is a BigInt, return a new BigInt object whose [[BigIntData]] internal slot is set to arg.
  7. Assert: arg is an Object.
  8. Return arg.
]

def AO_ToObject : AOReg :=
  [("ToObject", (["arg"], build toObject7_1_13))]

#eval checkRun (renest toObject7_1_13)
