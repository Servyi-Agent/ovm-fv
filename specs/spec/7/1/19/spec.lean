import metalanguage

/- ES 7.1.19 ToString ( arg ) - text-equal. Deviations:
   namespace-qualified names Number::toString / BigInt::toString are
   guillemet idents («…») — Lean idents cannot contain `::`; both are
   native stubs until the number/BigInt towers land. No Symbol or
   BigInt values exist in this universe, so steps 2 and 8 are
   statically dead. Step 11's assert records one proof debt:
   ToPrimitive's declared return type (langV) includes objects. -/

def toString7_1_19 : List FStep := [alg|
  1. If arg is a String, return arg.
  2. If arg is a Symbol, throw a TypeError exception.
  3. If arg is undefined, return "undefined".
  4. If arg is null, return "null".
  5. If arg is true, return "true".
  6. If arg is false, return "false".
  7. If arg is a Number, return «Number::toString»(arg, 10).
  8. If arg is a BigInt, return «BigInt::toString»(arg, 10).
  9. Assert: arg is an Object.
  10. Let primitiveValue be ? ToPrimitive(arg, string).
  11. Assert: primitiveValue is not an Object.
  12. Return ? ToString(primitiveValue).
]

def AO_ToString : AOReg :=
  [("ToString", (["arg"], build toString7_1_19))]

#eval checkRun (renest toString7_1_19)