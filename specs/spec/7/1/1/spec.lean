import metalanguage

/- ES 7.1.1 ToPrimitive ( input [ , preferredType ] ) — text-equal
   transcription. Semantic stubs (documented in the metalanguage):
   GetMethod/OrdinaryToPrimitive/Call return undefined until the heap
   arrives; « preferredType » loses its list brackets (Lean lexes « »
   as identifier delimiters). -/

def toPrimitive7_1_1 : List FStep := [alg|
  1. If input is an Object, then
    ┊ a. Let exoticToPrim be ? GetMethod(input, @@toPrimitive).
    ┊ b. If exoticToPrim is not undefined, then
    ┊ ┊ i. Let result be ? Call(exoticToPrim, input, preferredType).
    ┊ ┊ ii. If result is an Object, throw a TypeError exception.
    ┊ ┊ iii. Return result.
    ┊ c. If preferredType is not present, set preferredType to number.
    ┊ d. Return ? OrdinaryToPrimitive(input, preferredType).
  2. Return input.
]

def AO_ToPrimitive : AOReg :=
  [("ToPrimitive", (["input", "preferredType"], build toPrimitive7_1_1))]

#eval checkRun (renest toPrimitive7_1_1)
