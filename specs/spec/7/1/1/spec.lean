import metalanguage

/- ES 7.1.1 ToPrimitive ( input [, preferredType ] ) - text-equal.
   GetMethod/OrdinaryToPrimitive/Call/GetV are primitive stubs until
   the heap. -/

def toPrimitive7_1_1 : List FStep := [alg|
  1. If input is an Object, then
    ┊ a. Let exoticToPrimitive be ? GetMethod(input, %Symbol.toPrimitive%).
    ┊ b. If exoticToPrimitive is not undefined, then
    ┊ ┊ i. If preferredType is not present, then
    ┊ ┊ ┊ 1. Let hint be "default".
    ┊ ┊ ii. Else if preferredType is ~string~, then
    ┊ ┊ ┊ 1. Let hint be "string".
    ┊ ┊ iii. Else,
    ┊ ┊ ┊ 1. Assert: preferredType is ~number~.
    ┊ ┊ ┊ 2. Let hint be "number".
    ┊ ┊ iv. Let result be ? Call(exoticToPrimitive, input, « hint »).
    ┊ ┊ v. If result is not an Object, return result.
    ┊ ┊ vi. Throw a TypeError exception.
    ┊ c. If preferredType is not present, set preferredType to ~number~.
    ┊ d. Return ? OrdinaryToPrimitive(input, preferredType).
  2. Return input.
]

def AO_ToPrimitive : AOReg :=
  [("ToPrimitive", (["input", "preferredType"], build toPrimitive7_1_1))]

#eval checkRun (renest toPrimitive7_1_1)
