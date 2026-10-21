import metalanguage

/- ES 7.1.1 ToPrimitive ( input [ , preferredType ] )
   preferredType is optional in the spec; modelled as a parameter
   (unbound when the call site omits it — "not present" support
   pending). GetMethod/OrdinaryToPrimitive are primitive stubs until
   the heap arrives. -/

def toPrimitive7_1_1 : List FStep := [alg|
  1: if input is an Object then
    ┊ a: let exoticToPrim be ? GetMethod(input, toPrimitive)
    ┊ b: if exoticToPrim is not undefined then
    ┊ ┊ i: return exoticToPrim
    ┊ c: let r2 be ? OrdinaryToPrimitive(input, preferredType)
    ┊ d: return r2
  2: return input
]

def AO_ToPrimitive : AOReg :=
  [("ToPrimitive", (["input", "preferredType"], build toPrimitive7_1_1))]

#eval checkRun (renest toPrimitive7_1_1)
