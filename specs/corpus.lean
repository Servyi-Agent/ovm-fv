import metalanguage


/- ES 6.2.5.1 IsCallable ( x ) — text-equal transcription. -/

def isCallable6_2_5_1 : List FStep := [alg|
  1. If x is not an Object, return false.
  2. If x has a [[Call]] internal method, return true.
  3. Return false.
]

def AO_IsCallable : AOReg :=
  [("IsCallable", (["x"], build isCallable6_2_5_1))]

#eval checkRun (renest isCallable6_2_5_1)


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


def theReg : AOReg := AO_IsCallable ++ AO_ToPrimitive

/- smoke: every corpus program runs, audits, and SOS/machine agree -/
def exampleF : List FStep := [alg|
  1. If true, then
    ┊ a. Let x be 1.
  2. Return x.
]

def callDemoF : List FStep := [alg|
  1. Let c be IsCallable(true).
  2. Return c.
]

def retDemoF : List FStep := [alg|
  1. Let r be IsCallable(true).
  2. Return true.
]

def primDemoF : List FStep := [alg|
  1. Let p be ToPrimitive(undefined).
  2. Return p.
]

#eval ksteps theReg 50 (kmOf (build exampleF))
#eval ksteps theReg 100 (kmOf (build callDemoF))
#eval ksteps theReg 100 (kmOf (build retDemoF))
#eval ksteps theReg 100 (kmOf (build primDemoF))
#eval agree theReg (build exampleF)

