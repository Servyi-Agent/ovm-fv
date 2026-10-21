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


/- ES 6.2.5.2 IsConstructor ( x ) — text-equal transcription. -/

def isConstructor6_2_5_2 : List FStep := [alg|
  1. If x is not an Object, return false.
  2. If x has a [[Construct]] internal method, return true.
  3. Return false.
]

def AO_IsConstructor : AOReg :=
  [("IsConstructor", (["x"], build isConstructor6_2_5_2))]

#eval checkRun (renest isConstructor6_2_5_2)


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


/- ES 7.3.10 GetMethod ( V, P ) — text-equal transcription. The first
   registry entry that CALLS another registry entry (step 3: IsCallable).
   GetV is a stub primitive until the heap. -/

def getMethod7_3_10 : List FStep := [alg|
  1. Let func be ? GetV(V, P).
  2. If func is undefined, return undefined.
  3. If IsCallable(func) is false, throw a TypeError exception.
  4. Return func.
]

def AO_GetMethod : AOReg :=
  [("GetMethod", (["V", "P"], build getMethod7_3_10))]

#eval checkRun (renest getMethod7_3_10)


def theReg : AOReg := AO_IsCallable ++ AO_IsConstructor ++ AO_ToPrimitive ++ AO_GetMethod

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
#eval ksteps theReg 100 (kmOf (build getMethod7_3_10))
#eval ksteps theReg 100 (kmOf (build isConstructor6_2_5_2))
#eval agree theReg (build exampleF)

