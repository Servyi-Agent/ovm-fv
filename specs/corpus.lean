import metalanguage


/- ES 6.2.5.1 IsCallable ( argument ) -  text-equal (tools/diff_spec.py). -/

def isCallable6_2_5_1 : List FStep := [alg|
  1. If arg is not an Object, return false.
  2. If arg has a [[Call]] internal method, return true.
  3. Return false.
]

def AO_IsCallable : AOReg :=
  [("IsCallable", (["arg"], build isCallable6_2_5_1))]

#eval checkRun (renest isCallable6_2_5_1)


/- ES 6.2.5.2 IsConstructor ( argument ) - text-equal. -/

def isConstructor6_2_5_2 : List FStep := [alg|
  1. If arg is not an Object, return false.
  2. If arg has a [[Construct]] internal method, return true.
  3. Return false.
]

def AO_IsConstructor : AOReg :=
  [("IsConstructor", (["arg"], build isConstructor6_2_5_2))]

#eval checkRun (renest isConstructor6_2_5_2)


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


/- ES 7.3.10 GetMethod ( V, P ) - text-equal. GetV stubbed until the
   heap. Step 3 calls IsCallable (registry). -/

def getMethod7_3_10 : List FStep := [alg|
  1. Let func be ? GetV(value, propertyKey).
  2. If func is either undefined or null, return undefined.
  3. If IsCallable(func) is false, throw a TypeError exception.
  4. Return func.
]

def AO_GetMethod : AOReg :=
  [("GetMethod", (["value", "propertyKey"], build getMethod7_3_10))]

#eval checkRun (renest getMethod7_3_10)


def theReg : AOReg := AO_IsCallable ++ AO_IsConstructor ++ AO_OrdinaryToPrimitive ++ AO_ToPrimitive ++ AO_GetMethod

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

/- For each over a spec List: iterate to the 2nd element, return through
   the loop (the pending kLoopS marker is discarded by the return). -/
def forEachDemoF : List FStep := [alg|
  1. Let xs be « "a", "b" ».
  2. For each element x of xs, do
    ┊ a. If x is ~b~, Return x.
  3. Return undefined.
]

#eval ksteps theReg 100 (kmOf (build forEachDemoF))
#eval ksteps theReg 100 (kmOf (build ordinaryToPrimitive7_1_1_1))
#eval agree theReg (build exampleF)

