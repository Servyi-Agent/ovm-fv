import metalanguage


/- ES 6.2.5.1 IsCallable ( x )
   1. If x is not an Object, return false.
   2. If x has a [[Call]] internal method, return true.
   3. Return false.
   (Grammar note: "has a [[Call]]" loses its article — `a` collides
   with the ┊-depth label.) -/

def isCallable6_2_5_1 : List FStep := [alg|
  1: if x is not an Object then
    ┊ a: return false
  2: if x has [[Call]] internal method then
    ┊ a: return true
  3: return false
]

def AO_IsCallable : AOReg :=
  [("IsCallable", (["x"], build isCallable6_2_5_1))]

#eval checkRun (renest isCallable6_2_5_1)


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


def theReg : AOReg := AO_IsCallable ++ AO_ToPrimitive

/- smoke: every corpus program runs, audits, and SOS/machine agree -/
def exampleF : List FStep := [alg|
  1: if true then
    ┊ a: let x be 1
  2: return x
]

def callDemoF : List FStep := [alg|
  1: let c be IsCallable(true)
  2: return c
]

def retDemoF : List FStep := [alg|
  1: let r be IsCallable(true)
  2: return true
]

def primDemoF : List FStep := [alg|
  1: let p be ToPrimitive(undefined)
  2: return p
]

#eval ksteps theReg 50 (kmOf (build exampleF))
#eval ksteps theReg 100 (kmOf (build callDemoF))
#eval ksteps theReg 100 (kmOf (build retDemoF))
#eval ksteps theReg 100 (kmOf (build primDemoF))
#eval agree theReg (build exampleF)

