import metalanguage

/- ES 6.2.5.2 IsConstructor ( x ) — text-equal transcription. -/

def isConstructor6_2_5_2 : List FStep := [alg|
  1. If x is not an Object, return false.
  2. If x has a [[Construct]] internal method, return true.
  3. Return false.
]

def AO_IsConstructor : AOReg :=
  [("IsConstructor", (["x"], build isConstructor6_2_5_2))]

#eval checkRun (renest isConstructor6_2_5_2)
