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
