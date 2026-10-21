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
