import metalanguage

/- ES 7.2.4 IsConstructor ( arg ) - text-equal.
   Renumbered from 6/2/5/2 (this draft's coordinates). -/

def isConstructor7_2_4 : List FStep := [alg|
  1. If arg is not an Object, return false.
  2. If arg has a [[Construct]] internal method, return true.
  3. Return false.
]

def AO_IsConstructor : AOReg :=
  [("IsConstructor", (["arg"], build isConstructor7_2_4))]

#eval checkRun (renest isConstructor7_2_4)