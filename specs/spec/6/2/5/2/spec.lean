import metalanguage

/- ES 6.2.5.2 IsConstructor ( argument ) - text-equal. -/

def isConstructor6_2_5_2 : List FStep := [alg|
  1. If arg is not an Object, return false.
  2. If arg has a [[Construct]] internal method, return true.
  3. Return false.
]

def AO_IsConstructor : AOReg :=
  [("IsConstructor", (["arg"], build isConstructor6_2_5_2))]

#eval checkRun (renest isConstructor6_2_5_2)
