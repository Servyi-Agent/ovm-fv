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
