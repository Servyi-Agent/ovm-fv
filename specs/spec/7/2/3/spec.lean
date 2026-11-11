import metalanguage

/- ES 7.2.3 IsCallable ( arg ) -  text-equal (tools/diff_spec.py).
   Renumbered from 6/2/5/1 (this draft's coordinates). -/

def isCallable7_2_3 : List FStep := [alg|
  1. If arg is not an Object, return false.
  2. If arg has a [[Call]] internal method, return true.
  3. Return false.
]

def AO_IsCallable : AOReg :=
  [("IsCallable", (["arg"], build isCallable7_2_3))]

#eval checkRun (renest isCallable7_2_3)