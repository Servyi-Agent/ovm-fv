import metalanguage

/- ES 7.3.2 Get ( obj, propertyKey ) - text-equal
   (tools/diff_spec.py). The one-step MOP wrapper: the registry-backed
   body replaces the old native stub. -/

def get7_3_2 : List FStep := [alg|
  1. Return ? obj.[[Get]](propertyKey, obj).
]

def AO_Get : AOReg :=
  [("Get", (["obj", "propertyKey"], build get7_3_2))]

#eval checkRun (renest get7_3_2)
