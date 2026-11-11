import metalanguage

/- ES 7.3.3 GetV ( V, P ) - text-equal.
   Renumbered from 7/3/1 (this draft's coordinates). -/

def getV7_3_3 : List FStep := [alg|
  1. Let obj be ? ToObject(value).
  2. Return ? obj.[[Get]](propertyKey, value).
]

def AO_GetV : AOReg :=
  [("GetV", (["value", "propertyKey"], build getV7_3_3))]

#eval checkRun (renest getV7_3_3)