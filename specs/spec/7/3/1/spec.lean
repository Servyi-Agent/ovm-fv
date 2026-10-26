import metalanguage

/- ES 7.3.1 GetV ( V, P ) - text-equal. -/

def getV7_3_1 : List FStep := [alg|
  1. Let obj be ? ToObject(value).
  2. Return ? obj.[[Get]](propertyKey, value).
]

def AO_GetV : AOReg :=
  [("GetV", (["value", "propertyKey"], build getV7_3_1))]

#eval checkRun (renest getV7_3_1)
