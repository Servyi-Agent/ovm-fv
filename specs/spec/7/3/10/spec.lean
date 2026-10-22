import metalanguage

/- ES 7.3.10 GetMethod ( V, P ) - text-equal. GetV stubbed until the
   heap. Step 3 calls IsCallable (registry). -/

def getMethod7_3_10 : List FStep := [alg|
  1. Let func be ? GetV(value, propertyKey).
  2. If func is either undefined or null, return undefined.
  3. If IsCallable(func) is false, throw a TypeError exception.
  4. Return func.
]

def AO_GetMethod : AOReg :=
  [("GetMethod", (["value", "propertyKey"], build getMethod7_3_10))]

#eval checkRun (renest getMethod7_3_10)
