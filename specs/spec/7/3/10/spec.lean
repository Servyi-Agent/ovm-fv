import metalanguage

/- ES 7.3.10 GetMethod ( V, P ) — text-equal transcription. The first
   registry entry that CALLS another registry entry (step 3: IsCallable).
   GetV is a stub primitive until the heap. -/

def getMethod7_3_10 : List FStep := [alg|
  1. Let func be ? GetV(V, P).
  2. If func is undefined, return undefined.
  3. If IsCallable(func) is false, throw a TypeError exception.
  4. Return func.
]

def AO_GetMethod : AOReg :=
  [("GetMethod", (["V", "P"], build getMethod7_3_10))]

#eval checkRun (renest getMethod7_3_10)
