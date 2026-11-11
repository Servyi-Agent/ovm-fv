import metalanguage

/- ES 7.2.1 RequireObjectCoercible ( arg ) - text-equal. One
   deviation: the spec's `Return unused.` — no `unused` value in this
   universe; modeled as undefined (the result is never observable,
   only the throw matters). -/

def requireObjectCoercible7_2_1 : List FStep := [alg|
  1. If arg is either undefined or null, throw a TypeError exception.
  2. Return undefined.
]

def AO_RequireObjectCoercible : AOReg :=
  [("RequireObjectCoercible", (["arg"], build requireObjectCoercible7_2_1))]

#eval checkRun (renest requireObjectCoercible7_2_1)