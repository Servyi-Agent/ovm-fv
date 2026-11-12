import metalanguage

/- ES 7.1.21 ToPropertyKey ( arg ) - text-equal. `Return !` is the
   abruptness-asserted return (elaborates like ?; the never-abrupt
   claim is a proof obligation). No Symbol values exist in this
   universe, so step 2's then-branch is statically dead and the
   declared return type is cStr-only. -/

def toPropertyKey7_1_21 : List FStep := [alg|
  1. Let key be ? ToPrimitive(arg, string).
  2. If key is a Symbol, then
    ┊ a. Return key.
  3. Return ! ToString(key).
]

def AO_ToPropertyKey : AOReg :=
  [("ToPropertyKey", (["arg"], build toPropertyKey7_1_21))]

#eval checkRun (renest toPropertyKey7_1_21)