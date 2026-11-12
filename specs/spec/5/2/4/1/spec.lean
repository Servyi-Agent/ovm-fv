import metalanguage

/- ES 5.2.4.1 Completion ( completionRecord ) - the FIRST algorithm
   in the spec (chapters 1-5.2.3 carry no emu-alg). Text-equal, no
   deviations: bare `Return completionRecord.` returns the completion
   unchanged (kWrapIfBare: completion in → out as-is), and the step-1
   assert DISCHARGES — the completion-record split (testType meets
   the completion wire-shape family with the variable's type, here
   complN anyV from the signature) keeps the then-world and empties
   the false-world, so the verdict is forced to true. -/

def completion5_2_4_1 : List FStep := [alg|
  1. Assert: completionRecord is a Completion Record.
  2. Return completionRecord.
]

def AO_Completion : AOReg :=
  [("Completion", (["completionRecord"], build completion5_2_4_1))]

#eval checkRun (renest completion5_2_4_1)