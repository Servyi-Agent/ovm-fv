import metalanguage

/- ES 6.2.6.3 IsGenericDescriptor ( propertyDesc ) - text-equal.
   Both calls are registry entries; the `is true` correlated
   predicate tests split exact desc atoms and duplicate coarse ones
   (splitWorldsP machinery, exercised here by a registry body for the
   first time). -/

def isGenericDescriptor6_2_6_3 : List FStep := [alg|
  1. If IsAccessorDescriptor(propertyDesc) is true, return false.
  2. If IsDataDescriptor(propertyDesc) is true, return false.
  3. Return true.
]

def AO_IsGenericDescriptor : AOReg :=
  [("IsGenericDescriptor", (["propertyDesc"], build isGenericDescriptor6_2_6_3))]

#eval checkRun (renest isGenericDescriptor6_2_6_3)