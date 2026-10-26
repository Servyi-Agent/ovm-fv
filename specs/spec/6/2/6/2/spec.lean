import metalanguage

/- ES 6.2.6.2 IsDataDescriptor ( Desc ) - text-equal. -/

def isDataDescriptor6_2_6_2 : List FStep := [alg|
  1. If propertyDesc has a [[Value]] field, return true.
  2. If propertyDesc has a [[Writable]] field, return true.
  3. Return false.
]

def AO_IsDataDescriptor : AOReg :=
  [("IsDataDescriptor", (["propertyDesc"], build isDataDescriptor6_2_6_2))]

#eval checkRun (renest isDataDescriptor6_2_6_2)
