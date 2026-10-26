import metalanguage

/- ES 6.2.6.3 IsAccessorDescriptor ( Desc ) - text-equal. -/

def isAccessorDescriptor6_2_6_3 : List FStep := [alg|
  1. If propertyDesc has a [[Getter]] field, return true.
  2. If propertyDesc has a [[Setter]] field, return true.
  3. Return false.
]

def AO_IsAccessorDescriptor : AOReg :=
  [("IsAccessorDescriptor", (["propertyDesc"], build isAccessorDescriptor6_2_6_3))]

#eval checkRun (renest isAccessorDescriptor6_2_6_3)
