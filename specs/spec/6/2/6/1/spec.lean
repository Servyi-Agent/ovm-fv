import metalanguage

/- ES 6.2.6.1 IsAccessorDescriptor ( propertyDesc ) - text-equal.
   (Renumbered: this clause was first filed under 6/2/6/3, which in
   this draft is IsGenericDescriptor's slot.) -/

def isAccessorDescriptor6_2_6_1 : List FStep := [alg|
  1. If propertyDesc has a [[Getter]] field, return true.
  2. If propertyDesc has a [[Setter]] field, return true.
  3. Return false.
]

def AO_IsAccessorDescriptor : AOReg :=
  [("IsAccessorDescriptor", (["propertyDesc"], build isAccessorDescriptor6_2_6_1))]

#eval checkRun (renest isAccessorDescriptor6_2_6_1)