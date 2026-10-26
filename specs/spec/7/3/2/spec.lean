import metalanguage

/- ES 7.3.2 OrdinaryToPrimitive... no: OrdinaryGet ( O, P, Receiver ) - text-equal.
   One deviation: _obj_.[[GetPrototypeOf]]() is zero-arg, which the
   grammar cannot pattern-match (empty parens); written in field-read
   form — the machine treats the field name as the zero-arg MOP call. -/

def ordinaryGet7_3_2 : List FStep := [alg|
  1. Let propertyDesc be ? obj.[[GetOwnProperty]](propertyKey).
  2. If propertyDesc is undefined, then
    ┊ a. Let parent be ? obj.[[GetPrototypeOf]].
    ┊ b. If parent is null, return undefined.
    ┊ c. Return ? parent.[[Get]](propertyKey, receiver).
  3. If IsDataDescriptor(propertyDesc) is true, return propertyDesc.[[Value]].
  4. Assert: IsAccessorDescriptor(propertyDesc) is true.
  5. Let getter be propertyDesc.[[Getter]].
  6. If getter is undefined, return undefined.
  7. Return ? Call(getter, receiver).
]

def AO_OrdinaryGet : AOReg :=
  [("OrdinaryGet", (["obj", "propertyKey", "receiver"], build ordinaryGet7_3_2))]

#eval checkRun (renest ordinaryGet7_3_2)
