import metalanguage

/- ES 10.1.8.1 OrdinaryGet ( O, P, Receiver ) - text-equal, no
   deviations: `obj.[[GetPrototypeOf]]()` now parses (zero-arg MOP
   call production), and the call form makes the machine actually
   dispatch the zero-arg MOP — the old field-read workaround returned
   undefined at runtime on the proto-chain path.
   Renumbered from 7/3/2 (this draft's coordinates). -/

def ordinaryGet10_1_8_1 : List FStep := [alg|
  1. Let propertyDesc be ? obj.[[GetOwnProperty]](propertyKey).
  2. If propertyDesc is undefined, then
    ┊ a. Let parent be ? obj.[[GetPrototypeOf]]().
    ┊ b. If parent is null, return undefined.
    ┊ c. Return ? parent.[[Get]](propertyKey, receiver).
  3. If IsDataDescriptor(propertyDesc) is true, return propertyDesc.[[Value]].
  4. Assert: IsAccessorDescriptor(propertyDesc) is true.
  5. Let getter be propertyDesc.[[Getter]].
  6. If getter is undefined, return undefined.
  7. Return ? Call(getter, receiver).
]

def AO_OrdinaryGet : AOReg :=
  [("OrdinaryGet", (["obj", "propertyKey", "receiver"], build ordinaryGet10_1_8_1))]

#eval checkRun (renest ordinaryGet10_1_8_1)