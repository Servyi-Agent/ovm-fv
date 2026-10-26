import metalanguage


/- ES 6.2.5.1 IsCallable ( argument ) -  text-equal (tools/diff_spec.py). -/

def isCallable6_2_5_1 : List FStep := [alg|
  1. If arg is not an Object, return false.
  2. If arg has a [[Call]] internal method, return true.
  3. Return false.
]

def AO_IsCallable : AOReg :=
  [("IsCallable", (["arg"], build isCallable6_2_5_1))]

#eval checkRun (renest isCallable6_2_5_1)


/- ES 6.2.5.2 IsConstructor ( argument ) - text-equal. -/

def isConstructor6_2_5_2 : List FStep := [alg|
  1. If arg is not an Object, return false.
  2. If arg has a [[Construct]] internal method, return true.
  3. Return false.
]

def AO_IsConstructor : AOReg :=
  [("IsConstructor", (["arg"], build isConstructor6_2_5_2))]

#eval checkRun (renest isConstructor6_2_5_2)


/- ES 6.2.6.2 IsDataDescriptor ( Desc ) - text-equal. -/

def isDataDescriptor6_2_6_2 : List FStep := [alg|
  1. If propertyDesc has a [[Value]] field, return true.
  2. If propertyDesc has a [[Writable]] field, return true.
  3. Return false.
]

def AO_IsDataDescriptor : AOReg :=
  [("IsDataDescriptor", (["propertyDesc"], build isDataDescriptor6_2_6_2))]

#eval checkRun (renest isDataDescriptor6_2_6_2)


/- ES 6.2.6.3 IsAccessorDescriptor ( Desc ) - text-equal. -/

def isAccessorDescriptor6_2_6_3 : List FStep := [alg|
  1. If propertyDesc has a [[Getter]] field, return true.
  2. If propertyDesc has a [[Setter]] field, return true.
  3. Return false.
]

def AO_IsAccessorDescriptor : AOReg :=
  [("IsAccessorDescriptor", (["propertyDesc"], build isAccessorDescriptor6_2_6_3))]

#eval checkRun (renest isAccessorDescriptor6_2_6_3)


/- ES 7.1.1.1 OrdinaryToPrimitive ( O, hint ) - text-equal. Get and
   Call are stubs until the heap; For each iterates a spec List. -/

def ordinaryToPrimitive7_1_1_1 : List FStep := [alg|
  1. If hint is ~string~, then
    ┊ a. Let methodNames be « "toString", "valueOf" ».
  2. Else,
    ┊ a. Let methodNames be « "valueOf", "toString" ».
  3. For each element name of methodNames, do
    ┊ a. Let method be ? Get(obj, name).
    ┊ b. If IsCallable(method) is true, then
    ┊ ┊ i. Let result be ? Call(method, obj).
    ┊ ┊ ii. If result is not an Object, return result.
  4. Throw a TypeError exception.
]

def AO_OrdinaryToPrimitive : AOReg :=
  [("OrdinaryToPrimitive", (["obj", "hint"], build ordinaryToPrimitive7_1_1_1))]

#eval checkRun (renest ordinaryToPrimitive7_1_1_1)


/- ES 7.1.1 ToPrimitive ( input [, preferredType ] ) - text-equal.
   GetMethod/OrdinaryToPrimitive/Call/GetV are primitive stubs until
   the heap. -/

def toPrimitive7_1_1 : List FStep := [alg|
  1. If input is an Object, then
    ┊ a. Let exoticToPrimitive be ? GetMethod(input, %Symbol.toPrimitive%).
    ┊ b. If exoticToPrimitive is not undefined, then
    ┊ ┊ i. If preferredType is not present, then
    ┊ ┊ ┊ 1. Let hint be "default".
    ┊ ┊ ii. Else if preferredType is ~string~, then
    ┊ ┊ ┊ 1. Let hint be "string".
    ┊ ┊ iii. Else,
    ┊ ┊ ┊ 1. Assert: preferredType is ~number~.
    ┊ ┊ ┊ 2. Let hint be "number".
    ┊ ┊ iv. Let result be ? Call(exoticToPrimitive, input, « hint »).
    ┊ ┊ v. If result is not an Object, return result.
    ┊ ┊ vi. Throw a TypeError exception.
    ┊ c. If preferredType is not present, set preferredType to ~number~.
    ┊ d. Return ? OrdinaryToPrimitive(input, preferredType).
  2. Return input.
]

def AO_ToPrimitive : AOReg :=
  [("ToPrimitive", (["input", "preferredType"], build toPrimitive7_1_1))]

#eval checkRun (renest toPrimitive7_1_1)


/- ES 7.1.13 ToObject ( argument ) - text-equal. -/

def toObject7_1_13 : List FStep := [alg|
  1. If arg is either undefined or null, throw a TypeError exception.
  2. If arg is a Boolean, return a new Boolean object whose [[BooleanData]] internal slot is set to arg.
  3. If arg is a Number, return a new Number object whose [[NumberData]] internal slot is set to arg.
  4. If arg is a String, return a new String object whose [[StringData]] internal slot is set to arg.
  5. If arg is a Symbol, return a new Symbol object whose [[SymbolData]] internal slot is set to arg.
  6. If arg is a BigInt, return a new BigInt object whose [[BigIntData]] internal slot is set to arg.
  7. Assert: arg is an Object.
  8. Return arg.
]

def AO_ToObject : AOReg :=
  [("ToObject", (["arg"], build toObject7_1_13))]

#eval checkRun (renest toObject7_1_13)


/- ES 7.3.1 GetV ( V, P ) - text-equal. -/

def getV7_3_1 : List FStep := [alg|
  1. Let obj be ? ToObject(value).
  2. Return ? obj.[[Get]](propertyKey, value).
]

def AO_GetV : AOReg :=
  [("GetV", (["value", "propertyKey"], build getV7_3_1))]

#eval checkRun (renest getV7_3_1)


/- ES 7.3.10 GetMethod ( V, P ) - text-equal. GetV stubbed until the
   heap. Step 3 calls IsCallable (registry). -/

def getMethod7_3_10 : List FStep := [alg|
  1. Let func be ? GetV(value, propertyKey).
  2. If func is either undefined or null, return undefined.
  3. If IsCallable(func) is false, throw a TypeError exception.
  4. Return func.
]

def AO_GetMethod : AOReg :=
  [("GetMethod", (["value", "propertyKey"], build getMethod7_3_10))]

#eval checkRun (renest getMethod7_3_10)


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


def theReg : AOReg := AO_IsCallable ++ AO_IsConstructor ++ AO_IsDataDescriptor ++ AO_IsAccessorDescriptor ++ AO_OrdinaryToPrimitive ++ AO_ToPrimitive ++ AO_ToObject ++ AO_GetV ++ AO_GetMethod ++ AO_OrdinaryGet

/- smoke: every corpus program runs, audits, and SOS/machine agree -/
def exampleF : List FStep := [alg|
  1. If true, then
    ┊ a. Let x be 1.
  2. Return x.
]

def callDemoF : List FStep := [alg|
  1. Let c be IsCallable(true).
  2. Return c.
]

def retDemoF : List FStep := [alg|
  1. Let r be IsCallable(true).
  2. Return true.
]

def primDemoF : List FStep := [alg|
  1. Let p be ToPrimitive(undefined).
  2. Return p.
]

#eval ksteps theReg 50 (kmOf (build exampleF))
#eval ksteps theReg 100 (kmOf (build callDemoF))
#eval ksteps theReg 100 (kmOf (build retDemoF))
#eval ksteps theReg 100 (kmOf (build primDemoF))
#eval ksteps theReg 100 (kmOf (build getMethod7_3_10))
#eval ksteps theReg 100 (kmOf (build isConstructor6_2_5_2))

/- For each over a spec List: iterate to the 2nd element, return through
   the loop (the pending kLoopS marker is discarded by the return). -/
def forEachDemoF : List FStep := [alg|
  1. Let xs be « "a", "b" ».
  2. For each element x of xs, do
    ┊ a. If x is ~b~, Return x.
  3. Return undefined.
]

#eval ksteps theReg 100 (kmOf (build forEachDemoF))
#eval ksteps theReg 100 (kmOf (build ordinaryToPrimitive7_1_1_1))

/- A real two-argument call: OrdinaryToPrimitive(undefined, ~string~) enters
   the registry with both params bound; the loop iterates over both
   method names; stubbed Get -> undefined -> IsCallable false; the
   loop exhausts; step 4 throws. -/
def otpDemoF : List FStep := [alg|
  1. Let r be OrdinaryToPrimitive(undefined, ~string~).
  2. Return r.
]

#eval checkRun (renest otpDemoF)
#eval ksteps theReg 200 (kmOf (build otpDemoF))

/- Omission: fewer args than params — preferredType stays unbound,
   the not-present defaulting path runs (already shown by primDemoF). -/
def omitDemoF : List FStep := [alg|
  1. Let q be ToPrimitive(undefined).
  2. Return q.
]
#eval ksteps theReg 100 (kmOf (build omitDemoF))
#eval agree2 theReg (build exampleF)

/- Frame machine on the same corpus -/
#eval fsteps theReg 100 (fmOf (build exampleF))
#eval fsteps theReg 100 (fmOf (build callDemoF))
#eval fsteps theReg 100 (fmOf (build retDemoF))
#eval fsteps theReg 100 (fmOf (build primDemoF))
#eval fsteps theReg 100 (fmOf (build forEachDemoF))
/- otpDemoF: 2-arg call, loop over both names, Throw at step 4 —
   the throw is now a VALUE: pThrowC + kRet returns the completion
   through the call, the self-test at the call site propagates it -/
#eval fsteps theReg 300 (fmOf (build otpDemoF))
#eval agree2 theReg (build exampleF)
#eval agree2 theReg (build forEachDemoF)

/- original KM agreement -/
#eval agree theReg (build exampleF)

/- The full lookup chain, live: GetV -> ToObject -> OrdinaryGet ->
   native MOP. A heap object with own property "x" = 42,
   reached via propertyKey "x". -/
def lookupDemoF : List FStep := [alg|
  1. Let m be GetV(input, propertyKey).
  2. Return m.
]

/- GetMethod on a non-callable, non-undefined value: spec says
   step 4 throws a TypeError (compl true undefined). -/
def getMethodDemoF : List FStep := [alg|
  1. Let m be GetMethod(input, propertyKey).
  2. Return m.
]

def demoHeap : Heap :=
  heapSet emptyHeap 0 {
    (objWith .ordinary none) with
      props := [(PKey.str "x",
        Descriptor.mk (some (JSValue.number 42)) (some Bool.true)
          none none (some Bool.true) (some Bool.true))] }

#eval checkRun (renest lookupDemoF)
#eval fsteps theReg
    1000 (.frames [⟨compileSteps (build lookupDemoF),
        [("input", .obj 0), ("propertyKey", .str "x")], []⟩] demoHeap 1)
#eval fsteps theReg
    1000 (.frames [⟨compileSteps (build getMethodDemoF),
        [("input", .obj 0), ("propertyKey", .str "x")], []⟩] demoHeap 1)

