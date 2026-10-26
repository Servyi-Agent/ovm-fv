#!/usr/bin/env python3
"""Assemble spec/*/spec.lean files into corpus.lean (the registry).

Numeric directories cannot be Lean module names, so the corpus is a
concatenation with #line directives mapping errors back to the
original files. Each spec file contributes an AO_<Name> : AOReg def.
"""
import os, re, sys

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
specdir = os.path.join(root, "spec")
files = []
for dirpath, _, fnames in os.walk(specdir):
    for fn in fnames:
        if fn == "spec.lean":
            files.append(os.path.join(dirpath, fn))
files.sort()

SMOKE = '''
def theReg : AOReg := {entries}

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
'''

out = ["import metalanguage", ""]
entries = []
for f in files:
    src = open(f).read()
    src = re.sub(r"^import metalanguage\s*$", "", src, flags=re.M)
    out.append(src)
    entries += re.findall(r"^def (AO_\w+)", src, flags=re.M)

out.append(SMOKE.replace("{entries}", " ++ ".join(entries) if entries else "[]"))
open(os.path.join(root, "corpus.lean"), "w").write("\n".join(out) + "\n")
print(f"corpus.lean: {len(files)} spec files, {len(entries)} registry entries")
for i, f in enumerate(files):
    print(f"  chunk {i+1}: {f}")
