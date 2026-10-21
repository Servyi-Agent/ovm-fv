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
  1: if true then
    ┊ a: let x be 1
  2: return x
]

def callDemoF : List FStep := [alg|
  1: let c be IsCallable(true)
  2: return c
]

def retDemoF : List FStep := [alg|
  1: let r be IsCallable(true)
  2: return true
]

def primDemoF : List FStep := [alg|
  1: let p be ToPrimitive(undefined)
  2: return p
]

#eval ksteps theReg 50 (kmOf (build exampleF))
#eval ksteps theReg 100 (kmOf (build callDemoF))
#eval ksteps theReg 100 (kmOf (build retDemoF))
#eval ksteps theReg 100 (kmOf (build primDemoF))
#eval agree theReg (build exampleF)
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
