# specs/

ECMA-262 transcribed into a verifiable, executable metalanguage (Lean 4),
toward a simulation proof against the [ovm](https://github.com/anomalyco/ovm)
JavaScript engine.

## Layout

- `metalanguage.lean` — the whole emu-alg metalanguage: surface grammar
  (`┊` depth markers + spec numbering), label-carrying elaboration, the
  numbering audit, SOS semantics, and the kEval small-step machine
  (frames for control boundaries, registry-driven calls).
- `spec/<clause>/spec.lean` — one file per spec clause: `spec/6/2/5/1/spec.lean`
  defines 6.2.5.1 `IsCallable`. Each is standalone-checkable and contributes
  an `AO_<Name> : AOReg` registry entry.
- `tools/build_corpus.py` — numeric directories cannot be Lean module names,
  so the corpus/registry is assembled by concatenation into `corpus.lean`
  (the script prints the chunk order; error positions are corpus-relative).
- `tools/check.sh` — everything: library, each spec file, corpus + smoke.

## Conventions

- Transcriptions aim for obvious 1:1 correspondence with the spec text;
  deviations are commented at the site.
- Everything that can go wrong goes wrong loudly: dangling else markers
  survive in the AST, unknown operations stick, non-Boolean conditions stick,
  the numbering audit (`checkRun`) rejects non-consecutive labels.
- Bedrock (the spec's mathematical notation) is a small, explicit primitive
  inventory; everything above it is transcribed steps.

## Check

    ./tools/check.sh   # from this directory
