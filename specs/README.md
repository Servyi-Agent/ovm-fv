# specs/

ECMA-262 transcribed into a verifiable, executable metalanguage (Lean 4),
toward a simulation proof against the [ovm](https://github.com/anomalyco/ovm)
JavaScript engine.

## Layout

- `metalanguage.lean` — the whole emu-alg metalanguage:
  - surface grammar (spec numbering + `┊` depth markers, `If`/`Else`,
    `Let`/`Return`/`Set`/`Assert:`/`Throw`, `For each`, is-family
    predicates, MOP calls `o.[[M]](args)` and field reads `o.[[F]]`,
    `« lists »`, `%Intrinsics%`),
  - label-carrying elaboration + the numbering audit (`checkRun`),
  - three semantics kept in agreement: big-step, SOS, and the FM frame
    machine (per-frame env + eval stack; `kEval` decomposes expressions
    at runtime; registry-driven calls),
  - the heap (`Nat → Option JsObj`, monotonic `nextLoc`),
  - a **static typechecker** for compiled instruction sequences:
    completion-protocol discipline + value refinement
    (`number/boolean/str/obj/list/descV` under `any`), driven by a
    signature table; rejections carry the instruction, reason, and
    abstract stack.
- `spec/<clause>/spec.lean` — one file per spec clause:
  `spec/6/2/5/1/spec.lean` defines 6.2.5.1 `IsCallable`. Each is
  standalone-checkable and contributes an `AO_<Name> : AOReg` registry
  entry. Current corpus (10, all text-equal):
  IsCallable, IsConstructor, IsDataDescriptor, IsAccessorDescriptor,
  ToPrimitive, OrdinaryToPrimitive, ToObject, GetV, OrdinaryGet,
  GetMethod.
- `tools/diff_spec.py` — **text-equality audit**: char-compares every
  transcription against the spec's `emu-alg` (whitespace/`┊` stripped,
  canonical markers; documented deviations).
- `tools/build_corpus.py` — numeric directories cannot be Lean module
  names, so the corpus/registry is assembled by concatenation into
  `corpus.lean` (gitignored, regenerated), including the smoke suite
  (end-to-end lookup chain, loops, negative typing tests).
- `tools/check.sh` — everything: library, each spec file, text
  equality, corpus + smoke + typing.

## Conventions

- Transcriptions aim for obvious 1:1 correspondence with the spec
  text; deviations are documented in `diff_spec.py`'s DEVIATIONS table.
- Completions are values (`compl abrupt v`); delivery is always a
  completion, signatures type the payload.
- Everything that can go wrong goes wrong loudly: unknown operations
  stick, non-Boolean conditions stick, the numbering audit rejects
  non-consecutive labels. Terminal states retain the full machine
  state and count absorbing steps (`step (done k n) = done k (1+n)`).
- Bedrock (the spec's mathematical notation) is a small, explicit
  primitive inventory; everything above it is transcribed steps.

## Check

    ./tools/check.sh   # from this directory
