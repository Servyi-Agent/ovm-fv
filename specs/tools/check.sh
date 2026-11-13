#!/usr/bin/env bash
set -e
cd "$(dirname "$0")/.."
# diff_spec audits against the live ECMA-262 single-page build; fetch
# it when the local copy is absent (CI has no /tmp carry-over)
SPEC_HTML=/tmp/opencode/spec/spec.html
if [ ! -s "$SPEC_HTML" ]; then
  echo "== fetching the live ECMA-262 draft for diff_spec"
  mkdir -p "$(dirname "$SPEC_HTML")"
  curl -sL https://tc39.es/ecma262/ -o "$SPEC_HTML"
fi
PATH="$HOME/.elan/bin:$PATH" lake build metalanguage

# ── THE PROOF GATE ──────────────────────────────────────────────
# 1) no sorry/admit anywhere in the sources (sorry is only a
#    WARNING to lake build; the gate makes it loud)
if grep -rn --include='*.lean' -E '\b(sorry|admit)\b' Metalanguage/ spec/ | grep -v '^tools/'; then
  echo "PROOF GATE: sorry/admit found (see above)"; exit 1
fi
# 2) every load-bearing theorem depends on nothing beyond Lean's
#    three standard axioms; a sorry in ANY listed proof would
#    surface as sorryAx here
AX=$(PATH="$HOME/.elan/bin:$PATH" lake env lean tools/axioms.lean)
echo "$AX"
# every axiom set must be a SUBSET of the standard three (fewer is fine)
BAD=$(echo "$AX" | grep "depends on axioms" | grep -vE "depends on axioms: \[\]?(propext|Classical\.choice|Quot\.sound)?(, (propext|Classical\.choice|Quot\.sound))*\]" || true)
if [ -n "$BAD" ]; then
  echo "PROOF GATE: non-standard axioms found:"; echo "$BAD"; exit 1
fi
if [ "$(echo "$AX" | wc -l)" -ne "$(grep -c '#print axioms' tools/axioms.lean)" ]; then
  echo "PROOF GATE: axiom report incomplete (missing theorems?)"; exit 1
fi

for f in $(find spec -name 'spec.lean' | sort); do
  echo "== $f"
  PATH="$HOME/.elan/bin:$PATH" lake env lean "$f"
done
python3 tools/build_corpus.py
echo "== diff_spec (text equality)"
python3 tools/diff_spec.py
echo "== corpus.lean"
PATH="$HOME/.elan/bin:$PATH" lake env lean corpus.lean
echo "ALL CHECKS PASSED"