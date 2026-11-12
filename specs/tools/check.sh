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