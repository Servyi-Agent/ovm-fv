#!/usr/bin/env bash
set -e
cd "$(dirname "$0")/.."
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
