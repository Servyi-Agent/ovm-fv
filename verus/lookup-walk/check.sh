#!/usr/bin/env bash
# Verus projects are NOT cargo projects: verus drives rustc itself.
# Locate the verus binary via $VERUS, PATH, or the known local dist.
set -e
cd "$(dirname "$0")"
export PATH="$HOME/.cargo/bin:$PATH"
if [ -z "$VERUS" ]; then
  if command -v verus >/dev/null; then VERUS=verus
  elif [ -x /tmp/opencode/verus-dist/verus-x86-linux/verus ]; then
    VERUS=/tmp/opencode/verus-dist/verus-x86-linux/verus
  else
    echo "verus not found; set VERUS=<path>" >&2; exit 1
  fi
fi
"$VERUS" --crate-type=lib lib.rs
echo "LOOKUP-WALK VERIFIED"
