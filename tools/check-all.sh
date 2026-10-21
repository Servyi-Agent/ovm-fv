#!/usr/bin/env bash
cd "$(dirname "$0")/.."
status=0
for check in specs/tools/check.sh verus/lookup-walk/check.sh; do
  echo "==== $check"
  if bash "$check"; then echo "PASS  $check"; else echo "FAIL  $check"; status=1; fi
done
exit $status
