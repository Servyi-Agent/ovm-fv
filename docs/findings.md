# Findings

Divergences between ovm and ECMA-262 found by the formal models
(Verus property-walk proof; Lean ES-lookup/Add models). Full details,
repros, and conformance tests live in the ovm issue tracker.

| # | divergence | model |
|---|---|---|
| #1 | mid-chain array length not updated | lookup |
| #2 | key spelling: -1 vs "-1" | lookup |
| #3 | mid-chain primitive wrapper | lookup |
| #7 | mid-chain proxy | lookup |
| #8 | literal `__proto__` no-op | lookup |
| #9 | `__proto__` setter no-op | lookup |
| #10 | `Object.create(wrapper)` throws | lookup |
| #15 | `ToString(-0)` = "-0" | arith |
| #16 | Smi 2^53+1 exactness | Add (proved from A1+A3) |

PRs #4-#6, #11-#14 add conformance tests. The lookup findings are
proved divergences (see verus/lookup-walk), not just observations.
