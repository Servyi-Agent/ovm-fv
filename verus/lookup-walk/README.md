# ovm property walk — ECMA-262 simulation proof (Verus)

A machine-checked proof that ovm's named property walk
(`vm_core/src/lookup.rs`) computes exactly what ECMA-262 *OrdinaryGet*
(10.1.8.1) computes, via a recursive simulation relation between an
abstract JavaScript object and a faithful model of ovm's object
representation.

## How to run

```sh
# Verus 0.2026.10.04 (any recent release; z3 bundled)
verus --crate-type=lib lib.rs
# verification results:: 15 verified, 0 errors
```

## The three layers

1. **The ECMA side** (`JsHeap`, `JsObject`, `PDesc`): an ordinary JS
   object is exactly `[[Prototype]]` plus an own-property map with
   complete `PropertyDescriptor`s (ES 6.2.6). `ogop` is OrdinaryGetOwn
   Property (10.1.5.1); `oget_rec` is OrdinaryGet (10.1.8.1), with an
   explicit recursion budget standing in for the spec's implicit
   prototype-chain acyclicity.

2. **The code side** (`CHeap`, `CObj`, `CMap`, `CDescr`): mirrors ovm's
   representation one-for-one — maps with ordered descriptor arrays
   (first-match scan = `Map::lookup`, lookup.rs:657-678), data values in
   receiver slot arrays at descriptor offsets, accessor pairs hanging off
   descriptors, the dictionary-mode accessor corner (dead for non-index
   keys, as `as_index` fires only for canonical-index Smi names,
   map.rs:633), and the receiver-only array-`length` corner of
   `load_outcome_on` (lookup.rs:71-75).

3. **The simulation relation** `sim(ha, hc, o, d)`: recursive along the
   prototype chain (budget `d`). Local clauses: prototype-link agreement
   (S1), arrays-only-as-receiver (S2), own-property correspondence at
   [[Get]] observables for every non-index key (S3), accessor-pair
   well-formedness with callable-or-undefined halves (S4), offset bounds
   and unique descriptor names (S5).

## The theorems

- `sim_main`: `sim(ha, hc, o, d) ∧ d > 0 ∧ !is_index_key(k) ⟹
  c_outcome(c_walk(hc, o, k, d)) == oget_rec(ha, o, k, d)`
- `sim_main_complete`: additionally with `chain_stops(ha, o, d-1)`, the
  equality holds against the budget-*independent* OrdinaryGet (the
  budgeted family is proved eventually constant).
- `sim_satisfiable`: the relation is inhabited (no vacuous theorem).
- Auxiliary soundness lemmas tie `FAcc` results back to descriptors
  (`scan_acc_sound`, `c_own_acc_sound`) and show the walk's root flag is
  immaterial off the receiver.

## Fragment (preconditions of the theorem)

- ordinary objects and arrays only (no proxies — proxy `[[Get]]` runs
  traps; no primitive receivers — their [[Get]] goes via wrapper
  prototypes, handled by `load_outcome_on`'s coercion, lookup.rs:81-91)
- single `[[Prototype]]` links — the multi-parent `FixedArray` extension
  for `super` (lookup.rs:367-378, 681-696) is excluded
- **non-index keys** — strings that are not canonical array-index
  strings, and symbols. Index keys are served by ovm's elements
  machinery (`load_outcome_keyed`), which is ArrayExotic[[Get]]
  (10.4.2.2), a different clause of the spec
- arrays only as the receiver, never as a prototype (see finding below)
- getter invocation is out of scope by construction: both sides yield
  the getter to call; `Call(getter, Receiver)`'s result is not a
  function of the walk. ES 10.1.8.1 steps 3-5 read only [[Value]] and
  [[Get]] — never attributes — so the correspondence at
  value/getter/absent observables is complete for [[Get]].

## Trust boundary (assumed, not proved)

- heap→model reads: descriptor/slot/prototype accessors against the real
  `unsafe` structures
- interning: name `ptr_eq` ⇔ key equality (map.rs:624)
- `is_index_string`: which abstract strings are canonical array indices
- prototype-chain acyclicity (supplied as the budget `d`, maintained in
  ovm by `set_prototype_of`'s cycle check)
- unique descriptor names / offset bounds (ovm transition-tree
  invariants — clause S5 requires them heap-side)

## Line-by-line correspondence (ovm code -> model)

| ovm code | model | status |
|---|---|---|
| load_outcome_on:68 (null/undefined receiver -> TypeError) | — | out of fragment |
| load_outcome_on:71-75 + object.rs:91-102 (receiver array `length`) | `c_own` root corner | exact: same ordering (before dict/scan), attrs {w: len_writable, e: false, c: false} per ES 10.4.2.2 |
| load_outcome_on:76-80 + string.rs:162-193 (String primitive/wrapper virtual props) | — | NOT modeled; fragment excludes String wrappers everywhere (receiver corner only in ovm) |
| load_outcome_on:81-91 (primitive -> prototype holder) | — | out of fragment |
| load_outcome_on:92-103 (result normalization) | `c_outcome` | exact: NotFound -> undefined, getter-undefined -> undefined, data -> value |
| Tagged::lookup:635-640 (non-object -> NotFound) | `c_own` guard | exact |
| Object::lookup:706-712 (dictionary accessor corner) | `c_own` dict branch | exact, and definitionally dead for fragment keys: `as_index` (map.rs:633-636) is Smi-only; `to_property_key` canonicalizes in-domain index strings to Smi (object.rs:925-928), so string/symbol queries never carry an index |
| Map::lookup:657-678 (descriptor first-match scan) | `scan` | exact: linear order = descriptor array order; data value at receiver slots[offset] (offset from the descriptor's value word, map.rs:617-620); accessor pair from the descriptor's value word (lookup.rs:664-667); attrs from SlotFlags (map.rs:561-598) |
| Map::lookup:680-696 (multi-parent pairs) | — | excluded by S1 |
| Map::lookup:697 + lookup_in_parents:363-380 (proto hop) | `c_walk` recursion | structurally exact; proto-word encodings {null, hole, undefined, weak} all behave as chain end (lookup.rs:137-144, 590-601) — bridge maps them to `LNull` |
| name ptr_eq (lookup.rs:658) | `name_matches` | sound iff query names are interned — guaranteed by `to_property_key` interning exactly once (object.rs:909-917); bridge obligation: every walk entry passes through it |

## Conformance findings (all three runtime-confirmed, ovm release build)

1. **Mid-chain array `length`** — `var o = {__proto__: [1,2,3]}; o.length`
   returns `undefined`; ES returns `3`. Mechanism: arrays hold `length`
   in an internal slot consulted only for the receiver (lookup.rs:71-75,
   ic.rs:21,572); the generic walk reaches Array.prototype's bootstrap
   `length` *accessor* (js_runtime/lib.rs:691-708, installed explicitly
   "so the generic lookup finds `length`", array.rs:458-460), whose
   getter reads the *receiver's* length slot unchecked (array.rs:476) —
   on a non-array receiver this yields garbage (`undefined` here; the
   plain-object length slot is not a Smi in this path).
2. **Key spelling** — `var o = {}; o[-1] = 1; o["-1"]` returns
   `undefined`; ES returns `1`. `to_property_key` returns Smi(-1)
   unstringified (object.rs:892-893) and canonicalizes only in-domain
   index strings (object.rs:925-928): the store and the load use
   different name words for the same ES property.
3. **Mid-chain String wrapper props** —
   `var o = {__proto__: Object("ab")}; o.length` throws
   `TypeError: invalid operand type`; ES returns `2`. Virtual own
   properties are a receiver-side corner only (lookup.rs:76-80,
   string.rs:162).

## Model fixes from the review

- S4 restored its callable-or-undefined halves conjunct (had been
  dropped in a rewrite while the doc comment still claimed it).
- Fragment statement corrected: String wrappers excluded from the whole
  chain; key-spelling and proto-word-encoding bridge obligations
  documented. Re-verified: 15 verified, 0 errors.

## Residual risk

The correspondence table above is still human-verified (this review),
not machine-checked. The remaining seam to close is the `HeapView`
bridge or differential testing of model vs live walk.

## Files

- `lib.rs` — everything: domains, ECMA side, code model, simulation,
  lemmas, theorems (annotated with ES sections and ovm source lines)
