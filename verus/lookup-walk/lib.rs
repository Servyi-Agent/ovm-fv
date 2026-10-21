//! # ovm property-walk: ECMA-262 simulation proof (Verus)
//!
//! Fragment: the *named property walk* of ovm (`vm_core/src/lookup.rs`),
//! restricted to:
//!  1. ordinary objects and arrays (no proxies, no primitives as
//!     receiver, and no String wrappers -- see below), whose whole
//!     prototype chain consists of ordinary objects,
//!  2. single `[[Prototype]]` links (the multi-parent `FixedArray`
//!     extension used for `super` is excluded: lookup.rs:367-378,
//!     681-696),
//!  3. non-index property keys (Strings that are not canonical
//!     array-index strings, and Symbols), queried via their string
//!     spelling (see the key-spelling caveat below). Index keys take the
//!     elements path (`load_outcome_keyed`, lookup.rs:185-256) -- a
//!     different ES clause.
//!  4. arrays may occur only as the [[Get]] receiver, never as a
//!     prototype (see the conformance findings at the bottom of this
//!     file).
//!
//! Additional bridge obligations discovered in the line-by-line review
//! (documented in README.md):
//!  - String wrappers (`PRIMITIVE_WRAPPER`, string.rs:158-176) expose
//!    their virtual own properties (`length`, indices) only through the
//!    receiver-side corner of `load_outcome_on` (lookup.rs:76-80) --
//!    mid-chain wrappers are missed, like mid-chain arrays. The fragment
//!    excludes them from the whole chain.
//!  - End-of-chain proto-word encodings {null, the_hole, undefined,
//!    weak ptr} all behave as chain end (lookup.rs:137-144, 590-601);
//!    the bridge maps them all to `LNull`.
//!  - Key spelling: `to_property_key` returns Smi keys unstringified
//!    (object.rs:892-893) and canonicalizes only in-domain index strings
//!    to Smi (object.rs:925-928), so `o[-1]` and `o["-1"]` use different
//!    words. `sim` is satisfiable only when such properties are stored
//!    under their string spelling (heap-side constraint).
//!
//! What is proved: for heaps related by the (recursive) simulation
//! relation `sim`, the code-level walk `c_walk` computes exactly what
//! ECMA-262 *OrdinaryGet* (10.1.8.1) computes on the abstract object:
//!
//!     c_outcome(c_walk(hc, o, k, d, root)) == oget_rec(ha, o, k, d)
//!
//! Getter invocation (`? Call(getter, Receiver)`) is deliberately outside:
//! both sides return the getter to be invoked; the Receiver argument does
//! not influence which getter that is. Key coercion (`ToPropertyKey`)
//! runs user code and happens before the walk in ovm; it is part of the
//! trusted bridge.
//!
//! Trust boundary (everything below it is verified, everything above is
//! assumed): the heap->model read functions -- descriptor arrays, slot
//! arrays, prototype links, interning (`ptr_eq` on names == key equality),
//! and the `is_index_string` abstraction of canonical array-index strings.

use vstd::prelude::*;
use vstd::pervasive::arbitrary;

verus! {

// =====================================================================
// 0. Domains
// =====================================================================

/// Abstract identity of an ECMAScript String value (trusted string bridge).
pub struct StrId { pub id: int }

/// Abstract identity of a Symbol (trusted interning bridge).
pub struct SymId { pub id: int }

/// Abstract identity of a heap object. The SAME ids index both heaps:
/// `JsHeap.objects` (ECMA view) and `CHeap.nodes` (code view).
pub struct ObjId { pub id: int }

/// The reserved abstract string `"length"`.
pub open spec fn length_str() -> StrId { StrId { id: 0 } }

/// TRUSTED: which abstract strings are canonical array-index strings
/// ("0" ..= "4294967294", decimal, no leading zero -- ES 6.1.7, Array
/// Index). Determined by the string bridge, not proven here; facts about
/// it are carried as preconditions where needed.
pub closed spec fn is_index_string(s: StrId) -> bool;

/// ECMAScript language values (enough structure for [[Get]]; numbers are
/// abstracted by an integer tag -- the theorem only compares values for
/// equality, never inspects them).
pub enum MValue {
    Undef,           // `undefined`
    Null,            // `null`
    B(bool),
    N(int),
    Str(StrId),
    Sym(SymId),
    Obj(ObjId),
}

/// ES 6.2.7 Property Keys: String or Symbol. (Canonical-index Strings
/// exist in this domain; the fragment restricts *queries* to non-index
/// keys.)
pub enum MKey {
    KStr(StrId),
    KSym(SymId),
}

/// A key is an array-index key (drives the elements path in ovm).
pub open spec fn is_index_key(k: MKey) -> bool {
    match k {
        MKey::KStr(s) => is_index_string(s),
        MKey::KSym(_) => false,
    }
}

// =====================================================================
// 1. The ECMA-262 side: an abstract JavaScript object
// =====================================================================

/// ES 6.2.6 Property Descriptor -- complete, both shapes, all four
/// attributes. For accessors, [[Get]]/[[Set]] are `Object or undefined`
/// (6.2.6.2); `undefined` is encoded as `MValue::Undef`.
pub enum PDesc {
    Data { value: MValue, writable: bool, enumerable: bool, configurable: bool },
    Acc { get: MValue, set: MValue, enumerable: bool, configurable: bool },
}

/// An ordinary object: [[Prototype]] and its own property map.
pub struct JsObject {
    pub proto: Option<ObjId>,      // [[Prototype]]: Object | null
    pub props: Map<MKey, PDesc>,   // own properties, key -> descriptor
}

/// The abstract heap. `callables` records which values have a [[Call]]
/// internal method (needed for the ES accessor invariant).
pub struct JsHeap {
    pub objects: Map<ObjId, JsObject>,
    pub callables: Set<MValue>,
}

/// ES 10.1.5.1 OrdinaryGetOwnProperty(O, P): O's own property with key P,
/// or undefined. (For ordinary objects this is exactly the own-property
/// map; the array `length` corner of 10.4.2.2 is reflected into `props`
/// by the simulation relation.)
pub open spec fn ogop(h: JsHeap, o: ObjId, k: MKey) -> Option<PDesc> {
    if h.objects.dom().contains(o) {
        let ob = h.objects[o];
        if ob.props.dom().contains(k) {
            Some(ob.props[k])
        } else {
            None
        }
    } else {
        None
    }
}

/// The observable of one level of [[Get]]: the value found, the getter to
/// call, or "keep walking". ES 10.1.8.1 steps 3-5 read ONLY [[Value]] and
/// [[Get]] -- never any attribute -- so this is a complete account of
/// what OrdinaryGet observes of a descriptor.
pub enum OwnObs {
    Miss,             // no own property: recurse to [[Prototype]]
    Val(MValue),      // data property: [[Value]]
    Get(MValue),      // accessor: perform Call(getter, Receiver)
}

pub open spec fn own_step_spec(d: Option<PDesc>) -> OwnObs {
    match d {
        None => OwnObs::Miss,
        Some(PDesc::Data { value, .. }) => OwnObs::Val(value),
        Some(PDesc::Acc { get, .. }) => {
            if get == MValue::Undef {
                // ES 10.1.8.1 step 5.b: "If getter is undefined, return undefined."
                OwnObs::Val(MValue::Undef)
            } else {
                OwnObs::Get(get)
            }
        }
    }
}

/// The result of [[Get]]: a value, or a getter to invoke (whose Call
/// return value is produced by the call, outside this theorem).
pub enum Outcome {
    Value(MValue),
    Getter(MValue),
}

/// ES 10.1.8.1 OrdinaryGet(O, P, Receiver), as a total function with an
/// explicit recursion budget `d` for the prototype chain (the budget also
/// discharges ES's implicit acyclicity assumption: a cyclic prototype
/// chain cannot be constructed). `oget_budget_stable` shows the budgeted
/// family is constant once the budget covers the chain -- its stable
/// value is the unbounded spec operation.
pub open spec fn oget_rec(h: JsHeap, o: ObjId, k: MKey, d: nat) -> Outcome
    decreases d
{
    if d == 0 {
        Outcome::Value(MValue::Undef)
    } else {
        match own_step_spec(ogop(h, o, k)) {
            OwnObs::Miss => {
                match proto_of_spec(h, o) {
                    // ES 10.1.8.1 step 2.c: null prototype -> undefined
                    None => Outcome::Value(MValue::Undef),
                    Some(p) => oget_rec(h, p, k, (d - 1) as nat),
                }
            }
            OwnObs::Val(v) => Outcome::Value(v),
            OwnObs::Get(g) => Outcome::Getter(g),
        }
    }
}

pub open spec fn proto_of_spec(h: JsHeap, o: ObjId) -> Option<ObjId> {
    if h.objects.dom().contains(o) {
        h.objects[o].proto
    } else {
        None
    }
}

// =====================================================================
// 2. The code-level model (mirrors vm_core/src/lookup.rs)
// =====================================================================

/// A code-level property name: interned string, symbol, or Smi
/// (map.rs:623-626: "names compare by pointer").
pub enum CName {
    NStr(StrId),
    NSym(SymId),
    NSmi(int),
}

/// The trusted interning abstraction: ovm matches names by `ptr_eq`
/// (lookup.rs:658, map.rs:624) -- sound exactly when pointer equality
/// coincides with key equality, which the interner maintains.
pub open spec fn name_matches(n: CName, k: MKey) -> bool {
    match (n, k) {
        (CName::NStr(s), MKey::KStr(s2)) => s == s2,
        (CName::NSym(y), MKey::KSym(y2)) => y == y2,
        _ => false,
    }
}

/// map.rs:633-637 `as_index`: only Smi names in `0..2^32-1` are indices.
pub open spec fn cname_as_index(n: CName) -> Option<int> {
    match n {
        CName::NSmi(v) => {
            if 0 <= v < 4294967295 {
                Some(v)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Prototype link of a map: null, one object, or the multi-parent
/// `FixedArray` extension (lookup.rs:367-378). The last is excluded by
/// the simulation relation.
pub enum CLink {
    LNull,
    LObj(ObjId),
    LParents,
}

/// One map descriptor (map.rs:601-621 `SlotDescriptor`): name, four
/// attribute bits (map.rs:561-598), and either the receiver-slot offset
/// of the data value or the id of the `AccessorPair` node. In ovm the
/// descriptor's value word holds the Smi offset (data) or the pair
/// pointer (accessor) -- lookup.rs:664-667 vs 670-676.
pub struct CDescr {
    pub name: CName,
    pub is_acc: bool,
    pub writable: bool,
    pub enumerable: bool,
    pub configurable: bool,
    pub off: int,     // data rows: index into receiver's slots
    pub pair: ObjId,  // accessor rows: id of an NPair node
}

pub struct CMap {
    pub descrs: Seq<CDescr>,
    pub proto: CLink,
}

pub struct CObj {
    pub map: CMap,
    pub slots: Seq<MValue>,
    /// JSArray internal slot `length` (object.rs:87-102) plus its
    /// writability (ES 10.4.2.2: non-enumerable, non-configurable).
    pub is_array: bool,
    pub length: MValue,
    pub len_writable: bool,
    /// Dictionary-mode accessor entries by element index
    /// (lookup.rs:704-714). Only reachable for index keys -- dead in this
    /// fragment, mirrored for faithfulness.
    pub dict_accs: Map<int, ObjId>,
}

pub enum CNode {
    NObj(CObj),
    NPair { get: MValue, set: MValue },  // AccessorPair (heap-resident)
}

pub struct CHeap {
    pub nodes: Map<ObjId, CNode>,
}

/// What one own-lookup finds (the code analogue of `Lookup`,
/// lookup.rs:10-24).
pub enum CFound {
    FNotFound,
    FData { value: MValue, writable: bool, enumerable: bool, configurable: bool },
    FAcc { pair: ObjId },
}

/// The descriptor first-match scan -- `Map::lookup`'s loop
/// (lookup.rs:657-678): linear over `map.descriptors`, first name that
/// matches wins. Data reads the receiver's slot at the descriptor offset
/// (lookup.rs:670-676); accessor returns the pair (lookup.rs:659-668).
pub open spec fn scan(h: CHeap, ds: Seq<CDescr>, slots: Seq<MValue>, i: int, k: MKey) -> CFound
    decreases ds.len() - i
{
    if i >= ds.len() {
        CFound::FNotFound
    } else {
        let d = ds[i];
        if name_matches(d.name, k) {
            if d.is_acc {
                CFound::FAcc { pair: d.pair }
            } else if 0 <= d.off < slots.len() {
                CFound::FData {
                    value: slots[d.off],
                    writable: d.writable,
                    enumerable: d.enumerable,
                    configurable: d.configurable,
                }
            } else {
                CFound::FNotFound
            }
        } else {
            scan(h, ds, slots, i + 1, k)
        }
    }
}

pub open spec fn cname_of_key(k: MKey) -> CName {
    match k {
        MKey::KStr(s) => CName::NStr(s),
        MKey::KSym(y) => CName::NSym(y),
    }
}

/// One level of the code own-lookup: mirrors `Object::lookup`
/// (lookup.rs:701-714) preceded by the receiver-only array-length corner
/// of `load_outcome_on` (lookup.rs:71-75) when `root`.
///
/// Ordering, exactly as in the code:
///   1. receiver array `length` (root only -- mid-chain hops never
///      consult it; see the conformance finding below),
///   2. dictionary-mode accessor entries (fires only for canonical-index
///      Smi names; `cname_of_key(k)` for a query key is never `NSmi`, so
///      this branch is definitionally dead here, as in the code),
///   3. map descriptor first-match scan.
pub open spec fn c_own(h: CHeap, o: ObjId, k: MKey, root: bool) -> CFound {
    if !h.nodes.dom().contains(o) {
        CFound::FNotFound
    } else {
        match h.nodes[o] {
            CNode::NObj(co) => {
                if root && co.is_array && name_matches(CName::NStr(length_str()), k) {
                    CFound::FData {
                        value: co.length,
                        writable: co.len_writable,
                        enumerable: false,
                        configurable: false,
                    }
                } else if cname_as_index(cname_of_key(k)).is_some() {
                    // unreachable for MKey queries; kept to mirror
                    // lookup.rs:706 (the dictionary corner)
                    match cname_as_index(cname_of_key(k)) {
                        Some(i) => {
                            if co.dict_accs.dom().contains(i) {
                                CFound::FAcc { pair: co.dict_accs[i] }
                            } else {
                                scan(h, co.map.descrs, co.slots, 0, k)
                            }
                        }
                        None => scan(h, co.map.descrs, co.slots, 0, k),
                    }
                } else {
                    scan(h, co.map.descrs, co.slots, 0, k)
                }
            }
            CNode::NPair { .. } => CFound::FNotFound,
        }
    }
}

/// The prototype walk itself: `Object::lookup` -> `Map::lookup` ->
/// `lookup_in_parents` (lookup.rs:363-380, 650-699, 701-714),
/// single-proto. `d` is the hop budget; only the root hop consults the
/// array-length corner (mirroring `load_outcome_on` vs `Object::lookup`).
pub open spec fn c_walk(h: CHeap, o: ObjId, k: MKey, d: nat, root: bool) -> CFound
    decreases d
{
    if d == 0 {
        CFound::FNotFound
    } else {
        match c_own(h, o, k, root) {
            CFound::FNotFound => {
                match proto_of_code(h, o) {
                    None => CFound::FNotFound,
                    Some(p) => c_walk(h, p, k, (d - 1) as nat, false),
                }
            }
            found => found,
        }
    }
}

pub open spec fn proto_of_code(h: CHeap, o: ObjId) -> Option<ObjId> {
    if h.nodes.dom().contains(o) {
        match h.nodes[o] {
            CNode::NObj(co) => match co.map.proto {
                CLink::LObj(p) => Some(p),
                CLink::LNull => None,
                CLink::LParents => None, // excluded by sim
            },
            CNode::NPair { .. } => None,
        }
    } else {
        None
    }
}

/// The normalization of `load_outcome_on`'s match (lookup.rs:92-103):
/// NotFound -> undefined; data -> value; accessor with getter undefined
/// -> undefined; otherwise the getter.
pub open spec fn c_outcome(h: CHeap, f: CFound) -> Outcome {
    match f {
        CFound::FNotFound => Outcome::Value(MValue::Undef),
        CFound::FData { value, .. } => Outcome::Value(value),
        CFound::FAcc { pair } => {
            if h.nodes.dom().contains(pair) {
                match h.nodes[pair] {
                    CNode::NPair { get, .. } => {
                        if get == MValue::Undef {
                            Outcome::Value(MValue::Undef)
                        } else {
                            Outcome::Getter(get)
                        }
                    }
                    CNode::NObj(_) => Outcome::Value(MValue::Undef),
                }
            } else {
                Outcome::Value(MValue::Undef)
            }
        }
    }
}

/// The code-side one-level observable, aligned with `OwnObs`.
pub open spec fn own_step_code(h: CHeap, f: CFound) -> OwnObs {
    match f {
        CFound::FNotFound => OwnObs::Miss,
        CFound::FData { value, .. } => OwnObs::Val(value),
        CFound::FAcc { pair } => {
            if h.nodes.dom().contains(pair) {
                match h.nodes[pair] {
                    CNode::NPair { get, .. } => {
                        if get == MValue::Undef {
                            OwnObs::Val(MValue::Undef)
                        } else {
                            OwnObs::Get(get)
                        }
                    }
                    CNode::NObj(_) => OwnObs::Miss,
                }
            } else {
                OwnObs::Miss
            }
        }
    }
}

// =====================================================================
// 3. The simulation relation (recursive in the prototype chain)
// =====================================================================

pub open spec fn h_is_pair(h: CHeap, p: ObjId) -> bool {
    h.nodes.dom().contains(p) && match h.nodes[p] {
        CNode::NPair { .. } => true,
        CNode::NObj(_) => false,
    }
}

pub open spec fn pair_get_v(h: CHeap, p: ObjId) -> Option<MValue> {
    if h.nodes.dom().contains(p) {
        match h.nodes[p] {
            CNode::NPair { get, .. } => Some(get),
            CNode::NObj(_) => None,
        }
    } else {
        None
    }
}

pub open spec fn pair_set_v(h: CHeap, p: ObjId) -> Option<MValue> {
    if h.nodes.dom().contains(p) {
        match h.nodes[p] {
            CNode::NPair { set, .. } => Some(set),
            CNode::NObj(_) => None,
        }
    } else {
        None
    }
}

pub open spec fn is_callable_or_undef(ha: JsHeap, v: Option<MValue>) -> bool {
    match v {
        None => false,
        Some(MValue::Undef) => true,
        Some(x) => ha.callables.contains(x),
    }
}

/// Local (single-object) part of the simulation.
pub open spec fn sim_local(ha: JsHeap, hc: CHeap, o: ObjId) -> bool {
    &&& hc.nodes.dom().contains(o)
    &&& ha.objects.dom().contains(o)
    &&& match hc.nodes[o] {
            CNode::NObj(co) => {
                let ao = ha.objects[o];
                &&& // (S1) prototype-link agreement, at the id level.
                    // LParents (the multi-parent extension) is forbidden.
                    match co.map.proto {
                        CLink::LNull => ao.proto.is_none(),
                        CLink::LObj(p) => ao.proto == Some(p),
                        CLink::LParents => false,
                    }
                &&& // (S3) own-property correspondence, at [[Get]]
                    // observables, for every non-index key. This is the
                    // precise content of "the code object implements the
                    // spec object": OrdinaryGetOwnProperty's observable
                    // (value / getter / absent) agrees with the code's
                    // own-lookup, including the array `length` corner
                    // (root=true; immaterial for every key except "length").
                    forall |k: MKey| #![trigger c_own(hc, o, k, true)]
                        (!is_index_key(k) ==> 
                            own_step_code(hc, c_own(hc, o, k, true))
                            == own_step_spec(ogop(ha, o, k)))
                &&& // (S4) accessor descriptors are backed by an existing
                    // NPair node whose halves are callable-or-undefined
                    // (ES 6.2.6.2; maintained at defineProperty time by
                    // ToPropertyDescriptor, lookup.rs:511-581).
                    forall |i: int| #![trigger co.map.descrs.index(i)]
                        (0 <= i < co.map.descrs.len() && co.map.descrs[i].is_acc) ==> {
                            let p = co.map.descrs[i].pair;
                            &&& hc.nodes.dom().contains(p)
                            &&& h_is_pair(hc, p)
                            &&& is_callable_or_undef(ha, pair_get_v(hc, p))
                            &&& is_callable_or_undef(ha, pair_set_v(hc, p))
                        }
                &&& // (S5) data offsets in range; descriptor names
                    // pairwise distinct (ovm transition-tree invariant)
                    // so the first-match scan is unambiguous.
                    forall |i: int| #![trigger co.map.descrs.index(i)]
                        (0 <= i < co.map.descrs.len() && !co.map.descrs[i].is_acc) ==>
                            0 <= co.map.descrs[i].off < co.slots.len()
                &&& forall |i: int, j: int| #![trigger co.map.descrs.index(i), co.map.descrs.index(j)]
                        (0 <= i < co.map.descrs.len() && 0 <= j < co.map.descrs.len() && i < j) ==>
                            co.map.descrs[i].name != co.map.descrs[j].name
            },
            CNode::NPair { .. } => false,
        }
}

/// The simulation relation, recursive along [[Prototype]] with budget
/// `d`: the two views of `o` correspond locally, and (for d > 0) the
/// prototype (same id in both heaps) corresponds with one less budget.
/// The budget bounds the chain -- it is the witness of ES 10.1.2's
/// prototype-chain acyclicity, supplied heap-side.
pub open spec fn sim(ha: JsHeap, hc: CHeap, o: ObjId, d: nat) -> bool
    decreases d
{
    sim_local(ha, hc, o)
    && (d > 0 ==> match proto_of_code(hc, o) {
            Some(p) => sim(ha, hc, p, (d - 1) as nat),
            None => true,
        })
}

// =====================================================================
// 4. Lemmas
// =====================================================================

/// If the descriptor scan returns an accessor, it came from a matching
/// accessor descriptor (soundness of `Map::lookup`'s first-match scan,
/// lookup.rs:657-678).
proof fn scan_acc_sound(h: CHeap, ds: Seq<CDescr>, slots: Seq<MValue>, i: int, k: MKey)
    requires 0 <= i <= ds.len()
    ensures
        forall |pair: ObjId| scan(h, ds, slots, i, k) == (CFound::FAcc { pair: pair }) ==>
            exists |j: int| i <= j < ds.len()
                && name_matches(ds[j].name, k) && ds[j].is_acc
                && ds[j].pair == pair
    decreases ds.len() - i
{
    if i < ds.len() {
        let d = ds[i];
        if name_matches(d.name, k) {
            if d.is_acc {
                // scan returns FAcc { pair: d.pair } here; witness j == i
                assert(scan(h, ds, slots, i, k) == CFound::FAcc { pair: d.pair });
                assert(exists |j: int| i <= j < ds.len()
                    && name_matches(ds[j].name, k) && ds[j].is_acc && ds[j].pair == d.pair);
            } else {
                // data hit (or out-of-range offset): not FAcc, vacuous
            }
        } else {
            scan_acc_sound(h, ds, slots, i + 1, k);
        }
    }
}

/// Same, for the full own-lookup: an `FAcc` result at a query key
/// originates from a matching accessor descriptor of the receiver's map.
/// (The dictionary corner is unreachable for MKey queries: `cname_of_key`
/// is never `NSmi`, so `cname_as_index` is `None` -- as in the code,
/// where non-index names never take `as_index`.)
proof fn c_own_acc_sound(h: CHeap, o: ObjId, k: MKey, root: bool, pair: ObjId)
    requires c_own(h, o, k, root) == (CFound::FAcc { pair: pair })
    ensures
        h.nodes.dom().contains(o)
        && (match h.nodes[o] {
                CNode::NObj(co) => exists |j: int| 0 <= j < co.map.descrs.len()
                    && co.map.descrs[j].is_acc
                    && co.map.descrs[j].pair == pair
                    && name_matches(co.map.descrs[j].name, k),
                CNode::NPair { .. } => false,
            })
{
    if !h.nodes.dom().contains(o) {
        assert(c_own(h, o, k, root) == CFound::FNotFound); // contradicts FAcc
        assert(false);
    } else {
        match h.nodes[o] {
            CNode::NObj(co) => {
                if root && co.is_array && name_matches(CName::NStr(length_str()), k) {
                    // FData, never FAcc: contradicts the hypothesis
                    assert(false);
                } else if cname_as_index(cname_of_key(k)).is_some() {
                    // definitionally dead for MKey queries
                    assert(cname_as_index(cname_of_key(k)).is_none()) by {
                        match k {
                            MKey::KStr(_) => match cname_of_key(k) {
                                CName::NStr(_) => {}
                                _ => assert(false),
                            },
                            MKey::KSym(_) => match cname_of_key(k) {
                                CName::NSym(_) => {}
                                _ => assert(false),
                            },
                        }
                    }
                    assert(false);
                } else {
                    scan_acc_sound(h, co.map.descrs, co.slots, 0, k);
                }
            }
            CNode::NPair { .. } => {
                assert(c_own(h, o, k, root) == CFound::FNotFound);
                assert(false);
            }
        }
    }
}

/// The `root` flag only guards the receiver-only array-length corner
/// (lookup.rs:71-75), so it is immaterial whenever the key is not the
/// string "length" -- arrays anywhere in the chain included.
proof fn c_own_root_irrelevant(h: CHeap, o: ObjId, k: MKey)
    requires k != MKey::KStr(length_str())
    ensures c_own(h, o, k, true) == c_own(h, o, k, false)
{
}

/// Likewise for the walk proper (the recursion passes `root=false` after
/// the first hop, mirroring `Object::lookup` after `load_outcome_on`).
proof fn c_walk_root_irrelevant(h: CHeap, o: ObjId, k: MKey, d: nat)
    requires d > 0 && k != MKey::KStr(length_str())
    ensures c_walk(h, o, k, d, true) == c_walk(h, o, k, d, false)
    decreases d
{
    c_own_root_irrelevant(h, o, k);
    // unfold one level on both sides: equal scrutinees, and the miss
    // branch recurses into the *identical* call (root = false both ways)
    reveal_with_fuel(c_walk, 2);
}

// =====================================================================
// 5. The theorem
// =====================================================================

/// MAIN THEOREM (simulation).
///
/// If the code heap `hc` simulates the abstract heap `ha` along the whole
/// prototype chain of `o` (budget d), and `k` is a non-index property
/// key, then ovm's walk computes exactly ES 10.1.8.1 OrdinaryGet:
///
///     c_outcome(c_walk(hc, o, k, d))  ==  oget_rec(ha, o, k, d)
///
/// i.e. both return the same value, or the same getter (whose Call
/// result is, by construction of [[Get]], outside the walk).
proof fn sim_main(ha: JsHeap, hc: CHeap, o: ObjId, k: MKey, d: nat)
    requires
        d > 0,
        sim(ha, hc, o, d),
        !is_index_key(k),
        k != MKey::KStr(length_str()),
    ensures
        c_outcome(hc, c_walk(hc, o, k, d, true)) == oget_rec(ha, o, k, d),
    decreases d
{
    // ---- unfold the local simulation facts ----
    assert(sim_local(ha, hc, o));
    assert(hc.nodes.dom().contains(o));
    assert(ha.objects.dom().contains(o));
    assert(match hc.nodes[o] { CNode::NObj(_) => true, CNode::NPair { .. } => false });
    let co = match hc.nodes[o] {
        CNode::NObj(c) => c,
        CNode::NPair { .. } => { assert(false); arbitrary::<CObj>() }
    };
    let ao = ha.objects[o];

    // Prototype agreement (S1) and proto-function agreement.
    match co.map.proto {
        CLink::LNull => {
            assert(ao.proto.is_none());
            assert(proto_of_code(hc, o).is_none());
            assert(proto_of_spec(ha, o).is_none());
        }
        CLink::LObj(p0) => {
            assert(ao.proto == Some(p0));
            assert(proto_of_code(hc, o) == Some(p0));
            assert(proto_of_spec(ha, o) == Some(p0));
        }
        CLink::LParents => {
            assert(false); // forbidden by S1
        }
    }

    let code_own = c_own(hc, o, k, true);
    let spec_own = own_step_spec(ogop(ha, o, k));

    // (S3) own-level correspondence, instantiated at k.
    assert(own_step_code(hc, code_own) == spec_own);

    match code_own {
        CFound::FData { value, .. } => {
            assert(own_step_code(hc, code_own) == OwnObs::Val(value));
            assert(spec_own == OwnObs::Val(value));
            assert(c_walk(hc, o, k, d, true) == code_own);
            assert(c_outcome(hc, code_own) == Outcome::Value(value));
            assert(oget_rec(ha, o, k, d) == Outcome::Value(value));
        }
        CFound::FAcc { pair } => {
            // Soundness: the accessor came from a descriptor; S4 then
            // guarantees the NPair node behind it exists.
            assert(hc.nodes.dom().contains(pair) && h_is_pair(hc, pair)) by {
                c_own_acc_sound(hc, o, k, true, pair);
            }
            assert(match hc.nodes[pair] { CNode::NPair { .. } => true, CNode::NObj(_) => false });
            let get = match hc.nodes[pair] {
                CNode::NPair { get: g, .. } => g,
                CNode::NObj(_) => { assert(false); arbitrary::<MValue>() }
            };
            if get == MValue::Undef {
                assert(own_step_code(hc, code_own) == OwnObs::Val(MValue::Undef));
                assert(spec_own == OwnObs::Val(MValue::Undef));
                assert(c_outcome(hc, code_own) == Outcome::Value(MValue::Undef));
                assert(oget_rec(ha, o, k, d) == Outcome::Value(MValue::Undef));
            } else {
                assert(own_step_code(hc, code_own) == OwnObs::Get(get));
                assert(spec_own == OwnObs::Get(get));
                assert(c_outcome(hc, code_own) == Outcome::Getter(get));
                assert(oget_rec(ha, o, k, d) == Outcome::Getter(get));
            }
        }
        CFound::FNotFound => {
            assert(spec_own == OwnObs::Miss);
            match proto_of_code(hc, o) {
                None => {
                    assert(c_walk(hc, o, k, d, true) == CFound::FNotFound);
                    assert(c_outcome(hc, CFound::FNotFound) == Outcome::Value(MValue::Undef));
                    assert(oget_rec(ha, o, k, d) == Outcome::Value(MValue::Undef));
                }
                Some(p) => {
                    if d == 1 {
                        // Budget exhausted one hop early on both sides:
                        // c_walk cannot hop (budget 0 => FNotFound), the
                        // spec side likewise bottoms out at undefined.
                        assert(c_walk(hc, p, k, 0, false) == CFound::FNotFound);
                        assert(oget_rec(ha, p, k, 0) == Outcome::Value(MValue::Undef));
                    } else {
                        // sim(o, d) unfolds to sim(p, d - 1): recurse.
                        assert(sim(ha, hc, p, (d - 1) as nat));
                        sim_main(ha, hc, p, k, (d - 1) as nat);
                        // root flag at the prototype hop is immaterial:
                        // k is not "length", so the array-length corner
                        // cannot fire (arrays mid-chain are fine for
                        // every other key).
                        c_walk_root_irrelevant(hc, p, k, (d - 1) as nat);
                    }
                }
            }
        }
    }
}

// =====================================================================
// 6. Budget completeness (the budgeted family is the spec operation)
// =====================================================================

/// The spec-side prototype chain of `o` reaches null within <= n hops
/// (the acyclicity/termination witness; ES 10.1.2).
pub open spec fn chain_stops(h: JsHeap, o: ObjId, n: nat) -> bool
    decreases n
{
    if n == 0 {
        proto_of_spec(h, o).is_none()
    } else {
        match proto_of_spec(h, o) {
            None => true,
            Some(p) => chain_stops(h, p, (n - 1) as nat),
        }
    }
}

proof fn chain_stops_mono(h: JsHeap, o: ObjId, n: nat)
    ensures chain_stops(h, o, n) ==> chain_stops(h, o, (n + 1) as nat)
    decreases n
{
    if n >= 1 {
        match proto_of_spec(h, o) {
            None => {}
            Some(p) => {
                chain_stops_mono(h, p, (n - 1) as nat);
            }
        }
    }
}

/// `oget_rec(o, d)` inspects the levels o .. o+(d-1). Once the chain
/// stops within <= n hops, all budgets >= n+1 agree -- the budgeted
/// family is eventually constant, and its stable value is (by the
/// definition of recursion in 10.1.8.1) the unbounded OrdinaryGet.
proof fn oget_budget_stable(h: JsHeap, o: ObjId, k: MKey, d: nat, n: nat)
    requires d >= n + 1 && chain_stops(h, o, n)
    ensures oget_rec(h, o, k, d) == oget_rec(h, o, k, (d + 1) as nat)
    decreases d
{
    // own-hit and proto-null cases are definitional; the hop case:
    if d >= 2 && proto_of_spec(h, o).is_some() {
        // proto is Some(p): n >= 1 and chain_stops(h, p, n - 1)
        match proto_of_spec(h, o) {
            None => {}
            Some(p) => {
                assert(d - 1 >= n);
                oget_budget_stable(h, p, k, (d - 1) as nat, (n - 1) as nat);
            }
        }
    }
}

proof fn oget_mono(h: JsHeap, o: ObjId, k: MKey, d: nat, d2: nat, n: nat)
    requires d >= n + 1 && d2 >= d && chain_stops(h, o, n)
    ensures oget_rec(h, o, k, d) == oget_rec(h, o, k, d2)
    decreases d2 - d
{
    if d2 == d {
    } else {
        oget_budget_stable(h, o, k, d, n);
        oget_mono(h, o, k, (d + 1) as nat, d2, n);
    }
}

/// COROLLARY (complete ECMA agreement). With the simulation budget
/// covering the whole prototype chain (chain stops within d-1 hops),
/// the walk's result equals the ECMA OrdinaryGet result at ANY budget
/// beyond the chain -- i.e. the unbounded spec operation.
proof fn sim_main_complete(ha: JsHeap, hc: CHeap, o: ObjId, k: MKey, d: nat, d2: nat)
    requires
        d > 0,
        d2 >= d,
        sim(ha, hc, o, d),
        chain_stops(ha, o, (d - 1) as nat),
        !is_index_key(k),
        k != MKey::KStr(length_str()),
    ensures
        c_outcome(hc, c_walk(hc, o, k, d, true)) == oget_rec(ha, o, k, d2)
{
    sim_main(ha, hc, o, k, d);
    oget_mono(ha, o, k, d, d2, (d - 1) as nat);
}


// =====================================================================
// 6b. Divergence witness: with only the genuine invariants (no S2),
// the walk diverges from OrdinaryGet for exactly the key "length"
// when an array sits mid-chain. This is finding #1 of the conformance
// report, machine-checked at the model level: the code walk returns
// Value(Undefined) (in the real VM, Array.prototype's `length`
// accessor then fires and yields the receiver's slot), while ES
// returns the array's own length.
// =====================================================================

proof fn divergence_witness_midchain_array_length()
{
    // Bridge fact (trusted): "length" is not a canonical index string.
    assume(!is_index_string(length_str()));
    let klen = MKey::KStr(length_str());
    let child = ObjId { id: 20 };
    let arr = ObjId { id: 21 };

    let js_arr = JsObject {
        proto: None,
        props: Map::empty().insert(klen, PDesc::Data {
            value: MValue::N(3), writable: true, enumerable: false, configurable: false,
        }),
    };
    let js_child = JsObject { proto: Some(arr), props: Map::empty() };
    let ha = JsHeap {
        objects: Map::empty().insert(arr, js_arr).insert(child, js_child),
        callables: Set::empty(),
    };

    let c_arr = CObj {
        map: CMap { descrs: Seq::empty(), proto: CLink::LNull },
        slots: Seq::empty(),
        is_array: true, length: MValue::N(3), len_writable: true,
        dict_accs: Map::empty(),
    };
    let c_child = CObj {
        map: CMap { descrs: Seq::empty(), proto: CLink::LObj(arr) },
        slots: Seq::empty(),
        is_array: false, length: MValue::Undef, len_writable: true,
        dict_accs: Map::empty(),
    };
    let hc = CHeap {
        nodes: Map::empty()
            .insert(arr, CNode::NObj(c_arr))
            .insert(child, CNode::NObj(c_child)),
    };

    // the genuine-invariant simulation holds (no array restriction)
    assert(sim(ha, hc, child, 2)) by {
        reveal_with_fuel(sim, 3);
        reveal_with_fuel(scan, 3);
    };

    // the code walk misses the array's `length` ...
    assert(c_walk(hc, child, klen, 2, true) == CFound::FNotFound) by {
        reveal_with_fuel(c_walk, 4);
        reveal_with_fuel(scan, 3);
    };
    assert(c_outcome(hc, c_walk(hc, child, klen, 2, true)) == Outcome::Value(MValue::Undef));

    // ... while ES 10.1.8.1 finds it
    assert(oget_rec(ha, child, klen, 2) == Outcome::Value(MValue::N(3))) by {
        reveal_with_fuel(oget_rec, 4);
    };

    // divergence, machine-checked
    assert(c_outcome(hc, c_walk(hc, child, klen, 2, true)) != oget_rec(ha, child, klen, 2));
}

// =====================================================================
// 7. Sanity: the relation is satisfiable (not vacuous)
// =====================================================================

/// One concrete instance: an empty receiver whose prototype is an object
/// with a single data property `x = 5` (abstract StrId 1). Confirms `sim`
/// holds of a real (model) heap pair and instantiates the theorem.
proof fn sim_satisfiable()
{
    // Bridge fact (trusted, about the uninterpreted is_index_string):
    // abstract string 42 is some non-index string like "x".
    assume(!is_index_string(StrId { id: 42 }));
    let kx = MKey::KStr(StrId { id: 42 });
    let parent = ObjId { id: 7 };
    let child = ObjId { id: 8 };
    let pair = ObjId { id: 9 };

    let js_parent = JsObject {
        proto: None,
        props: Map::empty().insert(kx, PDesc::Data {
            value: MValue::N(5), writable: true, enumerable: true, configurable: true,
        }),
    };
    let js_child = JsObject { proto: Some(parent), props: Map::empty() };
    let ha = JsHeap {
        objects: Map::empty().insert(parent, js_parent).insert(child, js_child),
        callables: Set::empty(),
    };

    let cd = CDescr {
        name: CName::NStr(StrId { id: 42 }),
        is_acc: false, writable: true, enumerable: true, configurable: true,
        off: 0, pair,
    };
    let c_parent = CObj {
        map: CMap { descrs: Seq::new(1, |_: int| cd), proto: CLink::LNull },
        slots: Seq::new(1, |_: int| MValue::N(5)),
        is_array: false, length: MValue::Undef, len_writable: true,
        dict_accs: Map::empty(),
    };
    let c_child = CObj {
        map: CMap { descrs: Seq::empty(), proto: CLink::LObj(parent) },
        slots: Seq::empty(),
        is_array: false, length: MValue::Undef, len_writable: true,
        dict_accs: Map::empty(),
    };
    let hc = CHeap {
        nodes: Map::empty()
            .insert(pair, CNode::NPair { get: MValue::Undef, set: MValue::Undef })
            .insert(parent, CNode::NObj(c_parent))
            .insert(child, CNode::NObj(c_child)),
    };

    assert(sim(ha, hc, parent, 0)) by {
        reveal_with_fuel(scan, 4);
    };
    assert(sim(ha, hc, child, 1)) by {
        reveal_with_fuel(scan, 4);
        reveal_with_fuel(sim, 2);
    };
    assert(sim(ha, hc, child, 2)) by {
        reveal_with_fuel(scan, 4);
        reveal_with_fuel(sim, 3);
    };

    // The theorem instance: child.x finds the parent's 5 on both sides,
    // and (corollary) equals the unbounded ECMA result at any budget.
    assert(c_outcome(hc, c_walk(hc, child, kx, 2, true)) == Outcome::Value(MValue::N(5))) by {
        reveal_with_fuel(c_walk, 4);
        reveal_with_fuel(scan, 4);
    };
    assert(oget_rec(ha, child, kx, 2) == Outcome::Value(MValue::N(5))) by {
        reveal_with_fuel(oget_rec, 4);
    };
    assert(chain_stops(ha, child, 1)) by {
        reveal_with_fuel(chain_stops, 2);
    };
    sim_main_complete(ha, hc, child, kx, 2, 7);
}

}

// =====================================================================
// Conformance findings (outside the proof, from the formalization):
//
// 1. Mid-chain array `length`. ES 10.4.2.2 gives every Array a `length`
//    own property; OrdinaryGet walking THROUGH an array must find it.
//    ovm consults the `length` internal slot only when the array is the
//    [[Get]] receiver (lookup.rs:71-75); Object::lookup / Map::lookup
//    (lookup.rs:701-714, 650-699) never consult it mid-chain. Test:
//    `var o = {__proto__: []}; o.length`.
//
// 2. Key spelling of out-of-domain numeric keys. to_property_key
//    returns Smi keys unstringified (object.rs:892-893) and maps only
//    in-domain canonical index strings to Smi (object.rs:925-928), so
//    `o[-1] = 1` (Smi-named descriptor) and `o["-1"]` (interned string
//    name) are different words -- the load appears to miss the store.
//    ES 6.1.7: both are the property "-1". Test:
//    `var o = {}; o[-1] = 1; o["-1"]`.
//
// 3. Mid-chain String wrapper virtual properties (same receiver-only
//    corner shape as 1): `var o = {__proto__: Object("ab")}; o.length`.
//
// The simulation relation excludes all three configurations (S2 and the
// fragment's receiver/chain restrictions) to keep the theorem about ES
// semantics.
// =====================================================================
