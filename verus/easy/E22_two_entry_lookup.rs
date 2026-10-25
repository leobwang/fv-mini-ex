// E22 | Two-entry lookup | 2-3 min | Map, map![], dom, m[k]
// GOAL
//   Look q up in the two-entry map {k1: v1, k2: v2}, without building a map at runtime.
//
// REFERENCE
//   map![k1 => v1, k2 => v2]      // Map literal = Map::empty().insert(k1, v1).insert(k2, v2)
//   m.dom().contains(k)           // key present?  (dom() is a Set<K>)
//   m[k]                          // value for a key in the domain
//   m.insert(k, v)                // later inserts overwrite earlier ones
// NOTE: k1 and k2 may be equal.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn lookup2(k1: u64, v1: u64, k2: u64, v2: u64, q: u64) -> (r: Option<u64>)
    ensures
        r is Some <==> map![k1 => v1, k2 => v2].dom().contains(q),
        r is Some ==> r->0 == map![k1 => v1, k2 => v2][q],
// END SPEC
{
    None // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The domain is {k1, k2}; what is the value at k1 when k1 == k2?
H2. Check the entry that was inserted last first.
H3. if q == k2 { Some(v2) } else if q == k1 { Some(v1) } else { None }
*/
