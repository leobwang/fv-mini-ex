// M05 | Reverse in place | 10-15 min | &mut Vec, swap loop, old(v), final(v) [R07]
// GOAL
//   Reverse v in place: afterwards position i holds what was at position n-1-i.
//
// REFERENCE
//   ensures final(v)[i] == old(v)[j]        // final(v): value at exit; old(v): value at entry
//   invariant v.len() == old(v).len(),      // in the body, `v` is current, `old(v)` the entry value
//   let a = v[i]; let b = v[j]; v.set(i, b); v.set(j, a);   // swap via two reads
//   forall|k: int| i <= k < n - i ==> v[k] == old(v)[k]    // the untouched middle
// NOTE: `n - 1 - i` on usize underflows when n == 0; guard or reason about it.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn reverse(v: &mut Vec<i64>)
    ensures
        final(v).len() == old(v).len(),
        forall|i: int| 0 <= i < old(v).len() ==> final(v)[i] == old(v)[old(v).len() - 1 - i],
// END SPEC
{

}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Swap v[i] with v[n-1-i] for i < n/2.
H2. The invariant splits v into three regions: the swapped left part, the swapped right part,
    and the untouched middle. Also keep v.len() == n and n == old(v).len().
H3. forall|k: int| 0 <= k < i ==> v[k] == old(v)[n - 1 - k],
    forall|k: int| 0 <= k < i ==> v[n - 1 - k] == old(v)[k],
    forall|k: int| i <= k < n - i ==> v[k] == old(v)[k],
*/
