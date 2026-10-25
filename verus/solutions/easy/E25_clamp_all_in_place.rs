// E25 | Clamp all in place | 2-3 min | v.set, old(v) in invariants
// GOAL
//   Replace every element greater than hi by hi, in place.
//
// REFERENCE
//   v.set(i, x);                        // v@ becomes v@.update(i, x); needs i < v.len()
//   final(v)@, old(v)@                  // in ensures: exit and entry views
//   invariant v.len() == old(v).len(),  // in a body, old(v) is the entry value, v the current
//   Say what the loop has NOT touched yet as well as what it has.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn clamp_all(v: &mut Vec<u64>, hi: u64)
    ensures
        final(v).len() == old(v).len(),
        forall|i: int| 0 <= i < old(v).len() ==>
            final(v)[i] == if old(v)[i] > hi { hi } else { old(v)[i] },
// END SPEC
{
    let n = v.len();
    for i in 0..n
        invariant
            v.len() == n,
            n == old(v).len(),
            forall|j: int| 0 <= j < i ==> v[j] == if old(v)[j] > hi { hi } else { old(v)[j] },
            forall|j: int| i <= j < n ==> v[j] == old(v)[j],
    {
        if v[i] > hi {
            v.set(i, hi);
        }
    }
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Loop over indices 0..n with n = v.len() taken before the loop.
H2. Four invariants: length unchanged, n is the entry length, prefix done, suffix untouched.
H3. invariant v.len() == n, n == old(v).len(), forall|j: int| 0 <= j < i ==> v[j] == (clamped old(v)[j]), forall|j: int| i <= j < n ==> v[j] == old(v)[j],
*/
