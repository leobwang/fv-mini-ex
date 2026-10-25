// M15 | Prefix sums | 10-15 min | recursive sum spec, subrange, =~=, overflow bound [R18]
// GOAL
//   Return out with out.len() == v.len() + 1 and out[i] == v[0] + ... + v[i-1] (out[0] == 0).
//   The length bound makes every sum fit in u64.
//
// REFERENCE
//   let mut out: Vec<u64> = Vec::new(); out.push(0);
//   assert(v@.subrange(0, i + 1).drop_last() =~= v@.subrange(0, i as int));   // unlock sum's step
//   acc <= i * 0xFFFF_FFFF          // linear bound (variable times literal): proves no overflow
//   forall|k: int| 0 <= k <= i ==> out[k] == sum(v@.subrange(0, k))   // earlier entries survive push
//   (v[i] as u64)                   // widen before adding

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn sum(s: Seq<u32>) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { sum(s.drop_last()) + s.last() }
}

fn prefix_sums(v: &Vec<u32>) -> (out: Vec<u64>)
    requires v.len() <= 0xFFFF_FFFF,
    ensures
        out.len() == v.len() + 1,
        forall|i: int| 0 <= i <= v.len() ==> out[i] == sum(v@.subrange(0, i)),
// END SPEC
{
    let mut out: Vec<u64> = Vec::new();
    out.push(0);
    let mut acc: u64 = 0;
    for i in 0..v.len()
        invariant
            v.len() <= 0xFFFF_FFFF,
            out.len() == i + 1,
            acc == sum(v@.subrange(0, i as int)),
            acc <= i * 0xFFFF_FFFF,
            forall|k: int| 0 <= k <= i ==> out[k] == sum(v@.subrange(0, k)),
    {
        assert(v@.subrange(0, i + 1).drop_last() =~= v@.subrange(0, i as int));
        acc = acc + v[i] as u64;
        out.push(acc);
    }
    out
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Keep a running total acc; push it after adding each element.
H2. Invariant: out has i+1 entries, all correct; acc is the sum of the prefix v[0..i);
    acc <= i * (2^32 - 1) for overflow. sum peels the LAST element, so assert that the
    longer prefix minus its last element is the shorter prefix (=~=).
H3. invariant v.len() <= 0xFFFF_FFFF, out.len() == i + 1, acc == sum(v@.subrange(0, i as int)),
        acc <= i * 0xFFFF_FFFF, forall|k: int| 0 <= k <= i ==> out[k] == sum(v@.subrange(0, k)),
    body: assert(v@.subrange(0, i + 1).drop_last() =~= v@.subrange(0, i as int));
*/
