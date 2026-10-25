// M40 | Byte histogram | 15-20 min | vec![0; n], count spec, per-bucket invariant, Vec::set
// GOAL
//   Count how often each byte value occurs: h[b] == count(v@, b) for all 256 values b.
//
// REFERENCE
//   let mut h: Vec<u64> = vec![0u64; 256];      // h.len() == 256, all zeros
//   let b = v[i] as usize;  let c = h[b];  h.set(b, c + 1);   // read, then write
//   invariant forall|b: int| 0 <= b < 256 ==> h[b] == count(v@.subrange(0, i as int), b as u8)
//   assert(v@.subrange(0, i + 1).drop_last() =~= v@.subrange(0, i as int));
// NOTE: c + 1 needs a bound on c. A second invariant, h[b] <= i for every b, gives one.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn count(s: Seq<u8>, x: u8) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        count(s.drop_last(), x) + if s.last() == x { 1nat } else { 0nat }
    }
}

fn histogram(v: &Vec<u8>) -> (h: Vec<u64>)
    ensures
        h.len() == 256,
        forall|b: int| 0 <= b < 256 ==> h[b] == count(v@, b as u8),
// END SPEC
{
    Vec::new() // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Start from 256 zeros and bump bucket v[i] for each i. The invariant compares h with the
    counts of the prefix v[..i].
H2. count on the prefix of length i + 1 unfolds to count on the prefix of length i plus one
    0/1 term; Verus needs to see that drop_last of the longer prefix is the shorter one.
    Add `h[b] <= i` for all b so that c + 1 cannot overflow.
H3. invariant h.len() == 256,
              forall|b: int| 0 <= b < 256 ==> h[b] == count(v@.subrange(0, i as int), b as u8),
              forall|b: int| 0 <= b < 256 ==> h[b] <= i,
    body starts with assert(v@.subrange(0, i + 1).drop_last() =~= v@.subrange(0, i as int));
    after the loop: assert(v@.subrange(0, v.len() as int) =~= v@);
*/
