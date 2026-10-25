// M38 | Filter evens | 10-15 min | Seq::filter (opaque), reveal, subrange invariant
// GOAL
//   Return the even elements of v, in order. The spec uses vstd's Seq::filter.
//
// REFERENCE
//   s.filter(|x: u64| x % 2 == 0)        // spec closure as the predicate
//   reveal(Seq::filter);                  // filter is opaque: reveal its recursive definition
//   // unfolded: s.filter(p) is s.drop_last().filter(p), then .push(s.last()) if p(s.last())
//   assert(v@.subrange(0, i + 1).drop_last() =~= v@.subrange(0, i as int));
//   invariant r@ == v@.subrange(0, i as int).filter(|x: u64| x % 2 == 0)
// NOTE: write the same closure text in your invariant as in the spec.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn evens(v: &Vec<u64>) -> (r: Vec<u64>)
    ensures r@ == v@.filter(|x: u64| x % 2 == 0),
// END SPEC
{
    let mut r: Vec<u64> = Vec::new();
    for i in 0..v.len()
        invariant r@ == v@.subrange(0, i as int).filter(|x: u64| x % 2 == 0),
    {
        proof {
            reveal(Seq::filter);
            assert(v@.subrange(0, i + 1).drop_last() =~= v@.subrange(0, i as int));
        }
        if v[i] % 2 == 0 {
            r.push(v[i]);
        }
    }
    assert(v@.subrange(0, v.len() as int) =~= v@);
    r
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Loop over v and push the even elements. The invariant: r is the filter of the prefix v[..i].
H2. filter is defined by peeling off the last element, and it is opaque. In each iteration reveal
    it and show that the prefix of length i + 1, minus its last element, is the prefix of length i.
H3. invariant r@ == v@.subrange(0, i as int).filter(|x: u64| x % 2 == 0),
    body:  proof { reveal(Seq::filter);
                   assert(v@.subrange(0, i + 1).drop_last() =~= v@.subrange(0, i as int)); }
    after: assert(v@.subrange(0, v.len() as int) =~= v@);
*/
