// E39 | Double every element | 2-3 min | spec closures, map_values
// GOAL
//   Return a Vec with every element of v doubled (widened to u64).
//
// REFERENCE
//   |x: u32| (2 * x) as u64              // spec closure (type the parameter)
//   s.map_values(f)                      // Seq with f applied to every element
//   s.subrange(0, i as int).map_values(f) // a prefix, mapped: handy in an invariant
//   (2 * x) as u64                        // spec arithmetic is int; cast back to the element type

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn double_all(v: &Vec<u32>) -> (r: Vec<u64>)
    ensures r@ == v@.map_values(|x: u32| (2 * x) as u64),
// END SPEC
{
    let mut r: Vec<u64> = Vec::new();
    for i in 0..v.len()
        invariant r@ == v@.subrange(0, i as int).map_values(|x: u32| (2 * x) as u64),
    {
        r.push(2 * (v[i] as u64));
    }
    r
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Same shape as E19: push one element per iteration.
H2. Widen before multiplying so 2 * x cannot overflow.
H3. invariant r@ == v@.subrange(0, i as int).map_values(|x: u32| (2 * x) as u64),  body: r.push(2 * (v[i] as u64));
*/
