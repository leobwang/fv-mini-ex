// M04 | Count occurrences | 10-15 min | recursive spec on Seq, subrange invariant, =~= [R06]
// GOAL
//   Count how many times x occurs in v; the result must equal the recursive spec count.
//
// REFERENCE
//   s.drop_last()   s.last()          // s without its last element; the last element
//   v@.subrange(0, i as int)          // the prefix v[0..i) as a Seq
//   assert(v@.subrange(0, i + 1).drop_last() =~= v@.subrange(0, i as int));
//       // =~= proves two sequences equal element-wise; needed when they sit inside a spec call
//   for i in 0..v.len() invariant c == count(v@.subrange(0, i as int), x), { ... }

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn count(s: Seq<i64>, x: i64) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        count(s.drop_last(), x) + if s.last() == x { 1nat } else { 0nat }
    }
}

fn count_occurrences(v: &Vec<i64>, x: i64) -> (r: usize)
    ensures r == count(v@, x),
// END SPEC
{
    let mut c: usize = 0;
    for i in 0..v.len()
        invariant
            c <= i,
            c == count(v@.subrange(0, i as int), x),
    {
        assert(v@.subrange(0, i + 1).drop_last() =~= v@.subrange(0, i as int));
        if v[i] == x {
            c += 1;
        }
    }
    assert(v@.subrange(0, v.len() as int) =~= v@);
    c
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. count peels elements off the END, so grow a prefix v[0..i) and add v[i] at each step.
H2. Invariant: c == count of the prefix (plus c <= i for overflow). Verus will not unfold
    count(prefix of length i + 1) into count(prefix of length i) unless it knows the
    drop_last of the longer prefix IS the shorter one: assert that with =~=.
H3. In the body: assert(v@.subrange(0, i + 1).drop_last() =~= v@.subrange(0, i as int));
    After the loop: assert(v@.subrange(0, v.len() as int) =~= v@);
*/
