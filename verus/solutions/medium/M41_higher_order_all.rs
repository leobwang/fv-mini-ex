// M41 | Higher-order all-satisfy | 10-15 min | closures, f.requires, f.ensures, closure contracts
// GOAL
//   all_satisfy(v, f) runs the predicate f on every element and reports whether all returned true.
//   Its spec talks about f only through f.requires / f.ensures. Then use it with a closure.
//
// REFERENCE
//   fn g<F: Fn(u64) -> bool>(f: F)                 // exec closure parameter
//   f.requires((x,))   f.ensures((x,), b)          // spec: may call f on x / f(x) may return b
//   let b = f(v[i]);                               // calling f needs f.requires((v[i],))
//   |x: u64| -> (r: bool) ensures r == (x < 10) { x < 10 }   // closure with a contract
//   // f.ensures is a relation: knowing f.ensures((x,), false) does NOT rule out ensures(.., true)
//   //   in general, which is why the spec has a separate witness clause for false.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn all_satisfy<F: Fn(u64) -> bool>(v: &Vec<u64>, f: F) -> (b: bool)
    requires forall|x: u64| #[trigger] f.requires((x,)),
    ensures
        b ==> forall|i: int| 0 <= i < v.len() ==> f.ensures((v[i],), true),
        !b ==> exists|i: int| 0 <= i < v.len() && f.ensures((v[i],), false),
// END SPEC
{
    for i in 0..v.len()
        invariant
            forall|x: u64| #[trigger] f.requires((x,)),
            forall|j: int| 0 <= j < i ==> #[trigger] f.ensures((v[j],), true),
    {
        if !f(v[i]) {
            return false;
        }
    }
    true
}

// BEGIN SPEC
fn all_small(v: &Vec<u64>) -> (b: bool)
    ensures b <==> forall|i: int| 0 <= i < v.len() ==> v[i] < 10,
// END SPEC
{
    all_satisfy(v, |x: u64| -> (r: bool) ensures r == (x < 10) { x < 10 })
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. all_satisfy is a plain loop with an early `return false`. The interesting part is the spec
    vocabulary: after `let r = f(x);` Verus knows f.ensures((x,), r).
H2. The loop invariant must restate the requires about f (loops don't see it otherwise) and say
    that f returned true on all earlier elements. For all_small, pass a closure whose own ensures
    clause pins its result, so f.ensures((x,), b) becomes b == (x < 10).
H3. invariant forall|x: u64| #[trigger] f.requires((x,)),
              forall|j: int| 0 <= j < i ==> #[trigger] f.ensures((v[j],), true),
    all_small:  all_satisfy(v, |x: u64| -> (r: bool) ensures r == (x < 10) { x < 10 })
*/
