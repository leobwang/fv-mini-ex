// M21 | Loop isolation | 5-10 min | #[verifier::loop_isolation(false)], nonlinear bound
// GOAL
//   Compute r[i] = a * x[i] + y[i]. The loop body needs every precondition. Instead of copying
//   them all into the invariant, turn off loop isolation so the loop sees the facts that hold
//   before it (facts about variables the loop does not modify stay true).
//
// REFERENCE
//   #[verifier::loop_isolation(false)]   // attribute on the fn (above `fn`, outside the spec)
//   fn f(..) requires P, { while .. invariant Inv, { /* P visible here too */ } }
//   let xi = x[i];   assert(a * xi <= 1_000_000) by (nonlinear_arith) requires a <= 1000, xi <= 1000;
// NOTE: without the attribute a loop sees ONLY its invariant (the default, loop_isolation(true)).

use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
// BEGIN SPEC
fn axpy(a: u64, x: &Vec<u64>, y: &Vec<u64>) -> (r: Vec<u64>)
    requires
        x.len() == y.len(),
        a <= 1000,
        forall|i: int| 0 <= i < x.len() ==> x[i] <= 1000,
        forall|i: int| 0 <= i < y.len() ==> y[i] <= 1_000_000,
    ensures
        r.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> r[i] == a * x[i] + y[i],
// END SPEC
{
    let mut r: Vec<u64> = Vec::new();
    for i in 0..x.len()
        invariant
            r.len() == i,
            forall|k: int| 0 <= k < i ==> r[k] == a * x[k] + y[k],
    {
        let xi = x[i];
        assert(a * xi <= 1_000_000) by (nonlinear_arith) requires a <= 1000, xi <= 1000;
        r.push(a * xi + y[i]);
    }
    r
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Build r with push in a for loop over 0..x.len().
H2. Put #[verifier::loop_isolation(false)] above `fn axpy`; then the invariant only needs to
    talk about r. The product a * x[i] still needs a nonlinear bound to rule out overflow.
H3. invariant r.len() == i, forall|k: int| 0 <= k < i ==> r[k] == a * x[k] + y[k],
    body: let xi = x[i];
          assert(a * xi <= 1_000_000) by (nonlinear_arith) requires a <= 1000, xi <= 1000;
*/
