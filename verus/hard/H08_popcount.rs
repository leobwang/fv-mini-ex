// H08 | Popcount (Kernighan) | 45-90 min | by (bit_vector), sub, induction on x / 2, decreases
// GOAL
//   popcount(x) counts the 1 bits of x (spec below). Prove Kernighan's fact: clearing the lowest
//   set bit, x & (x - 1), lowers the popcount by exactly one. Then use it for a loop that counts
//   bits by repeatedly clearing the lowest one, and for an O(1) power-of-two test.
//
// REFERENCE
//   sub(y, 1)                          // fixed-width y - 1 (stays u64); `y - 1` in specs is an int
//   assert(y & sub(y, 1) < y) by (bit_vector) requires y != 0;   // a bit-level fact about u64
//   assert(P) by (bit_vector) requires y % 2 == 0, y != 0;       // & | ^ >> << and % / by 2 work
//   // bit_vector sees ONLY its requires: no spec fns, no surrounding facts
//   if y % 2 == 0 { lemma(y / 2); }    // induction on the shifted value (decreases y)
//   (x % 2) as nat + popcount(x / 2)   // how the spec peels off the lowest bit
// NOTE: `y - 1` in exec code is checked for underflow; in a proof write sub(y, 1) to stay in u64.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn popcount(x: u64) -> nat
    decreases x,
{
    if x == 0 { 0 } else { (x % 2) as nat + popcount(x / 2) }
}

proof fn lemma_kernighan(y: u64)
    requires y != 0,
    ensures popcount(y & sub(y, 1)) + 1 == popcount(y),
    decreases y,
// END SPEC
{
}

// MILESTONE (optional: change or delete)
proof fn lemma_odd(y: u64)
    requires y % 2 == 1,
    ensures y & sub(y, 1) == sub(y, 1), sub(y, 1) / 2 == y / 2, sub(y, 1) % 2 == 0,
{
}

// MILESTONE (optional: change or delete)
proof fn lemma_even(y: u64)
    requires y % 2 == 0, y != 0,
    ensures (y & sub(y, 1)) % 2 == 0, (y & sub(y, 1)) / 2 == (y / 2) & sub(y / 2, 1),
{
}

// MILESTONE (optional: change or delete)
proof fn lemma_popcount_le(x: u64)
    ensures popcount(x) <= x,
    decreases x,
{
}

// MILESTONE (optional: change or delete)
proof fn lemma_popcount_zero(x: u64)
    ensures popcount(x) == 0 <==> x == 0,
    decreases x,
{
}

// BEGIN SPEC
fn popcount_loop(x: u64) -> (r: u64)
    ensures r == popcount(x),
// END SPEC
{
    0 // TODO
}

// BEGIN SPEC
fn is_pow2(x: u64) -> (b: bool)
    ensures b == (popcount(x) == 1),
// END SPEC
{
    false // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Split lemma_kernighan on the lowest bit. Odd y: y & (y-1) is just y-1, which has the same
    upper bits (y-1)/2 == y/2. Even y: the lowest bit of y & (y-1) is 0 and its upper bits are
    (y/2) & (y/2 - 1), so the induction hypothesis on y / 2 applies.
H2. The bit facts are the milestones lemma_odd / lemma_even, each a single `by (bit_vector)` assert
    with the lemma's requires repeated. In lemma_kernighan, popcount needs one manual unfolding
    for the cases where a value is 0 (fuel is 1). popcount_loop: y = y & (y - 1) until 0, with
    invariant c + popcount(y) == popcount(x); lemma_popcount_le bounds c so c + 1 cannot overflow.
H3. Even case:
      lemma_even(y); lemma_kernighan(y / 2);
      if y & sub(y, 1) == 0 { assert(popcount((y / 2) & sub(y / 2, 1)) == 0); }
    is_pow2: x != 0 && x & (x - 1) == 0, after lemma_kernighan(x); lemma_popcount_zero(x & sub(x, 1));
*/
