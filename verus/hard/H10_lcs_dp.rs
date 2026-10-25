// H10 | LCS length by DP | 45-90 min | recursive spec on prefixes, decreases i + j, rolling rows, table invariant
// GOAL
//   lcs(a, b, i, j) is the length of a longest common subsequence of a[..i] and b[..j] (spec below).
//   Compute lcs(a@, b@, a.len(), b.len()) bottom-up, keeping only one row of the DP table at a time
//   (O(|b|) memory): row i is computed from row i - 1.
//
// REFERENCE
//   spec fn f(i: nat, j: nat) -> nat decreases i + j, { .. }   // measure for two-argument recursion
//   (i - 1) as nat                          // nat subtraction must be cast back to nat
//   for j in 1..b.len() + 1 invariant cur.len() == j, { cur.push(x); }
//   forall|k: int| 0 <= k <= b.len() ==> #[trigger] prev[k] == lcs(a@, b@, i as nat, k as nat)
//   prev = next_row(a, b, &prev, i);        // replace the whole row
//   proof { lemma_lcs_le(a@, b@, i as nat, j as nat); }  // bound a value before computing x + 1
//   let x = if p >= q { p } else { q };     // exec max
// NOTE: loops see only their invariants: restate bounds such as b.len() <= 1_000_000 there.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn max(x: nat, y: nat) -> nat {
    if x >= y { x } else { y }
}

spec fn lcs(a: Seq<u8>, b: Seq<u8>, i: nat, j: nat) -> nat
    decreases i + j,
{
    if i == 0 || j == 0 {
        0
    } else if a[i - 1] == b[j - 1] {
        lcs(a, b, (i - 1) as nat, (j - 1) as nat) + 1
    } else {
        max(lcs(a, b, (i - 1) as nat, j), lcs(a, b, i, (j - 1) as nat))
    }
}

fn lcs_len(a: &Vec<u8>, b: &Vec<u8>) -> (r: u64)
    requires a.len() <= 1_000_000, b.len() <= 1_000_000,
    ensures r == lcs(a@, b@, a.len() as nat, b.len() as nat),
// END SPEC
{
    0 // TODO
}

// MILESTONE (optional: change or delete)
// Needed so that `prev[j - 1] + 1` cannot overflow.
proof fn lemma_lcs_le(a: Seq<u8>, b: Seq<u8>, i: nat, j: nat)
    ensures lcs(a, b, i, j) <= i,
    decreases i + j,
{
}

// MILESTONE (optional: change or delete)
// One DP step: row i - 1 in, row i out.
fn next_row(a: &Vec<u8>, b: &Vec<u8>, prev: &Vec<u64>, i: usize) -> (cur: Vec<u64>)
    requires
        1 <= i <= a.len(), prev.len() == b.len() + 1,
        forall|j: int| 0 <= j <= b.len() ==>
            #[trigger] prev[j] == lcs(a@, b@, (i - 1) as nat, j as nat),
    ensures
        cur.len() == b.len() + 1,
        forall|j: int| 0 <= j <= b.len() ==> #[trigger] cur[j] == lcs(a@, b@, i as nat, j as nat),
{
    Vec::new() // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Row 0 is all zeros. Row i, column j only needs prev[j - 1], prev[j] (row i - 1) and cur[j - 1]
    (the entry just computed), exactly the three recursive calls in lcs.
H2. lcs_len: build row 0 with a push loop, then `for i in 1..a.len() + 1` replace prev by
    next_row(..), invariant prev.len() == b.len() + 1 and prev[k] == lcs(.., (i - 1) as nat, k).
    Answer: prev[b.len()]. lemma_lcs_le: induction with `decreases i + j`, calling itself on the
    three smaller argument pairs whenever i > 0 && j > 0.
H3. next_row: cur = [0], then for j in 1..b.len() + 1 with invariant cur.len() == j,
    forall|k: int| 0 <= k < j ==> #[trigger] cur[k] == lcs(a@, b@, i as nat, k as nat), plus prev's facts.
    Body: if a[i - 1] == b[j - 1] { lemma_lcs_le(.., (i - 1) as nat, (j - 1) as nat); push prev[j - 1] + 1 }
    else { push max(prev[j], cur[j - 1]) }.
*/
