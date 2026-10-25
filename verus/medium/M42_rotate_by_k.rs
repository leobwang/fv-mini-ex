// M42 | Rotate by k | 15-20 min | % indexing, usize vs int, vstd div_mod lemmas
// GOAL
//   Return the left rotation of v by k: r[i] == v[(i + k) % n]. k may be huge (any usize),
//   so compute indices without overflowing.
//
// REFERENCE
//   use vstd::arithmetic::div_mod::*;              // before verus! { }
//   lemma_add_mod_noop_right(x, y, m);  // m > 0 ==> (x + (y % m)) % m == (x + y) % m
//   lemma_small_mod(x as nat, m as nat); // x < m ==> x % m == x
//   lemma_mod_sub_multiples_vanish(b, m); // m > 0 ==> (-m + b) % m == b % m
//   lemma_mod_bound(x, m);              // m > 0 ==> 0 <= x % m < m
// NOTE: `i + k` can overflow usize; reduce k modulo n first, and avoid `i + s` when it could exceed n.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;

verus! {

// BEGIN SPEC
fn rotate(v: &Vec<u64>, k: usize) -> (r: Vec<u64>)
    requires v.len() > 0,
    ensures
        r.len() == v.len(),
        forall|i: int| 0 <= i < v.len() ==> r[i] == v[(i + k) % (v.len() as int)],
// END SPEC
{
    Vec::new() // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Let s = k % n. Then (i + k) % n == (i + s) % n, and since i, s < n, that is either i + s
    or i + s - n.
H2. Exec: idx = if i < n - s { i + s } else { i - (n - s) } never overflows. Proof: one lemma
    replaces k by k % n inside the mod, then one of two cases shows (i + s) % n == idx.
H3. proof { lemma_add_mod_noop_right(i as int, k as int, n as int);
            if i < n - s { lemma_small_mod((i + s) as nat, n as nat); }
            else { lemma_mod_sub_multiples_vanish(i + s, n as int);
                   lemma_small_mod((i + s - n) as nat, n as nat); } }
    invariant also needs  s == k % n, s < n  (get s < n from lemma_mod_bound before the loop).
*/
