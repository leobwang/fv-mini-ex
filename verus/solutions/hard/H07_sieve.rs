// H07 | Sieve of Eratosthenes | 1-2 h | nested loops, divides via exists, choose, nonlinear_arith, ghost counter
// GOAL
//   Return r with r.len() == n + 1 and r[m] <==> m is prime, by the sieve: start with
//   "every m >= 2 is a candidate", and for each i still marked, clear 2i, 3i, ... <= n.
//
// REFERENCE
//   let k = choose|k: int| #[trigger] (k * d) == m;    // the witness inside divides(d, m)
//   assert(divides(d, m)) by { assert(k * d == m); }    // prove divides: mention the witness term
//   assert(a * c <= b * c) by (nonlinear_arith) requires a <= b, c > 0;
//   assert forall|m: int| P(m) implies Q(m) by { .. }   // prove a forall one m at a time
//   forall|m: int| 0 <= m <= n ==> #[trigger] r[m] == f(m)  // trigger on r[m], not on f(m)
//   let ghost mut kj: int = 2;   proof { kj = kj + 1; } // ghost loop counter (j == kj * i)
//   let ghost r0 = r@;                                  // snapshot before r.set(j, false)
//   invariant old(r).len() == n + 1,                    // loops see only their invariant
// NOTE: marking starts at 2*i (not i*i), so no "smallest factor <= sqrt(m)" argument is needed.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn divides(d: int, m: int) -> bool {
    exists|k: int| #[trigger] (k * d) == m
}

spec fn is_prime(m: int) -> bool {
    m >= 2 && forall|d: int| 2 <= d < m ==> !#[trigger] divides(d, m)
}
// END SPEC

// MILESTONE (optional: change or delete)
// The outer-loop invariant: r[m] == no_div_below(m, i).
spec fn no_div_below(m: int, i: int) -> bool {
    m >= 2 && forall|d: int| 2 <= d < i && d < m ==> !#[trigger] divides(d, m)
}

// MILESTONE (optional: change or delete)
proof fn lemma_divides_trans(a: int, b: int, c: int)
    requires divides(a, b), divides(b, c),
    ensures divides(a, c),
{
    let k1 = choose|k: int| #[trigger] (k * a) == b;
    let k2 = choose|k: int| #[trigger] (k * b) == c;
    assert((k2 * k1) * a == c) by (nonlinear_arith)
        requires k1 * a == b, k2 * b == c;
}

// MILESTONE (optional: change or delete)
proof fn lemma_no_multiple_between(i: int, kj: int, m: int)
    requires i > 0, kj * i < m < (kj + 1) * i,
    ensures !divides(i, m),
{
    assert forall|k: int| #[trigger] (k * i) != m by {
        if k <= kj {
            assert(k * i <= kj * i) by (nonlinear_arith) requires k <= kj, i > 0;
        } else {
            assert(k * i >= (kj + 1) * i) by (nonlinear_arith) requires k >= kj + 1, i > 0;
        }
    }
}

// MILESTONE (optional: change or delete)
// Clear every multiple 2i, 3i, ... <= n.
fn mark_multiples(r: &mut Vec<bool>, i: usize, n: usize)
    requires old(r).len() == n + 1, 2 <= i <= n, n < 1_000_000,
    ensures
        final(r).len() == n + 1,
        forall|m: int| 0 <= m <= n ==>
            #[trigger] final(r)[m] == (old(r)[m] && !(i < m && divides(i as int, m))),
{
    let mut j: usize = i + i;
    let ghost mut kj: int = 2;
    assert forall|m: int| i < m < i + i implies !divides(i as int, m) by {
        lemma_no_multiple_between(i as int, 1, m);
    }
    while j <= n
        invariant
            r.len() == n + 1, old(r).len() == n + 1, 2 <= i <= n, n < 1_000_000,
            j == kj * i, kj >= 2, i + i <= j <= n + i,
            forall|m: int| 0 <= m <= n ==> #[trigger] r[m] == (old(r)[m] && !(i < m < j && divides(i as int, m))),
        decreases n + i - j,
    {
        let ghost j0 = j as int;
        let ghost r0 = r@;
        r.set(j, false);
        proof {
            assert(divides(i as int, j0)) by { assert(kj * i == j0); }
            assert((kj + 1) * i == kj * i + i) by (nonlinear_arith);
            assert forall|m: int| j0 < m < j0 + i implies !divides(i as int, m) by {
                lemma_no_multiple_between(i as int, kj, m);
            }
            kj = kj + 1;
        }
        j = j + i;
        assert forall|m: int| 0 <= m <= n implies #[trigger] r[m] == (old(r)[m] && !(i < m < j && divides(i as int, m))) by {
            if m == j0 {
            } else {
                assert(r[m] == r0[m]);
                if j0 < m < j {
                    assert(!divides(i as int, m));
                }
            }
        }
    }
}

// BEGIN SPEC
fn sieve(n: usize) -> (r: Vec<bool>)
    requires n < 1_000_000,
    ensures
        r.len() == n + 1,
        forall|m: int| 0 <= m <= n ==> #[trigger] r[m] == is_prime(m),
// END SPEC
{
    let mut r: Vec<bool> = Vec::new();
    for m in 0..n + 1
        invariant r.len() == m, forall|x: int| 0 <= x < m ==> r[x] == (x >= 2),
    {
        r.push(m >= 2);
    }
    let mut i: usize = 2;
    while i <= n
        invariant
            n < 1_000_000, 2 <= i <= n + 2, r.len() == n + 1,
            forall|m: int| 0 <= m <= n ==> #[trigger] r[m] == no_div_below(m, i as int),
        decreases n + 1 - i,
    {
        if r[i] {
            mark_multiples(&mut r, i, n);
        } else {
            proof {
                let d = choose|d: int| 2 <= d < i && d < i && #[trigger] divides(d, i as int);
                assert forall|m: int| 0 <= m <= n && i < m && divides(i as int, m) implies !no_div_below(m, i as int) by {
                    lemma_divides_trans(d, i as int, m);
                }
            }
        }
        assert forall|m: int| 0 <= m <= n implies r[m] == no_div_below(m, i + 1) by {
            assert(no_div_below(m, i + 1) == (no_div_below(m, i as int) && !(i < m && divides(i as int, m))));
        }
        i = i + 1;
    }
    proof {
        assert forall|m: int| 0 <= m <= n implies r[m] == is_prime(m) by {
            assert(no_div_below(m, i as int) == is_prime(m));
        }
    }
    r
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Outer loop over i = 2..=n with invariant  r[m] == no_div_below(m, i)  for all m <= n.
    Initially (i == 2) that is just m >= 2; at the end (i == n + 1) it is is_prime(m).
H2. If r[i] is true then i is prime: mark_multiples. If r[i] is false, i has a divisor d < i
    (choose it); any multiple m of i is a multiple of d (lemma_divides_trans), so r[m] is
    already false. Either way no_div_below(m, i + 1) == no_div_below(m, i) && !(i < m && divides(i, m)).
H3. mark_multiples: j = i + i, ghost kj = 2, invariant
      j == kj * i, i + i <= j <= n + i, old(r).len() == n + 1,
      forall|m| 0 <= m <= n ==> #[trigger] r[m] == (old(r)[m] && !(i < m < j && divides(i as int, m)))
    Each step: divides(i, j), and lemma_no_multiple_between(i, kj, m) for j < m < j + i
    (also before the loop with kj = 1). lemma_no_multiple_between: assert forall|k| k * i != m,
    splitting k <= kj / k >= kj + 1 with nonlinear_arith.
*/
