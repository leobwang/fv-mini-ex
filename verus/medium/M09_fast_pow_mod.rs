// M09 | Fast modular exponentiation | 15-20 min | squaring loop, pow spec, vstd mod lemmas [R11]
// GOAL
//   Compute b^e mod m in O(log e) multiplications by repeated squaring. Since m <= 2^32 - 1,
//   every product of two residues fits in u64 (Verus adaptation of R11: overflow stays honest).
//
// REFERENCE
//   use vstd::arithmetic::div_mod::*;
//   lemma_mul_mod_noop_left(x, y, m);    // requires 0 < m; ensures (x % m) * y % m == x * y % m
//   lemma_mul_mod_noop_right(x, y, m);   // requires 0 < m; ensures x * (y % m) % m == x * y % m
//   proof fn lemma_pow_square(x: int, k: nat) ensures pow(x * x, k) == pow(x, 2 * k) decreases k
//   assert(a * (b * c) == (a * b) * c) by (nonlinear_arith);   // reassociate products
//   invariant (r * pow(base as int, k as nat)) % (m as int) == pow(b as int, e as nat) % (m as int),
// NOTE: vstd's own `pow` is opaque; this file defines its own `pow` below.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;

verus! {

// BEGIN SPEC
spec fn pow(x: int, k: nat) -> int
    decreases k,
{
    if k == 0 { 1 } else { x * pow(x, (k - 1) as nat) }
}

fn pow_mod(b: u64, e: u64, m: u64) -> (r: u64)
    requires 1 < m <= 0xFFFF_FFFF,
    ensures r == pow(b as int, e as nat) % (m as int),
// END SPEC
{
    0 // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Loop on k = e, e/2, e/4, ...; keep r and base reduced mod m. The invariant says the
    product r * base^k is congruent (mod m) to the answer.
H2. Two helper lemmas by induction on k: pow(x*x, k) == pow(x, 2k), and
    pow(x % m, k) % m == pow(x, k) % m (use the mul_mod_noop lemmas). In the loop, show
    r*base^k == R * (base*base)^(k/2) exactly (R = r*base if k odd, else r), then move the
    `% m` reductions in and out with the noop lemmas. Products stay < m*m <= (2^32-1)^2.
H3. invariant 1 < m <= 0xFFFF_FFFF, r < m, base < m,
        (r * pow(base as int, k as nat)) % (m as int) == pow(b as int, e as nat) % (m as int),
    proof fn lemma_pow_mod_noop(x: int, k: nat, m: int) requires m > 0
        ensures pow(x % m, k) % m == pow(x, k) % m decreases k
*/
