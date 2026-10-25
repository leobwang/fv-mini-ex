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
    let mut r: u64 = 1;
    let mut base: u64 = b % m;
    let mut k: u64 = e;
    proof { lemma_pow_mod_noop(b as int, e as nat, m as int); }
    while k > 0
        invariant
            1 < m <= 0xFFFF_FFFF,
            r < m,
            base < m,
            (r * pow(base as int, k as nat)) % (m as int) == pow(b as int, e as nat) % (m as int),
        decreases k,
    {
        let ghost (r0, base0, k0) = (r as int, base as int, k as nat);
        let ghost q = (k0 / 2) as nat;
        let ghost m0 = m as int;
        proof {
            lemma_pow_square(base0, q);
            assert(r0 * base0 < m0 * m0) by (nonlinear_arith) requires 0 <= r0 < m0, 0 <= base0 < m0;
            assert(base0 * base0 < m0 * m0) by (nonlinear_arith) requires 0 <= base0 < m0;
            assert(m0 * m0 <= 0xFFFF_FFFF * 0xFFFF_FFFF) by (nonlinear_arith) requires 0 < m0 <= 0xFFFF_FFFF;
        }
        if k % 2 == 1 {
            r = r * base % m;
        }
        base = base * base % m;
        k = k / 2;
        proof {
            // WHY: first an exact identity r0 * base0^k0 == rr * (base0*base0)^q, then move `% m` around.
            let p = pow(base0 * base0, q);
            let rr: int = if k0 % 2 == 1 { r0 * base0 } else { r0 };
            if k0 % 2 == 1 {
                assert(pow(base0, k0) == base0 * pow(base0, 2 * q));
                assert(r0 * pow(base0, k0) == rr * p) by (nonlinear_arith)
                    requires pow(base0, k0) == base0 * pow(base0, 2 * q), p == pow(base0, 2 * q), rr == r0 * base0;
            } else {
                assert(k0 == 2 * q);
            }
            lemma_mul_mod_noop_left(rr, pow(base as int, q), m0);
            lemma_mul_mod_noop_right(rr, pow(base as int, q), m0);
            lemma_pow_mod_noop(base0 * base0, q, m0);
            lemma_mul_mod_noop_right(rr, p, m0);
            if k0 % 2 == 0 {
                lemma_small_mod(r0 as nat, m0 as nat);
            }
        }
    }
    proof { lemma_small_mod(r as nat, m as nat); }
    r
}

proof fn lemma_pow_square(x: int, k: nat)
    ensures pow(x * x, k) == pow(x, 2 * k),
    decreases k,
{
    if k > 0 {
        lemma_pow_square(x, (k - 1) as nat);
        assert(pow(x, (2 * k - 1) as nat) == x * pow(x, (2 * k - 2) as nat));
        assert(pow(x, 2 * k) == x * (x * pow(x, (2 * k - 2) as nat)));
        assert(x * (x * pow(x, (2 * k - 2) as nat)) == (x * x) * pow(x, (2 * k - 2) as nat))
            by (nonlinear_arith);
    }
}

proof fn lemma_pow_mod_noop(x: int, k: nat, m: int)
    requires m > 0,
    ensures pow(x % m, k) % m == pow(x, k) % m,
    decreases k,
{
    if k > 0 {
        lemma_pow_mod_noop(x, (k - 1) as nat, m);
        let a = pow(x % m, (k - 1) as nat);
        let b = pow(x, (k - 1) as nat);
        // (x%m * a) % m == (x * a) % m == (x * (a % m)) % m == (x * (b % m)) % m == (x * b) % m
        lemma_mul_mod_noop_left(x, a, m);
        lemma_mul_mod_noop_right(x, a, m);
        lemma_mul_mod_noop_right(x, b, m);
    }
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
