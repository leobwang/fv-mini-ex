// M43 | Bits to number | 10-15 min | Vec<bool>, pow2 bound invariant, by (compute), overflow
// GOAL
//   Interpret b as a binary number, most significant bit first (b[0] is the top bit), and
//   compute its value in a u64. At most 64 bits, so it always fits; prove that it does.
//
// REFERENCE
//   r = 2 * r + if b[i] { 1 } else { 0 };          // Horner step, exec
//   invariant r == bits_val(b@.subrange(0, i as int)), r < pow2(i as nat), ...
//   proof { lemma_pow2_mono(i as nat + 1, 64); }   // call the provided lemma
//   assert(pow2(64) == 0x1_0000_0000_0000_0000) by (compute);   // 2^64
//   assert(b@.subrange(0, i + 1).drop_last() =~= b@.subrange(0, i as int));
// NOTE: r < pow2(i) gives 2 * r + 1 < pow2(i + 1) <= 2^64, i.e. at most u64::MAX.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn pow2(n: nat) -> nat
    decreases n,
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

proof fn lemma_pow2_mono(a: nat, b: nat)
    requires a <= b,
    ensures pow2(a) <= pow2(b),
    decreases b,
{
    if a < b {
        lemma_pow2_mono(a, (b - 1) as nat);
    }
}

spec fn bits_val(s: Seq<bool>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        2 * bits_val(s.drop_last()) + if s.last() { 1nat } else { 0nat }
    }
}

fn from_bits(b: &Vec<bool>) -> (r: u64)
    requires b.len() <= 64,
    ensures r == bits_val(b@),
// END SPEC
{
    0 // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Horner's rule: r = 2r + bit, scanning left to right. bits_val also peels from the right end,
    so the prefix of length i + 1 is the prefix of length i plus one bit.
H2. Carry an invariant r < pow2(i). Then 2r + 1 < pow2(i + 1), and pow2(i + 1) <= pow2(64) = 2^64
    by the monotonicity lemma and a computed constant.
H3. invariant b.len() <= 64, r == bits_val(b@.subrange(0, i as int)), r < pow2(i as nat)
    body: assert(b@.subrange(0, i + 1).drop_last() =~= b@.subrange(0, i as int));
          proof { lemma_pow2_mono(i as nat + 1, 64);
                  assert(pow2(64) == 0x1_0000_0000_0000_0000) by (compute); }
*/
