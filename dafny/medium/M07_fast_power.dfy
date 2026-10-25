// M07 | Fast exponentiation | 15-20 min | invariant, helper lemma, nonlinear [R11]
// GOAL
//   Compute Pow(b, e) by repeated squaring (O(log e) multiplications).
//
// REFERENCE
//   invariant r * Pow(x, n) == Pow(b, e)     // "accumulated * remaining == answer"
//   lemma L(x: int, k: nat) ensures Pow(x * x, k) == Pow(x, 2 * k)   // state helpers like this
//   n % 2 == 0    n / 2                       // parity and halving
//   assert r * (x * P) == (r * x) * P;        // associativity: nonlinear steps may need an assert
// NOTE: e has type nat, so e - 1 is only allowed when e > 0.

// BEGIN SPEC
function Pow(b: int, e: nat): int { if e == 0 then 1 else b * Pow(b, e - 1) }

method FastPow(b: int, e: nat) returns (r: int)
  ensures r == Pow(b, e)
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Odd n: move one factor x into r. Even n: square x and halve n.
H2. The invariant r * Pow(x, n) == Pow(b, e) survives the even step only if
    Pow(x * x, n / 2) == Pow(x, n): prove that as a lemma by induction on n / 2.
H3. lemma PowSquare(x: int, k: nat) ensures Pow(x * x, k) == Pow(x, 2 * k)
    (inductive step: unfold Pow(x, 2 * k) twice: assert Pow(x, 2*k) == x * (x * Pow(x, 2*k - 2));)
*/
