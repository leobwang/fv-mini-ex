// M08 | Integer square root | 5-10 min | nonlinear loop invariant [R12]
// GOAL
//   Compute floor(sqrt(n)).
//
// REFERENCE
//   while (r + 1) * (r + 1) <= n        // guard may be any expression
//     invariant r * r <= n
//   // Termination: Dafny guesses "n - (r+1)*(r+1)" from the guard, which decreases here.
//   // Optional stretch: binary search on [0, n + 1) for O(log n) steps.

// BEGIN SPEC
method ISqrt(n: nat) returns (r: nat)
  ensures r * r <= n < (r + 1) * (r + 1)
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Start at 0 and increase r while the next square still fits.
H2. The guard gives the upper half of the postcondition at exit; the invariant the lower half.
H3. r := 0; while (r + 1) * (r + 1) <= n invariant r * r <= n { r := r + 1; }
*/
