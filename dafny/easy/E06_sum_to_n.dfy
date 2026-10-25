// E06 | Sum 0..n by loop | 2-3 min | while, invariant, decreases [R03]
// GOAL
//   Compute 0 + 1 + ... + n with a while loop and prove it equals n(n+1)/2.
//
// REFERENCE
//   var i := 0;
//   while i < n
//     invariant 0 <= i <= n             // must hold before the loop and after every iteration
//     invariant s == i * (i + 1) / 2    // the loop's "meaning so far"
//     decreases n - i                   // termination measure (often guessed for i < n)
//   { i := i + 1; s := s + i; }
//   // After the loop the verifier knows only: the invariants and the negated guard.

// BEGIN SPEC
method SumTo(n: nat) returns (s: nat)
  ensures s == n * (n + 1) / 2
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Keep a counter i and an accumulator s; relate them with an invariant.
H2. You need two invariants: a range for i (so i == n at exit) and the closed form for s.
H3. invariant 0 <= i <= n   invariant s == i * (i + 1) / 2   body: i := i + 1; s := s + i;
*/
