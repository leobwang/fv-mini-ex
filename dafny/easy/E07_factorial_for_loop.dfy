// E07 | Factorial by for-loop | 2-3 min | for loop
// GOAL
//   Compute Fact(n) with a for-loop.
//
// REFERENCE
//   for i := lo to hi                   // i takes lo, lo+1, ..., hi-1 (hi excluded)
//     invariant P(i)                    // at the loop head lo <= i <= hi holds automatically
//   { ... }                             // the body cannot assign i
//   for i := hi downto lo { ... }       // hi-1 down to lo
//   // No decreases needed: for-loops always terminate.

// BEGIN SPEC
function Fact(n: nat): nat { if n == 0 then 1 else n * Fact(n - 1) }

method ComputeFact(n: nat) returns (f: nat)
  ensures f == Fact(n)
// END SPEC
{
  f := 1;
  var i := 0;
  for i := 1 to n + 1
  invariant 1 <= i <= n + 1
  invariant f == Fact(i - 1)
  {
    f := i * f;
  }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Which range should i run over so that you multiply by 1, 2, ..., n?
H2. Loop i from 1 to n + 1. Before multiplying by i, f should be Fact(i - 1).
H3. f := 1; for i := 1 to n + 1 invariant f == Fact(i - 1) { f := f * i; }
*/
