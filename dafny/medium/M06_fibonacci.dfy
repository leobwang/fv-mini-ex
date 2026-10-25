// M06 | Fibonacci | 5-8 min | two-variable invariant [R10]
// GOAL
//   Compute Fib(n) iteratively in O(n) (the recursive spec is exponential).
//
// REFERENCE
//   x, y := y, x + y;                    // simultaneous update
//   invariant x == F(i) && y == F(i + 1) // track two consecutive values
//   for i := 0 to n { ... }

// BEGIN SPEC
function Fib(n: nat): nat { if n < 2 then n else Fib(n - 1) + Fib(n - 2) }

method ComputeFib(n: nat) returns (f: nat)
  ensures f == Fib(n)
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Keep the last two Fibonacci numbers.
H2. After i iterations, x and y should be Fib(i) and Fib(i + 1).
H3. var x, y := 0, 1; for i := 0 to n invariant x == Fib(i) && y == Fib(i + 1) { x, y := y, x + y; }
*/
