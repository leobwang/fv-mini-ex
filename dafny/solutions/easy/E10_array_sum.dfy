// E10 | Array sum | 2-3 min | reads, function over array
// GOAL
//   SumUpTo reads the array but has no reads clause yet: add it (one line between the two
//   spec regions). Then implement ArraySum with a loop.
//
// REFERENCE
//   function F(a: array<int>): int
//     reads a                           // functions must declare the heap objects they read
//   { if a.Length == 0 then 0 else a[0] }
//   // Methods need no reads clause; they only declare what they *modify*.
//   // Clauses (requires/reads/decreases) may appear in any order.

// BEGIN SPEC
function SumUpTo(a: array<int>, n: int): int
  requires 0 <= n <= a.Length
// END SPEC
  reads a
// BEGIN SPEC
  decreases n
{
  if n == 0 then 0 else SumUpTo(a, n - 1) + a[n - 1]
}

method ArraySum(a: array<int>) returns (s: int)
  ensures s == SumUpTo(a, a.Length)
// END SPEC
{
  s := 0;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant s == SumUpTo(a, i)
  {
    s := s + a[i];
    i := i + 1;
  }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The error "insufficient reads clause" points at a[n - 1]. Which object is being read?
H2. reads a. Then the loop accumulates left to right, matching how SumUpTo unfolds.
H3. invariant 0 <= i <= a.Length   invariant s == SumUpTo(a, i)
*/
