// E05 | Sum of a range | 2-3 min | recursive function, decreases
// GOAL
//   Define SumRange(lo, hi) = lo + (lo+1) + ... + (hi-1) recursively (0 if lo >= hi).
//   Dafny must see that the recursion terminates: give a decreases clause.
//
// REFERENCE
//   function F(n: nat): nat { if n == 0 then 0 else F(n - 1) }  // decreases n is guessed
//   function G(i: int, n: int): int
//     decreases n - i                     // goes between the signature and the body
//   { if i >= n then 0 else G(i + 1, n) }
//   // The default guess is "parameters in order" (here lo, then hi); lo grows, so it fails.

// BEGIN SPEC
function SumRange(lo: int, hi: int): int
// END SPEC
{
  0 // TODO
}

// BEGIN SPEC
lemma SumRangeTests()
  ensures SumRange(0, 5) == 10 && SumRange(-3, 1) == -6
  ensures SumRange(4, 4) == 0 && SumRange(5, 2) == 0
{}
// END SPEC

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Recurse on lo + 1. What quantity shrinks with each call, and is bounded below?
H2. The distance hi - lo shrinks by one per call; when it is <= 0 the recursion stops.
H3. decreases hi - lo   { if lo >= hi then 0 else lo + SumRange(lo + 1, hi) }
*/
