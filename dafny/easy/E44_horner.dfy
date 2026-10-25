// E44 | Horner's rule | 2-3 min | for downto
// GOAL
//   Evaluate a polynomial (coefficients c[0] + c[1] x + c[2] x^2 + ...) right to left.
//
// REFERENCE
//   for i := hi downto lo                // i takes hi-1, ..., lo
//     invariant P(i)                     // at the loop head, i is the last index processed
//   { ... }                              // (i == hi before the first iteration, lo at exit)
//   s[i..]                               // suffix starting at i; s[|s|..] == []

// BEGIN SPEC
function Eval(c: seq<int>, x: int): int
{
  if |c| == 0 then 0 else c[0] + x * Eval(c[1..], x)
}

method Horner(c: seq<int>, x: int) returns (r: int)
  ensures r == Eval(c, x)
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Start from the highest coefficient. What does r represent after processing c[i..]?
H2. r is the value of the suffix polynomial c[i..]; prepending c[i] means r := c[i] + x * r.
H3. for i := |c| downto 0 invariant r == Eval(c[i..], x) { r := r * x + c[i]; }
*/
