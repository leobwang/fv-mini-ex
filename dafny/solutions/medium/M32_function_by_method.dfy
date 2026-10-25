// M32 | Function by method | 10-12 min | function by method
// GOAL
//   Fib's recursive definition is the spec; its compiled code runs the by method body instead.
//   Write fast by-method bodies for Fib and for SumSquares.
//
// REFERENCE
//   function F(n: nat): nat { <spec expression> }
//   by method { <imperative code> }     // must return exactly F(n): proved like an ensures
//   return x;                           // the by-method body returns the function's value
//   // Callers (and proofs) see only the expression; compiled code runs only the method.

// BEGIN SPEC
function Fib(n: nat): nat
{
  if n < 2 then n else Fib(n - 1) + Fib(n - 2)
}
// END SPEC
by method
{
  var x, y := 0, 1;
  for i := 0 to n
    invariant x == Fib(i) && y == Fib(i + 1)
  {
    x, y := y, x + y;
  }
  return x;
}

// BEGIN SPEC
function SumSquares(n: nat): nat
{
  if n == 0 then 0 else n * n + SumSquares(n - 1)
}
// END SPEC
by method
{
  var s := 0;
  for i := 1 to n + 1
    invariant s == SumSquares(i - 1)
  {
    s := s + i * i;
  }
  return s;
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each by-method body is a loop with the same shape as M06 / E07.
H2. The loop invariant ties a local to the function at the loop index; finish with return.
H3. var x, y := 0, 1; for i := 0 to n invariant x == Fib(i) && y == Fib(i + 1) { ... } return x;
*/
