// E01 | Absolute value | 1-3 min | method, ensures, if [R01]
// GOAL
//   Implement Abs so the verifier proves both postconditions.
//
// REFERENCE
//   method M(x: int) returns (y: int)   // out-parameter y is the result
//     requires P                         // precondition (caller must prove)
//     ensures Q                          // postcondition (you must prove); may mention x and y
//   { y := e; }                          // assign the out-parameter
//   if c { ... } else { ... }            // braces required, no parens needed
//   Operators: && || ! ==> <==>  == !=  < <= .  `int` is unbounded.

// BEGIN SPEC
method Abs(x: int) returns (y: int)
  ensures y >= 0
  ensures y == x || y == -x
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Split on the sign of x.
H2. Each branch assigns y once; the verifier checks both postconditions per branch.
H3. if x < 0 { y := -x; } else { y := x; }
*/
