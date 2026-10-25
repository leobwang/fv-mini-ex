// E03 | Min as a function | 1-3 min | function, if-then-else expression
// GOAL
//   Write the body of the function Min (an expression, not statements), then use it in Min3.
//
// REFERENCE
//   function F(x: int): int { x + 1 }           // body is a single expression
//   function G(x: int): int ensures G(x) > x { x + 1 }  // functions can have ensures too
//   if x < y then x else y                      // conditional *expression* (needs both arms)
//   // Functions may appear in specs; methods may not. Dafny 4 also compiles functions,
//   // so code can call them: m := F(3);

// BEGIN SPEC
function Min(a: int, b: int): int
  ensures Min(a, b) <= a && Min(a, b) <= b
  ensures Min(a, b) == a || Min(a, b) == b
// END SPEC
{
  0 // TODO
}

// BEGIN SPEC
method Min3(a: int, b: int, c: int) returns (m: int)
  ensures m == Min(a, Min(b, c))
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A function body is one expression. Statements like "m := ..." are not allowed there.
H2. Use the conditional expression. For Min3 any grouping works: the verifier sees Min's body.
H3. if a <= b then a else b      and      m := Min(Min(a, b), c);
*/
