// E02 | Max of two | 1-3 min | method call, var [R02]
// GOAL
//   Implement Max, then implement Max3 by calling Max (twice).
//
// REFERENCE
//   var m := Max(a, b);                 // call a method, bind its out-parameter
//   var t: int := 0;                    // local variable with an explicit type
//   m := Max(t, c);                     // assign an existing variable from a call
//   // A caller knows only the callee's ensures clauses, never its body.

// BEGIN SPEC
method Max(a: int, b: int) returns (m: int)
  ensures m >= a && m >= b
  ensures m == a || m == b
// END SPEC
{
  m := if a > b then a else b;
}

// BEGIN SPEC
method Max3(a: int, b: int, c: int) returns (m: int)
  ensures m >= a && m >= b && m >= c
  ensures m == a || m == b || m == c
// END SPEC
{
  var mab := Max(a, b);
  m := Max(mab, c);
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Max is E01 again with two inputs. For Max3, a method call is a statement, not an expression.
H2. Store the max of a and b in a fresh local, then take its max with c.
H3. var t := Max(a, b); m := Max(t, c);
*/
