// E22 | Division with remainder | 2-3 min | multiple returns
// GOAL
//   Compute quotient and remainder by repeated subtraction (no / or %).
//
// REFERENCE
//   method M(x: int) returns (a: int, b: int)   // several out-parameters
//   a, b := 0, x;                               // simultaneous assignment
//   var q, r := DivMod(17, 5);                  // caller binds both results
//   invariant a == q * b + r                    // an invariant may mention several variables

// BEGIN SPEC
method DivMod(a: nat, b: nat) returns (q: nat, r: nat)
  requires b > 0
  ensures a == q * b + r && r < b
// END SPEC
{
  q, r := 0, a;
  while r >= b
    invariant a == q * b + r
  {
    q, r := q + 1, r - b;
  }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Start with r = a and subtract b while you can.
H2. The invariant "a == q * b + r" holds initially (q = 0) and after each step. Termination: r
    shrinks (guessed from the guard).
H3. q, r := 0, a; while r >= b invariant a == q * b + r { q, r := q + 1, r - b; }
*/
