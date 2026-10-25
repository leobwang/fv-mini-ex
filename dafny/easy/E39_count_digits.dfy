// E39 | Count digits | 2-3 min | invariant, done + remaining
// GOAL
//   Count decimal digits with a loop and prove it matches the recursive NumDigits.
//
// REFERENCE
//   invariant done + F(rest) == F(input)      // "work done so far + work left = total":
//                                             // the usual shape when the spec recurses on
//                                             // the *remaining* input (here n / 10)
//   m := m / 10;                              // integer division rounds down for m >= 0

// BEGIN SPEC
function NumDigits(n: nat): nat { if n < 10 then 1 else 1 + NumDigits(n / 10) }

method CountDigits(n: nat) returns (d: nat)
  ensures d == NumDigits(n)
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Keep dividing a copy m of n by 10. What does NumDigits(m) still have to contribute?
H2. Relate d, NumDigits(m) and NumDigits(n) in one equation that is true at the start (d = 1).
H3. invariant d + NumDigits(m) == NumDigits(n) + 1   (loop while m >= 10)
*/
