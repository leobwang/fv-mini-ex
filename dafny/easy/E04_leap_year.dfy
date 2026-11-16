// E04 | Leap year | 1-3 min | predicate, %, test lemma
// GOAL
//   Define IsLeap for the Gregorian calendar: divisible by 4, except centuries,
//   except centuries divisible by 400. The two lemmas check your definition.
//
// REFERENCE
//   predicate P(x: int) { x > 0 }          // a function returning bool
//   x % 4 == 0                              // remainder (always >= 0 for a positive divisor)
//   a && (b || !c)                          // boolean operators
//   lemma L() ensures P(3) {}               // an empty-bodied lemma: the verifier proves it alone

// BEGIN SPEC
predicate IsLeap(y: int)
// END SPEC
{
  (y % 400 == 0) || ((y % 4 == 0) && (y % 100 != 0))  // TODO
}

// BEGIN SPEC
lemma LeapTests()
  ensures IsLeap(2024) && IsLeap(2000) && IsLeap(1600)
  ensures !IsLeap(2023) && !IsLeap(1900) && !IsLeap(2100)
{}

lemma LeapPeriodic(y: int)
  ensures IsLeap(y) == IsLeap(y + 400)
{}
// END SPEC

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Three rules, one boolean expression. Which years are the exceptions to "divisible by 4"?
H2. "divisible by 4" AND ("not a century" OR "divisible by 400").
H3. y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)
*/
