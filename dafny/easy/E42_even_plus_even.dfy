// E42 | Even plus even | 2-3 min | existential elimination
// GOAL
//   Prove both lemmas. Even is an existential, so first *obtain* the witnesses from the
//   hypotheses, then *supply* a witness for the conclusion.
//
// REFERENCE
//   var k :| a == 2 * k;                 // in a lemma: name a witness of a known "exists"
//   assert a + b == 2 * (i + j);         // mention the new witness term so it gets used
//   ghost predicate G(n: int) { exists k :: n == 3 * k }   // ghost: not compilable (unbounded)

// BEGIN SPEC
ghost predicate Even(n: int) { exists k :: n == 2 * k }

lemma EvenAdd(a: int, b: int)
  requires Even(a) && Even(b)
  ensures Even(a + b)
// END SPEC
{
}

// BEGIN SPEC
lemma EvenTimes(a: int, b: int)
  requires Even(a)
  ensures Even(a * b)
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. You know a == 2*i for some i. Name it.
H2. Two ":|" for EvenAdd, one for EvenTimes, then assert the conclusion's body with a witness.
H3. var i :| a == 2 * i;  var j :| b == 2 * j;  assert a + b == 2 * (i + j);
*/
