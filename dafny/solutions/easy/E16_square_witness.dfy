// E16 | A square witness | 1-2 min | lemma, assert
// GOAL
//   Prove the lemma. The verifier will not guess a witness for an existential with
//   multiplication; give it one.
//
// REFERENCE
//   lemma L(x: int) requires x > 0 ensures x + x > x { }   // a ghost method: proof only
//   assert e;                         // prove e here, then use it as a known fact below
//   assert P(5);                      // mentioning a concrete term lets the verifier use it
//                                     // as the witness for "exists k :: P(k)"

// BEGIN SPEC
lemma SquareWitness()
  ensures exists k: int :: k > 0 && k * k == 144
// END SPEC
{
  assert 12 > 0 && 12 * 12 == 144;
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Which k works? The verifier needs to see that term.
H2. Assert the body of the existential, instantiated with the witness.
H3. assert 12 > 0 && 12 * 12 == 144;
*/
