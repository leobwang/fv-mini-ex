// M15 | Assert by | 10-15 min | assert by, lemma, termination
// GOAL
//   Find the smallest k with Pow2(k) > x. Termination needs a fact about Pow2; prove it once as
//   a lemma and bring it in locally with assert ... by.
//
// REFERENCE
//   assert P by { L(k); }       // facts from the block are used to prove P, then forgotten:
//                               // only P remains in the context (keeps proofs fast and tidy)
//   decreases x - k             // must be >= 0 whenever an iteration starts
//   lemma {:induction false} L(n: nat) ensures F(n) > n { if n > 0 { L(n - 1); } }

// BEGIN SPEC
function Pow2(n: nat): nat { if n == 0 then 1 else 2 * Pow2(n - 1) }

lemma {:induction false} Pow2Grows(n: nat)
  ensures Pow2(n) > n
// END SPEC
{
  if n > 0 { Pow2Grows(n - 1); }
}

// BEGIN SPEC
method Log2Above(x: nat) returns (k: nat)
  ensures Pow2(k) > x
  ensures k == 0 || Pow2(k - 1) <= x
// END SPEC
{
  k := 0;
  while Pow2(k) <= x
    invariant k == 0 || Pow2(k - 1) <= x
    decreases x - k
  {
    assert k < Pow2(k) by { Pow2Grows(k); }
    k := k + 1;
  }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Loop k upward while Pow2(k) <= x. Why can k not run past x?
H2. Inside the loop Pow2(k) <= x and k < Pow2(k), so k < x: that makes "decreases x - k" valid.
H3. invariant k == 0 || Pow2(k - 1) <= x   decreases x - k
    in the body: assert k < Pow2(k) by { Pow2Grows(k); }
*/
