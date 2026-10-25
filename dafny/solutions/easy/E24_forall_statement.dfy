// E24 | All powers positive | 2-3 min | forall statement, assert forall
// GOAL
//   Pow2Pos proves one instance. Turn it into the universal statements below.
//
// REFERENCE
//   forall n: nat ensures P(n) { L(n); }          // proves "forall n :: P(n)" by calling L(n)
//   forall i | 0 <= i < |s| ensures P(s[i]) { L(s[i]); }   // with a range
//   assert forall i | 0 <= i < |s| :: P(s[i]) by {
//     forall i | 0 <= i < |s| { L(s[i]); }          // ensures may be omitted when obvious
//   }
//   // Plain lemma calls cannot do this: L(n) needs a concrete n.

// BEGIN SPEC
function Pow2(n: nat): nat { if n == 0 then 1 else 2 * Pow2(n - 1) }

lemma Pow2Pos(n: nat)
  ensures Pow2(n) > 0
{}

lemma AllPow2Pos()
  ensures forall n: nat :: Pow2(n) > 0
// END SPEC
{
  forall n: nat ensures Pow2(n) > 0 { Pow2Pos(n); }
}

// BEGIN SPEC
lemma Pow2OfSeq(s: seq<nat>)
  ensures forall i :: 0 <= i < |s| ==> Pow2(s[i]) > 0
// END SPEC
{
  forall i | 0 <= i < |s| ensures Pow2(s[i]) > 0 { Pow2Pos(s[i]); }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The verifier does not prove a universal about a recursive function by itself.
H2. A forall statement runs a proof "for every n": its body calls the one-instance lemma.
H3. forall n: nat ensures Pow2(n) > 0 { Pow2Pos(n); }    (the seq version adds a range)
*/
