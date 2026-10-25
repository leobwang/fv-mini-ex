// M17 | Opaque function | 10-15 min | opaque, reveal
// GOAL
//   AllNonNeg is opaque: its body is hidden unless revealed. Prove the two interface lemmas
//   with reveal, then build Abses using only the lemmas.
//
// REFERENCE
//   opaque predicate P(x: int) { x > 0 }      // body hidden from the verifier by default
//   reveal P();                                // in a proof: make the body visible from here on
//   assert P(3) by { reveal P(); }             // reveal for one fact only
//   // Opaque definitions keep big quantified bodies out of every proof: callers reason through
//   // a few lemmas instead.

// BEGIN SPEC
opaque ghost predicate AllNonNeg(s: seq<int>) { forall i :: 0 <= i < |s| ==> s[i] >= 0 }

lemma AllNonNegSnoc(s: seq<int>, x: int)
  requires AllNonNeg(s) && x >= 0
  ensures AllNonNeg(s + [x])
// END SPEC
{
  reveal AllNonNeg();
}

// BEGIN SPEC
lemma AllNonNegEmpty()
  ensures AllNonNeg([])
// END SPEC
{
  reveal AllNonNeg();
}

// BEGIN SPEC
method Abses(a: array<int>) returns (r: seq<int>)
  ensures |r| == a.Length && AllNonNeg(r)
  ensures forall i :: 0 <= i < a.Length ==> r[i] == a[i] || r[i] == -a[i]
// END SPEC
{
  r := [];
  AllNonNegEmpty();
  for i := 0 to a.Length
    invariant |r| == i && AllNonNeg(r)
    invariant forall k :: 0 <= k < i ==> r[k] == a[k] || r[k] == -a[k]
  {
    var v := if a[i] < 0 then -a[i] else a[i];
    AllNonNegSnoc(r, v);
    r := r + [v];
  }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The lemmas are one line each. In Abses, carry AllNonNeg(r) as a loop invariant.
H2. Establish it with AllNonNegEmpty() before the loop; maintain it with AllNonNegSnoc(r, v)
    just before r := r + [v].
H3. invariant |r| == i && AllNonNeg(r)
    invariant forall k :: 0 <= k < i ==> r[k] == a[k] || r[k] == -a[k]
*/
