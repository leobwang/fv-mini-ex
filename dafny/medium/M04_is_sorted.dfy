// M04 | Is sorted | 5-10 min | pair quantifier, adjacent check [R08]
// GOAL
//   Decide sortedness with ONE pass over adjacent pairs, against an all-pairs spec.
//
// REFERENCE
//   forall i, j :: 0 <= i < j < n ==> a[i] <= a[j]      // two bound variables
//   0 <= p < q <= i                                       // chained range
//   // Extending "all pairs in a[0..i] are ordered" by a[i] <= a[i+1] needs transitivity,
//   // which the verifier does on its own once the invariant states the pair property.

// BEGIN SPEC
method IsSorted(a: array<int>) returns (b: bool)
  ensures b <==> forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. If a[i] > a[i+1] you can return false: (i, i+1) is the bad pair.
H2. Invariant on the scanned prefix in the *all-pairs* form, not the adjacent form.
H3. invariant 0 <= i < a.Length (after handling the empty array)
    invariant forall p, q :: 0 <= p < q <= i ==> a[p] <= a[q]
*/
