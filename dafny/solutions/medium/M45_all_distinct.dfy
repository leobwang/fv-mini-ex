// M45 | All distinct | 10-15 min | nested loops, pair invariants
// GOAL
//   Decide whether all elements are pairwise distinct, using two nested loops (O(n^2)).
//
// REFERENCE
//   for i := 0 to n {
//     for j := i + 1 to n
//       invariant P(i, j)     // inner invariants: repeat what the outer loop knows
//     { ... }
//   }
//   return false;             // early exit from inside both loops

// BEGIN SPEC
method AllDistinct(a: array<int>) returns (b: bool)
  ensures b <==> forall i, j :: 0 <= i < j < a.Length ==> a[i] != a[j]
// END SPEC
{
  for i := 0 to a.Length
    invariant forall p, q :: 0 <= p < i && p < q < a.Length ==> a[p] != a[q]
  {
    for j := i + 1 to a.Length
      invariant forall p, q :: 0 <= p < i && p < q < a.Length ==> a[p] != a[q]
      invariant forall q :: i < q < j ==> a[i] != a[q]
    {
      if a[i] == a[j] { return false; }
    }
  }
  return true;
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Outer index i, inner index j > i; return false on the first equal pair.
H2. Outer invariant: every pair whose smaller index is < i is distinct. Inner: additionally
    a[i] differs from a[i+1..j).
H3. invariant forall p, q :: 0 <= p < i && p < q < a.Length ==> a[p] != a[q]
    inner: invariant forall q :: i < q < j ==> a[i] != a[q]
*/
