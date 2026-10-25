// M38 | Partition evens first | 10-15 min | in-place swaps, multiset invariant
// GOAL
//   Rearrange a in place so all even elements come before all odd ones; return the boundary.
//
// REFERENCE
//   a[i], a[j] := a[j], a[i];                        // swap (E14)
//   invariant multiset(a[..]) == multiset(old(a[..]))  // "still a permutation"
//   x % 2 == 0                                         // even (also for negative x)
//   // Two zones grow: evens in [0, k), odds in [k, i); [i, n) unexplored.

// BEGIN SPEC
method PartitionEvens(a: array<int>) returns (k: int)
  modifies a
  ensures 0 <= k <= a.Length
  ensures forall i :: 0 <= i < k ==> a[i] % 2 == 0
  ensures forall i :: k <= i < a.Length ==> a[i] % 2 != 0
  ensures multiset(a[..]) == multiset(old(a[..]))
// END SPEC
{
  k := 0;
  for i := 0 to a.Length
    invariant 0 <= k <= i
    invariant forall p :: 0 <= p < k ==> a[p] % 2 == 0
    invariant forall p :: k <= p < i ==> a[p] % 2 != 0
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    if a[i] % 2 == 0 {
      a[k], a[i] := a[i], a[k];
      k := k + 1;
    }
  }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Scan with i; keep the even zone [0, k) and the odd zone [k, i).
H2. When a[i] is even, swap it with a[k] (the first odd element, or itself) and grow k.
H3. invariant 0 <= k <= i   evens on [0, k), odds on [k, i)   multiset(a[..]) == multiset(old(a[..]))
*/
