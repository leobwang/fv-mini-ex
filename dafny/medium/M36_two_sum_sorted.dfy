// M36 | Two-sum on a sorted array | 15-20 min | two pointers, pair invariant
// GOAL
//   Find i < j with a[i] + a[j] == target in a sorted array, moving two pointers inward.
//
// REFERENCE
//   var lo, hi := 0, a.Length - 1;
//   while lo < hi
//   invariant forall p, q :: 0 <= p < q < a.Length && (p < lo || q > hi) ==> a[p] + a[q] != target
//   return true, lo, hi;                 // several out-parameters at once
//   // If a[lo] + a[hi] < target, no partner q <= hi works for lo, since a[q] <= a[hi].

// BEGIN SPEC
method TwoSum(a: array<int>, target: int) returns (found: bool, i: int, j: int)
  requires forall p, q :: 0 <= p < q < a.Length ==> a[p] <= a[q]
  ensures found ==> 0 <= i < j < a.Length && a[i] + a[j] == target
  ensures !found ==> forall p, q :: 0 <= p < q < a.Length ==> a[p] + a[q] != target
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Compare a[lo] + a[hi] with the target; one of the two pointers can always move.
H2. Invariant: every pair that uses an index outside [lo, hi] has been ruled out. At exit
    lo >= hi, so every pair p < q uses such an index.
H3. invariant 0 <= lo && hi < a.Length && lo <= hi + 1
    invariant forall p, q :: 0 <= p < q < a.Length && (p < lo || q > hi) ==> a[p] + a[q] != target
*/
