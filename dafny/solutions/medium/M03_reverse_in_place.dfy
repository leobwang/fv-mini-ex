// M03 | Reverse in place | 10-15 min | two indices, old, swap [R07]
// GOAL
//   Reverse the array in place.
//
// REFERENCE
//   a[i], a[j] := a[j], a[i];              // swap
//   old(a[k])                              // entry value of a[k] (also inside invariants)
//   invariant forall k :: 0 <= k < i ==> a[k] == old(a[n - 1 - k])
//   // Describe three zones: done on the left, done on the right, untouched in the middle.

// BEGIN SPEC
method Reverse(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
// END SPEC
{
  var n := a.Length;
  var i := 0;
  while i < n / 2
    invariant 0 <= i <= n / 2
    invariant forall k :: 0 <= k < i ==> a[k] == old(a[n - 1 - k]) && a[n - 1 - k] == old(a[k])
    invariant forall k :: i <= k < n - i ==> a[k] == old(a[k])
  {
    a[i], a[n - 1 - i] := a[n - 1 - i], a[i];
    i := i + 1;
  }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Swap a[i] with its mirror a[n-1-i] for i < n / 2. The middle element (odd n) stays.
H2. Invariants: the left zone [0, i) and its mirror are reversed; the middle [i, n-i) is untouched.
H3. invariant forall k :: 0 <= k < i ==> a[k] == old(a[n - 1 - k]) && a[n - 1 - k] == old(a[k])
    invariant forall k :: i <= k < n - i ==> a[k] == old(a[k])
*/
