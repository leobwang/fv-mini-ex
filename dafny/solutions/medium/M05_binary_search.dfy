// M05 | Binary search | 10-15 min | sorted precondition, half-open interval [R09]
// GOAL
//   Find key in a sorted array in O(log n) steps: an index holding key, or -1 if absent.
//
// REFERENCE
//   var lo, hi := 0, a.Length;          // search window [lo, hi)
//   var mid := lo + (hi - lo) / 2;      // lo <= mid < hi when lo < hi
//   invariant forall i :: 0 <= i < lo ==> a[i] < key
//   // Termination: hi - lo shrinks (guessed from the guard lo < hi).

// BEGIN SPEC
method BinarySearch(a: array<int>, key: int) returns (idx: int)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures -1 <= idx < a.Length
  ensures idx >= 0 ==> a[idx] == key
  ensures idx == -1 ==> key !in a[..]
// END SPEC
{
  var lo, hi := 0, a.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i :: 0 <= i < lo ==> a[i] < key
    invariant forall i :: hi <= i < a.Length ==> a[i] > key
  {
    var mid := lo + (hi - lo) / 2;
    if a[mid] < key {
      lo := mid + 1;
    } else if a[mid] > key {
      hi := mid;
    } else {
      return mid;
    }
  }
  return -1;
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Keep a window [lo, hi) outside of which key provably is not.
H2. Everything left of lo is < key, everything from hi on is > key. Sortedness justifies
    discarding a whole half after one comparison.
H3. invariant 0 <= lo <= hi <= a.Length
    invariant forall i :: 0 <= i < lo ==> a[i] < key
    invariant forall i :: hi <= i < a.Length ==> a[i] > key
*/
