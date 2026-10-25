// M01 | Linear search | 5-8 min | array, loop, first occurrence [R04]
// GOAL
//   Return the index of the FIRST occurrence of key in a, or -1 if key does not occur.
//
// REFERENCE
//   key in a[..]    key !in a[..]       // membership in the array's contents (a seq)
//   forall j :: 0 <= j < i ==> a[j] != key
//   return i;                           // early return
//   // "x !in s" and "forall j :: 0 <= j < |s| ==> s[j] != x" are interchangeable for the
//   // verifier once the forall is known.

// BEGIN SPEC
method LinearSearch(a: array<int>, key: int) returns (idx: int)
  ensures -1 <= idx < a.Length
  ensures idx >= 0 ==> a[idx] == key && forall j :: 0 <= j < idx ==> a[j] != key
  ensures idx == -1 ==> key !in a[..]
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Scan left to right and return at the first hit.
H2. The invariant that gives you both "first" and "not found": no earlier element equals key.
H3. invariant 0 <= i <= a.Length   invariant forall j :: 0 <= j < i ==> a[j] != key
*/
