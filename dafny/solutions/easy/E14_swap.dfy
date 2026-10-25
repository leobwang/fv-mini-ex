// E14 | Swap | 1-3 min | multiset, parallel assignment
// GOAL
//   Swap two array elements, then use Swap to reverse a 3-element array.
//
// REFERENCE
//   a[i], a[j] := a[j], a[i];                // parallel assignment: right sides read first
//   multiset(s)   multiset{1, 1, 2}          // bag of elements; multiset(s)[x] = count of x
//   multiset(a[..]) == multiset(old(a[..]))  // "a is a permutation of its old contents"
//   Swap(a, 0, 2);                            // a method call as a statement (no out-params)

// BEGIN SPEC
method Swap(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
  ensures a[i] == old(a[j]) && a[j] == old(a[i])
  ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
  ensures multiset(a[..]) == multiset(old(a[..]))
// END SPEC
{
  a[i], a[j] := a[j], a[i];
}

// BEGIN SPEC
method Reverse3(a: array<int>)
  requires a.Length == 3
  modifies a
  ensures a[..] == [old(a[2]), old(a[1]), old(a[0])]
  ensures multiset(a[..]) == multiset(old(a[..]))
// END SPEC
{
  Swap(a, 0, 2);
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two writes that each need the *other* old value.
H2. A parallel assignment evaluates all right-hand sides before writing. The verifier proves the
    multiset fact for you. For Reverse3, which two positions move?
H3. a[i], a[j] := a[j], a[i];      and      Swap(a, 0, 2);
*/
