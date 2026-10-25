// E25 | Max element value | 3 min | ghost var [R05]
// GOAL
//   Return the largest element of a non-empty array. Track *where* it is with a ghost variable
//   so you can state the "exists" part as an invariant.
//
// REFERENCE
//   ghost var w := 0;                   // verification-only variable, erased at compile time
//   w := i;                             // ghost vars may be assigned; code may not read them
//   invariant 0 <= w < i && a[w] == m   // a concrete witness beats an "exists" invariant
//   // Ghost code may read real state; real code may never depend on ghost state.

// BEGIN SPEC
method MaxElement(a: array<int>) returns (m: int)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
  ensures exists i :: 0 <= i < a.Length && a[i] == m
// END SPEC
{
  m := a[0];
  ghost var w := 0;
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant 0 <= w < i && a[w] == m
    invariant forall j :: 0 <= j < i ==> a[j] <= m
  {
    if a[i] > m {
      m := a[i];
      w := i;
    }
    i := i + 1;
  }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Start with m = a[0] and scan from index 1.
H2. Invariants: m bounds the prefix a[0..i); the ghost w is an index in that prefix holding m.
H3. invariant 0 <= w < i && a[w] == m      invariant forall j :: 0 <= j < i ==> a[j] <= m
*/
