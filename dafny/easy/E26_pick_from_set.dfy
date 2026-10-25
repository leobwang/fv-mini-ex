// E26 | Pick from a set | 1-3 min | assign such that
// GOAL
//   Take an arbitrary element out of a non-empty set; then pick an index of a positive element.
//
// REFERENCE
//   var x :| x in s;                     // "some x such that ...": you must prove one exists
//   x :| P(x);                           // assign an existing variable
//   |s - {x}| == |s| - 1                 // (when x in s) the verifier knows this
//   // In compiled code the choice must be over a finite domain, e.g. 0 <= i < a.Length.

// BEGIN SPEC
method Extract(s: set<int>) returns (x: int, rest: set<int>)
  requires s != {}
  ensures x in s && rest == s - {x}
  ensures |rest| == |s| - 1
// END SPEC
{
}

// BEGIN SPEC
method SomePositive(a: array<int>) returns (i: int)
  requires exists k :: 0 <= k < a.Length && a[k] > 0
  ensures 0 <= i < a.Length && a[i] > 0
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. You do not need a loop for either method.
H2. The precondition is exactly the existence proof that :| needs.
H3. x :| x in s; rest := s - {x};      and      i :| 0 <= i < a.Length && a[i] > 0;
*/
