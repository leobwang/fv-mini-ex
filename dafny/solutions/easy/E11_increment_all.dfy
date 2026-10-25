// E11 | Increment all | 2-3 min | modifies, old
// GOAL
//   Add 1 to every element of the array, in place.
//
// REFERENCE
//   method M(a: array<int>) modifies a     // permission to write a's elements
//   old(a[i])                               // value of a[i] when the method was called
//   old(a[..])                              // the whole array (as a seq) at entry
//   a[i] := a[i] + 1;                       // array update
//   // A loop invariant must also describe the part of the array you have NOT touched yet.

// BEGIN SPEC
method IncrementAll(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
// END SPEC
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] == old(a[j]) + 1
    // WHY: without this, the verifier forgets what a[i] was before you increment it.
    invariant forall j :: i <= j < a.Length ==> a[j] == old(a[j])
  {
    a[i] := a[i] + 1;
    i := i + 1;
  }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. One loop. What do you know about the elements before i? After i?
H2. Two quantified invariants: done part (old + 1) and untouched part (== old).
H3. invariant forall j :: 0 <= j < i ==> a[j] == old(a[j]) + 1
    invariant forall j :: i <= j < a.Length ==> a[j] == old(a[j])
*/
