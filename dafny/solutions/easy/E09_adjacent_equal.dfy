// E09 | Adjacent equal pair | 2-3 min | exists, negated invariant
// GOAL
//   Return whether some element equals its right neighbour.
//
// REFERENCE
//   exists i :: 0 <= i < n && P(i)              // bounded existential: note && (not ==>)
//   !(exists i :: Q(i))  ==  forall i :: !Q(i)  // negating flips the quantifier
//   while i + 1 < a.Length { ... }              // any boolean guard is fine
//   return true;                                // early return
//   // Every a[k] inside an invariant must be provably in range: bound i from both sides.

// BEGIN SPEC
method HasAdjacentEqual(a: array<int>) returns (b: bool)
  ensures b <==> exists i :: 0 <= i < a.Length - 1 && a[i] == a[i + 1]
// END SPEC
{
  if a.Length == 0 { return false; }
  var i := 0;
  while i + 1 < a.Length
    invariant 0 <= i < a.Length
    invariant forall j :: 0 <= j < i ==> a[j] != a[j + 1]
  {
    if a[i] == a[i + 1] { return true; }
    i := i + 1;
  }
  return false;
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Returning true is easy to justify: the current i is the witness. What must hold to return false?
H2. Invariant: no pair seen so far is equal. Write it as a forall, not as a negated exists.
H3. (after returning false on an empty array) invariant 0 <= i < a.Length
    invariant forall j :: 0 <= j < i ==> a[j] != a[j + 1]
*/
