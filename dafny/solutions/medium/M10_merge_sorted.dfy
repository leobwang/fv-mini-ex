// M10 | Merge two sorted sequences | 15-20 min | multiset, sortedness invariants [R15]
// GOAL
//   Merge two sorted sequences into one sorted sequence with the same elements.
//
// REFERENCE
//   multiset(s + t) == multiset(s) + multiset(t)    // the verifier knows this
//   assert a[..i + 1] == a[..i] + [a[i]];           // growing a prefix
//   assert a[..|a|] == a;                           // full prefix
//   c := c + [x];                                   // append to a seq
//   // Key invariant: every element of c is <= the next candidates a[i] and b[j].

// BEGIN SPEC
predicate Sorted(s: seq<int>) { forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j] }

method Merge(a: seq<int>, b: seq<int>) returns (c: seq<int>)
  requires Sorted(a) && Sorted(b)
  ensures Sorted(c)
  ensures multiset(c) == multiset(a) + multiset(b)
// END SPEC
{
  var i, j := 0, 0;
  c := [];
  while i < |a| || j < |b|
    invariant 0 <= i <= |a| && 0 <= j <= |b|
    invariant Sorted(c)
    invariant multiset(c) == multiset(a[..i]) + multiset(b[..j])
    invariant forall k :: 0 <= k < |c| && i < |a| ==> c[k] <= a[i]
    invariant forall k :: 0 <= k < |c| && j < |b| ==> c[k] <= b[j]
    decreases |a| - i + |b| - j
  {
    if j == |b| || (i < |a| && a[i] <= b[j]) {
      assert a[..i + 1] == a[..i] + [a[i]];
      c := c + [a[i]];
      i := i + 1;
    } else {
      assert b[..j + 1] == b[..j] + [b[j]];
      c := c + [b[j]];
      j := j + 1;
    }
  }
  assert a[..|a|] == a && b[..|b|] == b;
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Standard two-pointer merge; take from a when b is exhausted or a[i] <= b[j].
H2. Invariants: Sorted(c); multiset(c) == multiset(a[..i]) + multiset(b[..j]); every c[k] is
    <= a[i] (if i < |a|) and <= b[j] (if j < |b|). Termination: |a| - i + |b| - j.
H3. invariant forall k :: 0 <= k < |c| && i < |a| ==> c[k] <= a[i]   (same for b, j)
*/
