// H02 | Merge sort | 30-60 min | recursion on seq, merge, multiset, milestones [R20]
// GOAL
//   Implement merge sort on sequences: the result is sorted and a permutation of the input.
//   Merge is M10 again (reuse it); the new part is the recursion and its permutation proof.
//
// REFERENCE
//   method M(s: seq<int>) returns (r: seq<int>) decreases |s| { ... var x := M(s[..k]); ... }
//   assert s == s[..k] + s[k..];               // so multiset(s) splits into the two halves
//   multiset(a + b) == multiset(a) + multiset(b)
//   assert a[..i + 1] == a[..i] + [a[i]];      // growing a prefix (M10)
//   // Sorted only talks about positions; sortedness of a merge needs "c's last <= next ones".

// BEGIN SPEC
predicate Sorted(s: seq<int>) { forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j] }

method MergeSort(s: seq<int>) returns (r: seq<int>)
  ensures Sorted(r)
  ensures multiset(r) == multiset(s)
  decreases |s|
// END SPEC
{
  if |s| <= 1 { return s; }
  var mid := |s| / 2;
  var left := MergeSort(s[..mid]);
  var right := MergeSort(s[mid..]);
  assert s == s[..mid] + s[mid..];
  r := Merge(left, right);
}

// MILESTONE (optional: change or delete)
method Merge(a: seq<int>, b: seq<int>) returns (c: seq<int>)
  requires Sorted(a) && Sorted(b)
  ensures Sorted(c)
  ensures multiset(c) == multiset(a) + multiset(b)
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

// MILESTONE (optional: change or delete)
lemma MultisetSplit(s: seq<int>, k: int)
  requires 0 <= k <= |s|
  ensures multiset(s) == multiset(s[..k]) + multiset(s[k..])
{
  assert s == s[..k] + s[k..];
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Base case |s| <= 1 is already sorted. Otherwise split at |s| / 2, sort both halves
    recursively, and merge.
H2. The permutation proof in MergeSort is one assert: s == s[..mid] + s[mid..]. All the work is
    in Merge: a two-pointer loop that always appends the smaller head.
H3. Merge invariants: Sorted(c); multiset(c) == multiset(a[..i]) + multiset(b[..j]);
    forall k :: 0 <= k < |c| && i < |a| ==> c[k] <= a[i]  (same for b, j);
    decreases |a| - i + |b| - j
*/
