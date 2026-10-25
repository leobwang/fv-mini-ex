// H01 | Insertion sort | 45-75 min | nested loops, sorted + permutation, milestones [R14]
// GOAL
//   Sort the array in place by insertion sort: the result is sorted AND a permutation of the
//   input. The milestones below suggest one decomposition; change or delete them freely.
//
// REFERENCE
//   multiset(a[..]) == multiset(old(a[..]))      // permutation (swaps preserve it)
//   a[j - 1], a[j] := a[j], a[j - 1];            // swap neighbours
//   while j > 0 && a[j - 1] > a[j]               // && short-circuits, so a[j - 1] is safe
//   method Helper(a: array<int>, i: int) requires ... modifies a ensures ...   // own contract
//   // Inner-loop invariant: a[0..i] is sorted except at the moving position j.

// BEGIN SPEC
predicate Sorted(s: seq<int>) { forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j] }

method InsertionSort(a: array<int>)
  modifies a
  ensures Sorted(a[..])
  ensures multiset(a[..]) == multiset(old(a[..]))
// END SPEC
{
  for i := 0 to a.Length
    invariant Sorted(a[..i])
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    InsertOne(a, i);
  }
  assert a[..a.Length] == a[..];
}

// MILESTONE (optional: change or delete)
// "Sorted on [0, hi] except that position j may be out of place, and a[j] is below everything
// to its right."
ghost predicate SortedExcept(s: seq<int>, hi: int, j: int)
  requires 0 <= j <= hi < |s|
{
  (forall p, q :: 0 <= p < q <= hi && p != j && q != j ==> s[p] <= s[q]) &&
  (forall q :: j < q <= hi ==> s[j] <= s[q])
}

// MILESTONE (optional: change or delete)
lemma ExceptToSorted(s: seq<int>, hi: int, j: int)
  requires 0 <= j <= hi < |s| && SortedExcept(s, hi, j)
  requires j == 0 || s[j - 1] <= s[j]
  ensures Sorted(s[..hi + 1])
{
  forall p, q | 0 <= p < q <= hi ensures s[p] <= s[q] {
    if p == j || q == j {
    } else if p < j && j < q {
      assert s[p] <= s[j - 1];
    }
  }
}

// MILESTONE (optional: change or delete)
// Insert a[i] into the sorted prefix a[0..i).
method InsertOne(a: array<int>, i: int)
  requires 0 <= i < a.Length && Sorted(a[..i])
  modifies a
  ensures Sorted(a[..i + 1])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var j := i;
  while j > 0 && a[j - 1] > a[j]
    invariant 0 <= j <= i
    invariant SortedExcept(a[..], i, j)
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    a[j - 1], a[j] := a[j], a[j - 1];
    j := j - 1;
  }
  ExceptToSorted(a[..], i, j);
  assert a[..i + 1] == a[..][..i + 1];
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Outer loop: a[0..i) is sorted and a is a permutation of the input. The work is inserting
    a[i] by swapping it leftwards while its left neighbour is bigger.
H2. Inner invariant (SortedExcept): pairs in [0, i] not involving j are ordered, and a[j] is <=
    everything to its right. When the inner loop stops (j == 0 or a[j-1] <= a[j]) that gives
    "a[0..i] sorted". The permutation part is automatic for swaps.
H3. while j > 0 && a[j - 1] > a[j]
      invariant 0 <= j <= i
      invariant SortedExcept(a[..], i, j)
      invariant multiset(a[..]) == multiset(old(a[..]))
    and in ExceptToSorted, the only interesting pairs are p < j < q: go through s[j - 1].
*/
