// H09 | Quicksort | 60-120 min | recursion on array ranges, partition, frames, milestones
// GOAL
//   Sort the array in place with quicksort (Lomuto partition, recursion on index ranges).
//   The milestones give one decomposition with contracts; change or delete them freely.
//
// REFERENCE
//   a[lo..hi]                                   // slice of the array: a seq (reads a)
//   multiset(a[lo..hi]) == multiset(old(a[lo..hi]))     // range is permuted
//   forall k :: 0 <= k < lo || hi <= k < a.Length ==> a[k] == old(a[k])   // frame
//   assert a[lo..hi] == a[lo..p] + [a[p]] + a[p + 1..hi];               // split a range
//   x in multiset(s) <==> x in s               // the verifier knows this
//   // After sorting the left part recursively, you still need "all <= pivot": it follows from
//   // the multiset equality, but only through a lemma (PermBound).

// BEGIN SPEC
predicate Sorted(s: seq<int>) { forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j] }

method QuickSort(a: array<int>)
  modifies a
  ensures Sorted(a[..])
  ensures multiset(a[..]) == multiset(old(a[..]))
// END SPEC
{
  QS(a, 0, a.Length);
  assert a[0..a.Length] == a[..];
  assert old(a[0..a.Length]) == old(a[..]);
}

// MILESTONE (optional: change or delete)
method Swap(a: array<int>, i: int, j: int, ghost lo: int, ghost hi: int)
  requires 0 <= lo <= i < hi <= a.Length && lo <= j < hi
  modifies a
  ensures a[i] == old(a[j]) && a[j] == old(a[i])
  ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
  ensures multiset(a[lo..hi]) == multiset(old(a[lo..hi]))
{
  ghost var s := a[lo..hi];
  a[i], a[j] := a[j], a[i];
  assert a[lo..hi] == s[i - lo := s[j - lo]][j - lo := s[i - lo]];
}

// MILESTONE (optional: change or delete)
method Partition(a: array<int>, lo: int, hi: int) returns (p: int)
  requires 0 <= lo < hi <= a.Length
  modifies a
  ensures lo <= p < hi
  ensures forall k :: lo <= k < p ==> a[k] <= a[p]
  ensures forall k :: p < k < hi ==> a[k] > a[p]
  ensures multiset(a[lo..hi]) == multiset(old(a[lo..hi]))
  ensures forall k :: 0 <= k < lo || hi <= k < a.Length ==> a[k] == old(a[k])
{
  var pivot := a[hi - 1];
  var i := lo;
  for j := lo to hi - 1
    invariant lo <= i <= j
    invariant forall k :: lo <= k < i ==> a[k] <= pivot
    invariant forall k :: i <= k < j ==> a[k] > pivot
    invariant a[hi - 1] == pivot
    invariant multiset(a[lo..hi]) == multiset(old(a[lo..hi]))
    invariant forall k :: 0 <= k < lo || hi <= k < a.Length ==> a[k] == old(a[k])
  {
    if a[j] <= pivot {
      Swap(a, i, j, lo, hi);
      i := i + 1;
    }
  }
  Swap(a, i, hi - 1, lo, hi);
  p := i;
}

// MILESTONE (optional: change or delete)
// A permutation of a seq whose elements are all <= b (or all > b) has the same property.
lemma PermBound(s: seq<int>, t: seq<int>, b: int)
  requires multiset(s) == multiset(t)
  ensures (forall x :: x in s ==> x <= b) ==> (forall x :: x in t ==> x <= b)
  ensures (forall x :: x in s ==> x > b) ==> (forall x :: x in t ==> x > b)
{
  forall x | x in t ensures x in s {
    assert x in multiset(t);
  }
}

// MILESTONE (optional: change or delete)
lemma Combine(L: seq<int>, pivot: int, R: seq<int>)
  requires Sorted(L) && Sorted(R)
  requires forall x :: x in L ==> x <= pivot
  requires forall x :: x in R ==> x > pivot
  ensures Sorted(L + [pivot] + R)
{
  var s := L + [pivot] + R;
  forall i, j | 0 <= i < j < |s| ensures s[i] <= s[j] {
    if j < |L| {
    } else if i > |L| {
      assert s[i] == R[i - |L| - 1] && s[j] == R[j - |L| - 1];
    } else {
      if i < |L| { assert s[i] in L; }
      if j > |L| { assert s[j] == R[j - |L| - 1]; assert s[j] in R; }
    }
  }
}

// MILESTONE (optional: change or delete)
method QS(a: array<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= a.Length
  modifies a
  ensures Sorted(a[lo..hi])
  ensures multiset(a[lo..hi]) == multiset(old(a[lo..hi]))
  ensures forall k :: 0 <= k < lo || hi <= k < a.Length ==> a[k] == old(a[k])
  decreases hi - lo
{
  if hi - lo <= 1 { return; }
  var p := Partition(a, lo, hi);
  ghost var pivot := a[p];
  ghost var L0, R0 := a[lo..p], a[p + 1..hi];
  assert forall x :: x in L0 ==> x <= pivot;
  assert forall x :: x in R0 ==> x > pivot;
  assert a[lo..hi] == L0 + [pivot] + R0;

  QS(a, lo, p);
  ghost var L1 := a[lo..p];
  PermBound(L0, L1, pivot);
  assert a[p + 1..hi] == R0;

  QS(a, p + 1, hi);
  ghost var R1 := a[p + 1..hi];
  PermBound(R0, R1, pivot);

  // WHY: build the final slice pointwise; equating slices of different heaps directly is slow.
  ghost var S := L1 + [pivot] + R1;
  assert forall k :: lo <= k < p ==> a[k] == S[k - lo];
  assert forall k :: p < k < hi ==> a[k] == S[k - lo];
  assert a[lo..hi] == S;
  Combine(L1, pivot, R1);
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. QS(a, lo, hi) sorts the range [lo, hi) and leaves everything else alone. Partition puts the
    pivot at p with smaller-or-equal elements left and larger ones right.
H2. Contracts are the whole game: every method must promise the range is a permutation AND
    the outside is unchanged. After the recursive calls, use PermBound (with the slices saved in
    ghost variables before each call) to show the left part is still <= pivot and the right part
    still > pivot; then glue the pieces with Combine (cases on where i and j fall).
H3. Partition loop (j from lo to hi - 1, pivot = a[hi - 1]):
      invariant lo <= i <= j
      invariant forall k :: lo <= k < i ==> a[k] <= pivot
      invariant forall k :: i <= k < j ==> a[k] > pivot
      invariant a[hi - 1] == pivot   (+ multiset and frame)
*/
