// H06 | Binary heap insert | 45-90 min | sift-up, "heap except at k" invariant, milestones
// GOAL
//   a[0..n) is a max-heap stored in an array (parent of i is (i - 1) / 2). Insert x at
//   position n and sift it up so that a[0..n] is a max-heap holding the old elements plus x.
//
// REFERENCE
//   (i - 1) / 2                                 // parent index, for i > 0
//   a[k], a[p] := a[p], a[k];                   // swap with the parent
//   multiset(a[..n + 1])                        // the heap's elements
//   assert a[..n + 1] == a[..n] + [x];          // after writing a[n] := x
//   // Sifting up keeps "every parent >= child", except possibly between k and its parent;
//   // the swap can also break the edge from k's parent to k's children: track that too.
// NOTE: s[i] and s[(i - 1) / 2] form a matching loop; give such quantifiers {:trigger s[i]}
//   (also forall statements: forall i {:trigger s[i]} | 0 < i < |s| ensures ... { }).

// BEGIN SPEC
ghost predicate IsHeap(s: seq<int>)
{
  forall i {:trigger s[i]} :: 0 < i < |s| ==> s[(i - 1) / 2] >= s[i]
}

method HeapInsert(a: array<int>, n: int, x: int)
  requires 0 <= n < a.Length && IsHeap(a[..n])
  modifies a
  ensures IsHeap(a[..n + 1])
  ensures multiset(a[..n + 1]) == multiset(old(a[..n])) + multiset{x}
  ensures a[n + 1..] == old(a[n + 1..])
// END SPEC
{
  a[n] := x;
  assert a[..n + 1] == old(a[..n]) + [x];
  var k := n;
  while k > 0 && a[(k - 1) / 2] < a[k]
    invariant 0 <= k <= n
    invariant HeapExcept(a[..n + 1], k)
    invariant multiset(a[..n + 1]) == multiset(old(a[..n])) + multiset{x}
    invariant a[n + 1..] == old(a[n + 1..])
  {
    var p := (k - 1) / 2;
    ghost var s := a[..n + 1];
    a[k], a[p] := a[p], a[k];
    assert a[..n + 1] == s[k := s[p]][p := s[k]];
    SwapStep(s, k);
    k := p;
  }
  HeapExceptDone(a[..n + 1], k);
}

// MILESTONE (optional: change or delete)
// Heap order holds on every edge except (parent(k), k); and the grandparent edge is safe:
// the parent of k is >= every child of k.
ghost predicate HeapExcept(s: seq<int>, k: int)
  requires 0 <= k < |s|
{
  (forall i {:trigger s[i]} :: 0 < i < |s| && i != k ==> s[(i - 1) / 2] >= s[i]) &&
  (k > 0 ==> forall i {:trigger s[i]} :: 0 < i < |s| && (i - 1) / 2 == k ==> s[(k - 1) / 2] >= s[i])
}

// MILESTONE (optional: change or delete)
lemma HeapExceptDone(s: seq<int>, k: int)
  requires 0 <= k < |s| && HeapExcept(s, k)
  requires k == 0 || s[(k - 1) / 2] >= s[k]
  ensures IsHeap(s)
{
}

// MILESTONE (optional: change or delete)
// One sift-up step: swapping k with its (smaller) parent moves the "hole" up to the parent.
lemma SwapStep(s: seq<int>, k: int)
  requires 0 < k < |s| && HeapExcept(s, k) && s[(k - 1) / 2] < s[k]
  ensures HeapExcept(s[k := s[(k - 1) / 2]][(k - 1) / 2 := s[k]], (k - 1) / 2)
{
  var p := (k - 1) / 2;
  var t := s[k := s[p]][p := s[k]];
  forall i {:trigger t[i]} | 0 < i < |t| && i != p ensures t[(i - 1) / 2] >= t[i] {
    var q := (i - 1) / 2;
    if i == k {
    } else if q == k {
      assert s[p] >= s[i];
    } else if q == p {
      assert s[p] >= s[i];
    } else {
      assert t[i] == s[i] && t[q] == s[q];
    }
  }
  if p > 0 {
    forall i {:trigger t[i]} | 0 < i < |t| && (i - 1) / 2 == p ensures t[(p - 1) / 2] >= t[i] {
      var g := (p - 1) / 2;
      assert s[g] >= s[p];
      if i == k {
      } else {
        assert s[p] >= s[i];
      }
    }
  }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write x at position n first; the only possible violation is between n and its parent.
    Swap upwards while the parent is smaller.
H2. Loop invariant HeapExcept(a[..n + 1], k): every edge except (parent(k), k) is ordered, and
    parent(k) dominates k's children (so after a swap, k's old parent, now at k, still dominates
    them). Also carry the multiset and the untouched tail a[n + 1..].
H3. (step: ghost var s := a[..n + 1]; swap; assert a[..n + 1] == s[k := s[p]][p := s[k]];
     then a lemma like SwapStep about the seq s keeps the method's proof small)
    invariant 0 <= k <= n
    invariant HeapExcept(a[..n + 1], k)
    invariant multiset(a[..n + 1]) == multiset(old(a[..n])) + multiset{x}
    invariant a[n + 1..] == old(a[n + 1..])
*/
