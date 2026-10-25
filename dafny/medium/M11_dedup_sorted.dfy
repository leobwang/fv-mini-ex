// M11 | Dedup a sorted sequence | 10-15 min | strictly increasing, element sets [R16]
// GOAL
//   Remove duplicates from a sorted sequence: the result is strictly increasing and has
//   exactly the same elements.
//
// REFERENCE
//   s[|s| - 1]                            // last element (needs |s| > 0)
//   forall x :: x in r <==> x in a[..i]   // same element set as the scanned prefix
//   assert a[..i + 1] == a[..i] + [a[i]];
//   // Remember the relation between the last element of r and the last element scanned.

// BEGIN SPEC
predicate Sorted(s: seq<int>) { forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j] }

method Dedup(a: seq<int>) returns (r: seq<int>)
  requires Sorted(a)
  ensures forall i, j :: 0 <= i < j < |r| ==> r[i] < r[j]
  ensures forall x :: x in r <==> x in a
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Append a[i] only when it differs from the last element appended.
H2. Because a is sorted, a[i] >= a[i-1] == last(r); "differs" therefore means "is larger".
H3. invariant forall x :: x in r <==> x in a[..i]
    invariant i == 0 ==> |r| == 0
    invariant i > 0 ==> |r| > 0 && r[|r| - 1] == a[i - 1]
*/
