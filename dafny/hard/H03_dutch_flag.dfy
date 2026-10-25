// H03 | Dutch national flag | 30-60 min | three-way partition, multiset, milestones [R19]
// GOAL
//   Rearrange the colors in ONE pass so all Reds come first, then Whites, then Blues; return
//   the two boundaries. The result must be a permutation of the input.
//
// REFERENCE
//   datatype Color = Red | White | Blue           // an enumeration
//   a[i] == Red     a[i].Blue?                     // compare, or use a discriminator
//   a[i], a[j] := a[j], a[i];                      // swap (multiset is preserved)
//   invariant forall k :: 0 <= k < r ==> a[k] == Red
//   // Four zones: Red [0, r), White [r, w), unknown [w, b), Blue [b, n).
//   invariant Zones(a[..], r, w, b)               // a predicate over a[..] works as an invariant

// BEGIN SPEC
datatype Color = Red | White | Blue

method DutchFlag(a: array<Color>) returns (r: int, w: int)
  modifies a
  ensures 0 <= r <= w <= a.Length
  ensures forall i :: 0 <= i < r ==> a[i] == Red
  ensures forall i :: r <= i < w ==> a[i] == White
  ensures forall i :: w <= i < a.Length ==> a[i] == Blue
  ensures multiset(a[..]) == multiset(old(a[..]))
// END SPEC
{
}

// MILESTONE (optional: change or delete)
// The loop invariant, packaged as a predicate over the zones.
ghost predicate Zones(s: seq<Color>, r: int, w: int, b: int)
{
  0 <= r <= w <= b <= |s| &&
  (forall i :: 0 <= i < r ==> s[i] == Red) &&
  (forall i :: r <= i < w ==> s[i] == White) &&
  (forall i :: b <= i < |s| ==> s[i] == Blue)
}

// MILESTONE (optional: change or delete)
method Swap(a: array<Color>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
  ensures a[i] == old(a[j]) && a[j] == old(a[i])
  ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Keep three boundaries r <= w <= b and look at a[w] (the first unknown element).
H2. Red: swap it to position r and advance both r and w. White: advance w. Blue: shrink b and
    swap a[w] with a[b] (do not advance w: the element that arrived is still unknown).
H3. invariant 0 <= r <= w <= b <= a.Length, plus one forall per colored zone, plus
    multiset(a[..]) == multiset(old(a[..])); decreases b - w
*/
