// H08 | Maximum subarray | 30-60 min | Kadane, optimality spec, witness indices
// GOAL
//   Find a contiguous slice a[lo..hi) of maximum sum (the empty slice, sum 0, is allowed) in one
//   pass. Return the sum AND the witness indices; prove no slice has a larger sum.
//
// REFERENCE
//   Sum(s, lo, hi)                        // sum of s[lo..hi); peels off the LAST element
//   Sum(s, p, i + 1) == Sum(s, p, i) + s[i]     // holds by unfolding Sum once
//   invariant forall p :: 0 <= p <= i ==> Sum(a[..], p, i) <= cur
//   best, lo, hi := cur, curLo, i + 1;     // update several outputs at once
//   // Two layers: cur is the best sum of a slice ENDING at i; best is the best so far.

// BEGIN SPEC
function Sum(s: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |s|
  decreases hi - lo
{
  if lo == hi then 0 else Sum(s, lo, hi - 1) + s[hi - 1]
}

method MaxSubarray(a: array<int>) returns (best: int, lo: int, hi: int)
  ensures 0 <= lo <= hi <= a.Length && best == Sum(a[..], lo, hi)
  ensures forall p, q :: 0 <= p <= q <= a.Length ==> Sum(a[..], p, q) <= best
// END SPEC
{
  best, lo, hi := 0, 0, 0;
  var cur, curLo := 0, 0;
  for i := 0 to a.Length
    invariant 0 <= curLo <= i && cur == Sum(a[..], curLo, i)
    invariant forall p :: 0 <= p <= i ==> Sum(a[..], p, i) <= cur
    invariant 0 <= lo <= hi <= i && best == Sum(a[..], lo, hi)
    invariant forall p, q :: 0 <= p <= q <= i ==> Sum(a[..], p, q) <= best
  {
    if cur + a[i] > 0 {
      cur := cur + a[i];
    } else {
      cur, curLo := 0, i + 1;
    }
    if cur > best {
      best, lo, hi := cur, curLo, i + 1;
    }
  }
}

// MILESTONE (optional: change or delete)
// Best sum of a slice ending exactly at i, as a spec: a witness start and an upper bound.
ghost predicate BestEndingAt(s: seq<int>, i: int, cur: int, curLo: int)
  requires 0 <= i <= |s|
{
  0 <= curLo <= i && cur == Sum(s, curLo, i) &&
  forall p :: 0 <= p <= i ==> Sum(s, p, i) <= cur
}

// MILESTONE (optional: change or delete)
// Extending every slice that ends at i by s[i].
lemma ExtendAll(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures forall p :: 0 <= p <= i ==> Sum(s, p, i + 1) == Sum(s, p, i) + s[i]
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Kadane: keep cur, the best sum of a slice ending at the current index (never below 0,
    since the empty slice is allowed), and best, the best seen anywhere.
H2. Step: cur := max(cur + a[i], 0). If you reset to 0, the witness start becomes i + 1. Every
    slice ending at i + 1 is a slice ending at i extended by a[i] (or empty).
H3. invariant 0 <= curLo <= i && cur == Sum(a[..], curLo, i)
    invariant forall p :: 0 <= p <= i ==> Sum(a[..], p, i) <= cur
    invariant 0 <= lo <= hi <= i && best == Sum(a[..], lo, hi)
    invariant forall p, q :: 0 <= p <= q <= i ==> Sum(a[..], p, q) <= best
*/
