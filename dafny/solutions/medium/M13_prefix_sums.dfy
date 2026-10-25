// M13 | Prefix sums | 8-12 min | new array, sum lemma, slices [R18]
// GOAL
//   Return p with p[i] = a[0] + ... + a[i-1] (so p[0] = 0), computed in one pass.
//
// REFERENCE
//   p := new int[a.Length];              // allocate (then fill it)
//   assert a[..i + 1][..i] == a[..i];    // the E40 step for Sum
//   invariant forall k :: 0 <= k < i ==> p[k] == Sum(a[..k])
//   // p is fresh, so writing p cannot change a (no aliasing).

// BEGIN SPEC
function Sum(s: seq<int>): int { if |s| == 0 then 0 else Sum(s[..|s| - 1]) + s[|s| - 1] }

method PrefixSums(a: array<int>) returns (p: array<int>)
  ensures fresh(p) && p.Length == a.Length
  ensures forall i :: 0 <= i < a.Length ==> p[i] == Sum(a[..i])
// END SPEC
{
  p := new int[a.Length];
  var acc := 0;
  for i := 0 to a.Length
    invariant acc == Sum(a[..i])
    invariant forall k :: 0 <= k < i ==> p[k] == Sum(a[..k])
  {
    p[i] := acc;
    assert a[..i + 1][..i] == a[..i];
    acc := acc + a[i];
  }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Keep a running total acc; write it before adding a[i].
H2. Invariants: acc == Sum(a[..i]) and all written entries are correct.
H3. invariant acc == Sum(a[..i])  invariant forall k :: 0 <= k < i ==> p[k] == Sum(a[..k])
    (step: assert a[..i + 1][..i] == a[..i];)
*/
