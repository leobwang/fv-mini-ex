// M02 | Count occurrences | 10-15 min | spec function, helper lemma, seq append [R06]
// GOAL
//   Count how often x occurs in the array. Count recurses from the FRONT but your loop grows
//   a prefix at the BACK, so you need a lemma about Count(s + [y], x).
//
// REFERENCE
//   lemma L(s: seq<int>, y: int) ensures F(s + [y]) == ... { if |s| > 0 { L(s[1..], y); } }
//   assert (s + [y])[1..] == s[1..] + [y];     // extensionality hint inside the lemma
//   assert a[..i + 1] == a[..i] + [a[i]];      // the prefix grows by one element
//   assert a[..a.Length] == a[..];             // after the loop

// BEGIN SPEC
function Count(s: seq<int>, x: int): nat
{
  if |s| == 0 then 0 else (if s[0] == x then 1 else 0) + Count(s[1..], x)
}

method CountOccurrences(a: array<int>, x: int) returns (c: nat)
  ensures c == Count(a[..], x)
// END SPEC
{
  c := 0;
  for i := 0 to a.Length
    invariant c == Count(a[..i], x)
  {
    assert a[..i + 1] == a[..i] + [a[i]];
    CountSnoc(a[..i], a[i], x);
    if a[i] == x { c := c + 1; }
  }
  assert a[..a.Length] == a[..];
}

lemma CountSnoc(s: seq<int>, y: int, x: int)
  ensures Count(s + [y], x) == Count(s, x) + (if y == x then 1 else 0)
{
  if |s| > 0 {
    assert (s + [y])[1..] == s[1..] + [y];
    CountSnoc(s[1..], y, x);
  }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write the loop with invariant c == Count(a[..i], x) and see which step fails.
H2. State and prove a helper lemma CountSnoc by induction on s (recursive call on s[1..]).
H3. lemma CountSnoc(s: seq<int>, y: int, x: int)
      ensures Count(s + [y], x) == Count(s, x) + (if y == x then 1 else 0)
*/
