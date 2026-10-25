// M37 | Filter into a fresh array | 15-20 min | two passes, new array, prefix lemma
// GOAL
//   Copy the positive elements of a, in order, into a new array of exactly the right size:
//   first count them, then allocate and fill.
//
// REFERENCE
//   var b := new int[n];                        // allocate after counting
//   assert a[..i + 1][..i] == a[..i];           // unfold Pos on a growing prefix (E40)
//   b[..j] == Pos(a[..i])                       // slice of an array equals a seq
//   lemma L(s: seq<int>, i: int) requires 0 <= i <= |s| ensures |Pos(s[..i])| <= |Pos(s)|
//   // Writing b[j] needs j < b.Length: relate a prefix's count to the whole count.

// BEGIN SPEC
function Pos(s: seq<int>): seq<int>
{
  if |s| == 0 then []
  else Pos(s[..|s| - 1]) + (if s[|s| - 1] > 0 then [s[|s| - 1]] else [])
}

method FilterPositives(a: array<int>) returns (b: array<int>)
  ensures fresh(b) && b[..] == Pos(a[..])
// END SPEC
{
  var n := 0;
  for i := 0 to a.Length
    invariant n == |Pos(a[..i])|
  {
    assert a[..i + 1][..i] == a[..i];
    if a[i] > 0 { n := n + 1; }
  }
  assert a[..a.Length] == a[..];
  b := new int[n];
  var j := 0;
  for i := 0 to a.Length
    invariant j == |Pos(a[..i])| && j <= n
    invariant b[..j] == Pos(a[..i])
  {
    assert a[..i + 1][..i] == a[..i];
    PrefixCount(a[..], i + 1);
    if a[i] > 0 {
      b[j] := a[i];
      j := j + 1;
    }
  }
}

lemma PrefixCount(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures |Pos(s[..i])| <= |Pos(s)|
  decreases |s|
{
  if i < |s| {
    assert s[..|s| - 1][..i] == s[..i];
    PrefixCount(s[..|s| - 1], i);
  } else {
    assert s[..i] == s;
  }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Pass 1 is E40 with a counter. Pass 2 needs j < b.Length before writing b[j].
H2. Prove |Pos(s[..i])| <= |Pos(s)| by induction on |s| (drop the last element of s). In pass 2
    keep j == |Pos(a[..i])| and b[..j] == Pos(a[..i]).
H3. lemma PrefixCount(s: seq<int>, i: int) requires 0 <= i <= |s| ensures |Pos(s[..i])| <= |Pos(s)|
    (step: assert s[..|s| - 1][..i] == s[..i]; PrefixCount(s[..|s| - 1], i);)
*/
