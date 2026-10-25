// E40 | Slice of a slice | 3 min | seq extensionality, assert
// GOAL
//   Prove SumSnoc, then use it to verify the loop in SumArray.
//
// REFERENCE
//   assert s[..i+1][..i] == s[..i];      // seq equality the verifier won't invent itself;
//                                        // once stated, it is proved element-wise
//   assert a[..a.Length] == a[..];       // the classic step after a loop over an array
//   L(a[..], i);                         // pass the array's contents as a seq
//   // Sum peels off the LAST element, so Sum(s[..i+1]) unfolds to Sum(s[..i+1][..i]) + s[i].

// BEGIN SPEC
function Sum(s: seq<int>): int { if |s| == 0 then 0 else Sum(s[..|s| - 1]) + s[|s| - 1] }

lemma SumSnoc(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures Sum(s[..i + 1]) == Sum(s[..i]) + s[i]
// END SPEC
{
}

// BEGIN SPEC
method SumArray(a: array<int>) returns (t: int)
  ensures t == Sum(a[..])
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold Sum(s[..i+1]) by hand: which sequence does the recursive call see?
H2. SumSnoc needs one assert. In the loop, call SumSnoc(a[..], i); after it, relate a[..a.Length]
    and a[..].
H3. assert s[..i + 1][..i] == s[..i];      loop invariant t == Sum(a[..i])
*/
