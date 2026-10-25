// M14 | Sum of a concatenation | 8-12 min | seq induction, extensionality
// GOAL
//   Sum recurses from the front. Prove it distributes over +, then use that to peel the LAST
//   element instead.
//
// REFERENCE
//   assert (a + b)[1..] == a[1..] + b;     // tail of a concatenation (when |a| > 0)
//   assert s == s[..k] + s[k..];           // split a seq at k
//   L(a[1..], b);                          // induction hypothesis on a shorter first argument
//   // Dafny's automatic induction stalls when an extensionality step is missing.

// BEGIN SPEC
function Sum(s: seq<int>): int { if |s| == 0 then 0 else s[0] + Sum(s[1..]) }

lemma SumConcat(a: seq<int>, b: seq<int>)
  ensures Sum(a + b) == Sum(a) + Sum(b)
// END SPEC
{
  if |a| > 0 {
    assert (a + b)[1..] == a[1..] + b;
    SumConcat(a[1..], b);
  } else {
    assert a + b == b;
  }
}

// BEGIN SPEC
lemma SumLast(s: seq<int>)
  requires |s| > 0
  ensures Sum(s) == Sum(s[..|s| - 1]) + s[|s| - 1]
// END SPEC
{
  assert s == s[..|s| - 1] + [s[|s| - 1]];
  SumConcat(s[..|s| - 1], [s[|s| - 1]]);
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Induct on a. What is (a + b)[1..] when a is non-empty?
H2. SumConcat: assert the tail identity, call SumConcat(a[1..], b). SumLast: split s into its
    prefix and its last element, then apply SumConcat.
H3. assert (a + b)[1..] == a[1..] + b; SumConcat(a[1..], b);
    assert s == s[..|s| - 1] + [s[|s| - 1]];
*/
