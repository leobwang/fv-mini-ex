// E35 | Integer range | 1-2 min | seq comprehension, lambda
// GOAL
//   Build both sequences with a seq comprehension (no recursion).
//
// REFERENCE
//   seq(5, i => i * i)                   // [0, 1, 4, 9, 16]: length and a function of the index
//   seq(n, i requires 0 <= i < n => s[i])    // a lambda may carry a precondition
//   x => x + 1    (x: int) => x + 1      // lambda expressions

// BEGIN SPEC
function Range(lo: int, hi: int): seq<int>
  requires lo <= hi
  ensures |Range(lo, hi)| == hi - lo
  ensures forall i :: 0 <= i < hi - lo ==> Range(lo, hi)[i] == lo + i
// END SPEC
{
  [] // TODO
}

// BEGIN SPEC
function Reversed(s: seq<int>): seq<int>
  ensures |Reversed(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> Reversed(s)[i] == s[|s| - 1 - i]
// END SPEC
{
  [] // TODO
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. seq(length, function-of-index).
H2. For Reversed, the lambda indexes into s, so it needs a precondition bounding i.
H3. seq(hi - lo, i => lo + i)      seq(|s|, i requires 0 <= i < |s| => s[|s| - 1 - i])
*/
