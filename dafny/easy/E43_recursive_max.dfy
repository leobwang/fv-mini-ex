// E43 | Recursive maximum | 2-3 min | function ensures by recursion, let expression
// GOAL
//   Define SeqMax recursively. Its own ensures, applied to the recursive call, prove it.
//
// REFERENCE
//   var m := F(t); m + 1                 // let expression: bind a name inside an expression
//   if |s| == 1 then s[0] else ...       // the base case for a non-empty seq
//   x in s                               // membership (no index needed)
//   // Proving F's ensures, the verifier assumes F's ensures for each recursive call.

// BEGIN SPEC
function SeqMax(s: seq<int>): int
  requires |s| > 0
  ensures forall i :: 0 <= i < |s| ==> s[i] <= SeqMax(s)
  ensures SeqMax(s) in s
// END SPEC
{
  0 // TODO
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Compare the head with the max of the tail.
H2. A let binding avoids calling SeqMax(s[1..]) twice.
H3. if |s| == 1 then s[0] else var m := SeqMax(s[1..]); if s[0] >= m then s[0] else m
*/
