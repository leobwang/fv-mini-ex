// E12 | Rotate left | 1-2 min | seq, slices, concatenation
// GOAL
//   Move the first element of a non-empty sequence to the end.
//
// REFERENCE
//   s: seq<int>   |s|   s[i]                // immutable value type; length; indexing
//   s[..k]   s[k..]   s[i..j]               // prefix (first k), suffix (from k), slice
//   s + t    [x]    []                       // concatenation, singleton, empty
//   [1, 2] + [3] == [1, 2, 3]

// BEGIN SPEC
function RotateLeft(s: seq<int>): seq<int>
  requires |s| > 0
  ensures |RotateLeft(s)| == |s|
  ensures forall i :: 0 <= i < |s| - 1 ==> RotateLeft(s)[i] == s[i + 1]
  ensures RotateLeft(s)[|s| - 1] == s[0]
// END SPEC
{
  s[1..] + [s[0]]
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Split s into its head and its tail.
H2. The tail is a suffix slice; the head becomes a one-element sequence.
H3. s[1..] + [s[0]]
*/
