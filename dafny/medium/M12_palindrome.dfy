// M12 | Palindrome check | 5-10 min | two pointers, string [R17]
// GOAL
//   Decide whether s reads the same forwards and backwards, comparing from both ends.
//
// REFERENCE
//   var i, j := 0, |s| - 1;            // |s| - 1 may be -1 for the empty string: fine for int
//   while i < j                         // stop when the pointers meet or cross
//   invariant j == |s| - 1 - i          // tie the two pointers together
//   return false;

// BEGIN SPEC
method IsPalindrome(s: string) returns (b: bool)
  ensures b <==> forall i :: 0 <= i < |s| ==> s[i] == s[|s| - 1 - i]
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Compare s[i] and s[j], move both inward.
H2. Invariants: j is the mirror of i, and the outer pairs checked so far match.
H3. invariant 0 <= i <= |s| && j == |s| - 1 - i
    invariant forall k :: 0 <= k < i ==> s[k] == s[|s| - 1 - k]
*/
