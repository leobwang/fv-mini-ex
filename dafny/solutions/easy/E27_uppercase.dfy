// E27 | Uppercase string | 2-3 min | string, char, as
// GOAL
//   Write UpChar (lowercase ASCII letter -> uppercase, anything else unchanged) and Upper,
//   which applies it to every character of a string.
//
// REFERENCE
//   string == seq<char>     'a'    "abc"    ""          // char and string literals
//   'a' <= c <= 'z'                                      // chained comparisons on chars
//   c as int     (n as char)                             // conversions (n must be a valid char)
//   [c] + s                                              // strings are seqs: all seq ops work
// NOTE: 'A' as int == 65 and 'a' as int == 97.

// BEGIN SPEC
function UpChar(c: char): char
  ensures 'a' <= c <= 'z' ==> UpChar(c) as int == c as int - 32
  ensures !('a' <= c <= 'z') ==> UpChar(c) == c
// END SPEC
{
  if 'a' <= c <= 'z' then (c as int - 32) as char else c
}

// BEGIN SPEC
function Upper(s: string): string
  ensures |Upper(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> Upper(s)[i] == UpChar(s[i])
// END SPEC
{
  if |s| == 0 then "" else [UpChar(s[0])] + Upper(s[1..])
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. UpChar is a conditional expression with a round trip through int.
H2. Upper recurses on the tail like any seq function.
H3. if 'a' <= c <= 'z' then (c as int - 32) as char else c    and
    if |s| == 0 then "" else [UpChar(s[0])] + Upper(s[1..])
*/
