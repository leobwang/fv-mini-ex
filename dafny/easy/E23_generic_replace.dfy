// E23 | Generic replace | 2-3 min | generics, T(==), recursion on seq
// GOAL
//   Replace every occurrence of x in s by y, for any element type that supports ==.
//
// REFERENCE
//   function Id<T>(x: T): T { x }               // type parameter
//   function Eq<T(==)>(a: T, b: T): bool { a == b }  // (==): T must support equality
//   s[0]   s[1..]                                // head and tail of a non-empty seq
//   if |s| == 0 then [] else [s[0]] + s[1..]     // the usual recursion shape
//   // A recursive call's ensures are available when proving the caller's ensures.

// BEGIN SPEC
function Replace<T(==)>(s: seq<T>, x: T, y: T): seq<T>
  ensures |Replace(s, x, y)| == |s|
  ensures forall i :: 0 <= i < |s| ==> Replace(s, x, y)[i] == (if s[i] == x then y else s[i])
// END SPEC
{
  [] // TODO
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Recurse on the tail.
H2. Empty in, empty out. Otherwise fix up the head and prepend it to the recursive result.
H3. if |s| == 0 then [] else [if s[0] == x then y else s[0]] + Replace(s[1..], x, y)
*/
