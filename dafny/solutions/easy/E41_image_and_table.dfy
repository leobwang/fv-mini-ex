// E41 | Set image and map comprehension | 1-3 min | set and map comprehensions
// GOAL
//   Build the set of doubles of s, and a map from each key in s to its square.
//
// REFERENCE
//   set x | x in s :: x + 1               // image: one element per x (after ::)
//   map k | k in s :: k + 1               // map comprehension: key k maps to the value
//   m.Keys                                 // the key set of a map
//   exists y :: y in s && x == f(y)        // "x is in the image of s under f"

// BEGIN SPEC
function Doubles(s: set<int>): set<int>
  ensures forall x :: x in Doubles(s) <==> exists y :: y in s && x == 2 * y
// END SPEC
{
  set y | y in s :: 2 * y
}

// BEGIN SPEC
function SquareTable(s: set<int>): map<int, int>
  ensures SquareTable(s).Keys == s
  ensures forall k :: k in s ==> SquareTable(s)[k] == k * k
// END SPEC
{
  map k | k in s :: k * k
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both are one comprehension.
H2. The part after :: is the element (set) or the value (map).
H3. set y | y in s :: 2 * y      map k | k in s :: k * k
*/
