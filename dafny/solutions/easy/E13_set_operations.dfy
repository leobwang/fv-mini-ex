// E13 | Set filter and symmetric difference | 1-3 min | set, comprehension
// GOAL
//   Implement both functions with set expressions (no recursion needed).
//
// REFERENCE
//   {1, 2, 3}   {}   x in s   x !in s        // literal, empty set, membership
//   a + b   a * b   a - b                      // union, intersection, difference
//   a <= b   |a|                               // subset, cardinality
//   set x | x in s && x % 2 == 0               // comprehension (must be finite: bound x by s)

// BEGIN SPEC
function Positives(s: set<int>): set<int>
  ensures forall x :: x in Positives(s) <==> x in s && x > 0
// END SPEC
{
  set x | x in s && x > 0
}

// BEGIN SPEC
function SymDiff(a: set<int>, b: set<int>): set<int>
  ensures forall x :: x in SymDiff(a, b) <==> (x in a) != (x in b)
// END SPEC
{
  (a - b) + (b - a)
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. One comprehension, one combination of the three set operators.
H2. "In exactly one of a, b" = in a but not b, or in b but not a.
H3. set x | x in s && x > 0       and       (a - b) + (b - a)
*/
