// E21 | Distance on nat | 1-2 min | nat subtraction
// GOAL
//   Return the distance between two naturals.
//
// REFERENCE
//   a - b                         // on nat operands this is int subtraction: may be negative
//   var d: nat := a - b;          // verification error unless a >= b is known here
//   if a >= b { ... } else { ... }
// NOTE: there is no saturating "monus" on nat; the subset check rejects a negative result.

// BEGIN SPEC
method Dist(a: nat, b: nat) returns (d: nat)
  ensures a + d == b || b + d == a
// END SPEC
{
  if a >= b { d := a - b; } else { d := b - a; }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. "d := a - b" alone fails: why?
H2. Subtract the smaller from the larger.
H3. if a >= b { d := a - b; } else { d := b - a; }
*/
