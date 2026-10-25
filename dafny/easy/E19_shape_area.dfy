// E19 | Shape area | 1-3 min | datatype, match, discriminator, destructor
// GOAL
//   Compute the area of a shape with a match expression.
//
// REFERENCE
//   datatype D = A(x: int) | B(y: int, z: int)   // constructors with named fields
//   match d                                       // match expression: one case per constructor
//   case A(x) => x
//   case B(y, z) => y + z
//   d.A?    d.x                                   // discriminator; destructor (needs d.A?)

// BEGIN SPEC
datatype Shape = Square(side: nat) | Rect(w: nat, h: nat)

function Area(s: Shape): nat
  ensures s.Square? ==> Area(s) == s.side * s.side
  ensures s.Rect? ==> Area(s) == s.w * s.h
// END SPEC
{
  0 // TODO
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. One case per constructor.
H2. Bind the fields in the patterns and multiply.
H3. match s  case Square(a) => a * a  case Rect(w, h) => w * h
*/
