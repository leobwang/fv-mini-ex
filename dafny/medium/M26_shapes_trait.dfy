// M26 | Shapes trait | 10-15 min | trait, extends, override specs, dynamic dispatch
// GOAL
//   Implement Square and Rect so they meet the Shape trait's contract. Client (frozen) must
//   then verify using only the trait's specification for the dispatched call.
//
// REFERENCE
//   trait T { function F(): int reads this   method M() modifies this ensures F() > old(F()) }
//   class C extends T { ... }       // C must implement every bodyless member of T
//   // An override repeats the signature; its ensures must imply the trait's ensures
//   // (restating them is the simple way).
//   var shapes: seq<Shape> := [sq as Shape, r as Shape];   // upcast with "as" in a display

// BEGIN SPEC
trait Shape {
  function Perimeter(): nat
    reads this

  method Grow(d: nat)
    modifies this
    ensures Perimeter() == old(Perimeter()) + 4 * d
}

class Square extends Shape {
  var side: nat

  constructor (s: nat)
    ensures side == s
// END SPEC
  {
  }

// BEGIN SPEC
  function Perimeter(): nat
    reads this
// END SPEC
  {
    0 // TODO
  }

// BEGIN SPEC
  method Grow(d: nat)
    modifies this
    ensures Perimeter() == old(Perimeter()) + 4 * d
// END SPEC
  {
  }
}

// BEGIN SPEC
class Rect extends Shape {
  var w: nat
  var h: nat

  constructor (w0: nat, h0: nat)
    ensures w == w0 && h == h0
// END SPEC
  {
  }

// BEGIN SPEC
  function Perimeter(): nat
    reads this
// END SPEC
  {
    0 // TODO
  }

// BEGIN SPEC
  method Grow(d: nat)
    modifies this
    ensures Perimeter() == old(Perimeter()) + 4 * d
// END SPEC
  {
  }
}

// BEGIN SPEC
method Client()
{
  var sq := new Square(3);
  var r := new Rect(2, 5);
  var shapes: seq<Shape> := [sq as Shape, r as Shape];
  shapes[1].Grow(1);
  assert r.Perimeter() == 18;
  assert sq.Perimeter() == 12;
}
// END SPEC

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Perimeter is the usual formula; Grow adds d to every side length.
H2. Square: 4 * side, side := side + d. Rect: 2 * (w + h), grow both w and h by d.
H3. Rect.Grow: w, h := w + d, h + d;   (2 * ((w + d) + (h + d)) == 2 * (w + h) + 4 * d)
*/
