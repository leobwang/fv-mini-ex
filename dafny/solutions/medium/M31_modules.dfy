// M31 | Modules | 10-12 min | module, import, export
// GOAL
//   MathLib exports Abs abstractly: clients see its lemmas but not its body. Implement the
//   library, then the two clients using only what is exported.
//
// REFERENCE
//   module A { export provides F, L   function F(x: int): int { x }  lemma L() ... }
//   // "provides F": clients see F's signature and specs, not its body ("reveals F" would).
//   module B { import opened A   method M() { var y := F(1); } }   // unqualified names
//   module C { import X = A      method M() { var y := X.F(1); } } // qualified via alias

// BEGIN SPEC
module MathLib {
  export provides Abs, AbsNonNeg, AbsNeg, AbsTriangle

  function Abs(x: int): int
// END SPEC
  {
    if x < 0 then -x else x
  }

// BEGIN SPEC
  lemma AbsNonNeg(x: int) ensures Abs(x) >= 0 && (Abs(x) == x || Abs(x) == -x)
// END SPEC
  {}

// BEGIN SPEC
  lemma AbsNeg(x: int) ensures Abs(-x) == Abs(x)
// END SPEC
  {}

// BEGIN SPEC
  lemma AbsTriangle(x: int, y: int) ensures Abs(x + y) <= Abs(x) + Abs(y)
// END SPEC
  {}
}

// BEGIN SPEC
module Client1 {
  import opened MathLib

  method Dist(a: int, b: int) returns (d: int)
    ensures d >= 0 && d == Abs(a - b)
// END SPEC
  {
    AbsNonNeg(a - b);
    d := Abs(a - b);
  }
}

// BEGIN SPEC
module Client2 {
  import M = MathLib

  lemma DistTriangle(a: int, b: int, c: int)
    ensures M.Abs(a - c) <= M.Abs(a - b) + M.Abs(b - c)
// END SPEC
  {
    M.AbsTriangle(a - b, b - c);
    assert (a - b) + (b - c) == a - c;
  }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Inside MathLib, Abs's body is visible, so the lemmas are automatic once Abs is right.
H2. In the clients Abs is opaque: every fact must come from an exported lemma call.
H3. Client1: AbsNonNeg(a - b); d := Abs(a - b);     Client2: M.AbsTriangle(a - b, b - c);
*/
