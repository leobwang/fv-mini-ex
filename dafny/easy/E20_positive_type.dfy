// E20 | Positive integers | 1-3 min | subset type, witness, nat
// GOAL
//   Make Pos a legal type (add a witness on the TODO line), then implement Add and Pred.
//   Every value you return must provably satisfy its type's constraint.
//
// REFERENCE
//   type Small = x: int | 0 <= x < 10           // subset type: int values satisfying the predicate
//     witness 3                                 // an inhabitant (Dafny tries 0 by default)
//   nat                                         // built in: x: int | 0 <= x
//   var s: Small := 7;                          // membership is checked by the verifier

// BEGIN SPEC
type Pos = x: int | x > 0
// END SPEC
  // TODO: Dafny tries witness 0, which is not a Pos

// BEGIN SPEC
function Add(a: Pos, b: Pos): Pos
  ensures Add(a, b) == a + b
// END SPEC
{
  0 // TODO
}

// BEGIN SPEC
function Pred(p: Pos): nat
  ensures Pred(p) + 1 == p
// END SPEC
{
  0 // TODO
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The error "cannot find witness" means the default 0 is not in the type.
H2. Any positive literal works as a witness. The function bodies are one-liners.
H3. witness 1      a + b      p - 1
*/
