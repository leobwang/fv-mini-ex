// E38 | Compose | 1-2 min | function types, lambdas
// GOAL
//   Return functions: the composition f after g, and f applied twice.
//
// REFERENCE
//   f: int -> int                        // total function type (no reads, no precondition)
//   f(3)                                 // apply
//   x => f(x) + 1                        // lambda; its type is inferred
//   function K(c: int): int -> int { x => c }   // functions can return functions

// BEGIN SPEC
function Compose(f: int -> int, g: int -> int): int -> int
  ensures forall x :: Compose(f, g)(x) == f(g(x))
// END SPEC
{
  x => 0 // TODO
}

// BEGIN SPEC
function Twice(f: int -> int): int -> int
  ensures forall x :: Twice(f)(x) == f(f(x))
// END SPEC
{
  f // TODO
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each body is a lambda (or a call that returns one).
H2. Twice is a special case of Compose.
H3. x => f(g(x))      Compose(f, f)
*/
