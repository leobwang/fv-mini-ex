// E36 | Mean of two | 1-3 min | real, as real, Floor
// GOAL
//   Implement Mean on reals, then use it on integers (convert first) and round down.
//
// REFERENCE
//   x: real    1.5    2.0    0.0             // real literals need a decimal point
//   n as real                                // int -> real
//   r.Floor                                  // largest int <= r
//   a / b                                    // real division (b != 0.0 must be provable)

// BEGIN SPEC
function Mean(a: real, b: real): real
  ensures Mean(a, b) - a == b - Mean(a, b)
// END SPEC
{
  0.0 // TODO
}

// BEGIN SPEC
method FloorMean(x: int, y: int) returns (f: int)
  ensures f as real <= Mean(x as real, y as real) < f as real + 1.0
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Mean is the midpoint. FloorMean converts, calls Mean, rounds down.
H2. "2" is an int; a real literal is written 2.0.
H3. (a + b) / 2.0      f := Mean(x as real, y as real).Floor;
*/
