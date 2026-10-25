// M09 | GCD by Euclid | 15-20 min | divisibility, % lemma, invariant over all divisors [R13]
// GOAL
//   Compute gcd(a, b) by Euclid's algorithm. The spec: g divides both, and every common divisor
//   divides g (no recursive gcd function is given).
//
// REFERENCE
//   ghost predicate Divides(d: int, n: int) { exists k :: n == d * k }
//   invariant forall d :: Divides(d, x) && Divides(d, y) <==> Divides(d, a) && Divides(d, b)
//   var i :| x == d * i;                 // unpack a divisibility fact (E42)
//   x == y * (x / y) + x % y             // for y > 0 (the verifier knows this)
//   assert x % y == d * (i - j * q);     // repack with an explicit witness

// BEGIN SPEC
ghost predicate Divides(d: int, n: int) { exists k :: n == d * k }

method Gcd(a: nat, b: nat) returns (g: nat)
  ensures Divides(g, a) && Divides(g, b)
  ensures forall d :: Divides(d, a) && Divides(d, b) ==> Divides(d, g)
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Loop x, y := y, x % y until y == 0. The answer is x. What does the loop preserve?
H2. The set of common divisors of (x, y) never changes. Prove a lemma for one step, then use a
    forall statement (E24) to lift it to all d. At the end, x divides x and 0.
H3. lemma ModStep(x: nat, y: nat, d: int) requires y > 0
      ensures Divides(d, x) && Divides(d, y) <==> Divides(d, y) && Divides(d, x % y)
*/
