// E45 | Strip factors of two | 2-3 min | loop decreases, invariant
// GOAL
//   The loop is written. Add the invariant(s) and the termination measure.
//
// REFERENCE
//   while g
//     invariant P
//     decreases e                        // e: int bounded below by 0, or nat; must shrink
//   { ... }
//   // Dafny guesses decreases only from guards like i < n or i != n; "m % 2 == 0" is opaque.

// BEGIN SPEC
function Pow2(n: nat): nat { if n == 0 then 1 else 2 * Pow2(n - 1) }

method StripTwos(n: nat) returns (m: nat, k: nat)
  requires n > 0
  ensures m % 2 == 1 && n == m * Pow2(k)
// END SPEC
{
  m, k := n, 0;
  while m % 2 == 0
    // TODO: invariant(s) and a decreases clause
  {
    m, k := m / 2, k + 1;
  }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. What stays true about n, m and k every time you halve m? Why does halving terminate?
H2. Keep m positive (0 is even, so the loop would never stop on 0) and keep n == m * Pow2(k).
H3. invariant m > 0 && n == m * Pow2(k)    decreases m
*/
