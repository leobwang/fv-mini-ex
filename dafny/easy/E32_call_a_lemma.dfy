// E32 | Call a lemma | 1-2 min | lemma call in a method
// GOAL
//   The body computes the right number, but the verifier cannot connect the closed form to
//   the recursive SumTo. Add one statement.
//
// REFERENCE
//   L(x);                    // inside a method: the ensures of L(x) become known facts
//   // Lemmas are ghost: calling them costs nothing at run time.
//   // The verifier never unfolds a recursive function "all the way" on a symbolic n.

// BEGIN SPEC
function SumTo(n: nat): nat { if n == 0 then 0 else n + SumTo(n - 1) }

lemma SumToFormula(n: nat)
  ensures 2 * SumTo(n) == n * (n + 1)
{
  if n > 0 { SumToFormula(n - 1); }
}

method Gauss(n: nat) returns (s: nat)
  ensures s == SumTo(n)
// END SPEC
{
  // TODO: one line
  s := n * (n + 1) / 2;
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Which given lemma talks about SumTo(n)?
H2. Call it with this n, before or after the assignment.
H3. SumToFormula(n);
*/
