// M43 | Sum of cubes | 15-20 min | nonlinear induction, calc
// GOAL
//   Prove Nicomachus' theorem: 1^3 + ... + n^3 == (1 + ... + n)^2.
//
// REFERENCE
//   calc {
//     X * X;
//     == (A + n) * (A + n);
//     == A * A + 2 * n * A + n * n;        // the solver needs small nonlinear steps
//     == { L(n - 1); } ...;                // justify a step with a lemma
//   }
//   lemma {:induction false} G(n: nat) ensures 2 * T(n) == n * (n + 1) { if n > 0 { G(n - 1); } }

// BEGIN SPEC
function SumTo(n: nat): nat { if n == 0 then 0 else SumTo(n - 1) + n }

function SumCubes(n: nat): nat { if n == 0 then 0 else SumCubes(n - 1) + n * n * n }

lemma {:induction false} Nicomachus(n: nat)
  ensures SumCubes(n) == SumTo(n) * SumTo(n)
// END SPEC
{
  if n > 0 {
    var a := SumTo(n - 1);
    Gauss(n - 1);
    calc {
      SumTo(n) * SumTo(n);
      == (a + n) * (a + n);
      == a * a + 2 * a * n + n * n;
      == { Nicomachus(n - 1); }
      SumCubes(n - 1) + 2 * a * n + n * n;
      == { assert 2 * a == (n - 1) * n; }
      SumCubes(n - 1) + (n - 1) * n * n + n * n;
      == SumCubes(n - 1) + n * n * n;
    }
  }
}

lemma Gauss(n: nat)
  ensures 2 * SumTo(n) == n * (n + 1)
{}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write SumTo(n) = SumTo(n - 1) + n and expand the square.
H2. You need Gauss: 2 * SumTo(n) == n * (n + 1), and the induction hypothesis for n - 1. Then
    2 * SumTo(n - 1) * n == (n - 1) * n * n, and (n - 1) * n * n + n * n == n * n * n.
H3. calc { SumTo(n) * SumTo(n); == (a + n) * (a + n); == a * a + 2 * a * n + n * n;
           == { Nicomachus(n - 1); } SumCubes(n - 1) + 2 * a * n + n * n; == ... }
*/
