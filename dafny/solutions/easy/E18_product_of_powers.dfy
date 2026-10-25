// E18 | Product of powers | 2-3 min | calc
// GOAL
//   Prove the three-way product law with a calc chain, using Pow2Add (already proved) as the
//   justification of each step.
//
// REFERENCE
//   calc {
//     A;
//     == { L(x); }            // hint: facts used to justify this step
//     B;
//     == B';                  // a step with no hint
//   }                         // proves A == B'; steps can also use <, <=, ==>
// NOTE: {:induction false} keeps Dafny from proving ThreePowers by itself.

// BEGIN SPEC
function Pow2(n: nat): nat { if n == 0 then 1 else 2 * Pow2(n - 1) }

lemma Pow2Add(a: nat, b: nat)
  ensures Pow2(a + b) == Pow2(a) * Pow2(b)
{
  if a > 0 { Pow2Add(a - 1, b); }
}

lemma {:induction false} ThreePowers(a: nat, b: nat, c: nat)
  ensures Pow2(a + b + c) == Pow2(a) * Pow2(b) * Pow2(c)
// END SPEC
{
  calc {
    Pow2(a + b + c);
    == { Pow2Add(a + b, c); }
    Pow2(a + b) * Pow2(c);
    == { Pow2Add(a, b); }
    Pow2(a) * Pow2(b) * Pow2(c);
  }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. a + b + c parses as (a + b) + c. Split off c first.
H2. Two steps: Pow2Add(a + b, c), then Pow2Add(a, b).
H3. calc { Pow2(a + b + c); == { Pow2Add(a + b, c); } Pow2(a + b) * Pow2(c); == { Pow2Add(a, b); } ... }
*/
