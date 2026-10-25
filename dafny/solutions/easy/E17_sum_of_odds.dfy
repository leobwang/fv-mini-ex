// E17 | Sum of odd numbers | 2-3 min | lemma, induction
// GOAL
//   Prove 1 + 3 + ... + (2n-1) == n*n by induction: call the lemma on a smaller n.
//
// REFERENCE
//   lemma {:induction false} L(n: nat) ensures P(n)   // turn off automatic induction
//   { if n > 0 { L(n - 1); } }      // recursive call = induction hypothesis for n-1
//   // A lemma call adds its ensures (for those arguments) to what the verifier knows.
//   // Dafny checks that the recursion terminates (decreases n is guessed here).
// NOTE: {:induction false} is part of the spec; without it Dafny would find this proof itself.

// BEGIN SPEC
function OddSum(n: nat): nat { if n == 0 then 0 else OddSum(n - 1) + (2 * n - 1) }

lemma {:induction false} OddSumIsSquare(n: nat)
  ensures OddSum(n) == n * n
// END SPEC
{
  if n > 0 { OddSumIsSquare(n - 1); }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Base case n == 0 is automatic. What do you need to know about OddSum(n - 1)?
H2. In the case n > 0, invoke the induction hypothesis by calling the lemma on n - 1.
H3. if n > 0 { OddSumIsSquare(n - 1); }
*/
