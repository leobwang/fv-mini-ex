// M19 | Ackermann | 10-15 min | lexicographic decreases, induction
// GOAL
//   Prove closed forms of Ack(1, n) and Ack(2, n), and make the Drain loop provably terminate.
//
// REFERENCE
//   decreases m, n          // lexicographic: m shrinks, or m stays and n shrinks
//                           // (n may grow arbitrarily when m shrinks)
//   // Functions default to "decreases <params in order>"; loops guess only from the guard.
//   lemma {:induction false} L(n: nat) ensures P(n) { if n > 0 { L(n - 1); } }

// BEGIN SPEC
function Ack(m: nat, n: nat): nat
  decreases m, n
{
  if m == 0 then n + 1
  else if n == 0 then Ack(m - 1, 1)
  else Ack(m - 1, Ack(m, n - 1))
}

lemma {:induction false} Ack1(n: nat)
  ensures Ack(1, n) == n + 2
// END SPEC
{
}

// BEGIN SPEC
lemma {:induction false} Ack2(n: nat)
  ensures Ack(2, n) == 2 * n + 3
// END SPEC
{
}

// BEGIN SPEC
method Drain(m0: nat, n0: nat)
// END SPEC
{
  var m, n := m0, n0;
  while m > 0 || n > 0
    // TODO: termination measure
  {
    if n > 0 {
      n := n - 1;
    } else {
      m, n := m - 1, 100;
    }
  }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold Ack(1, n) and Ack(2, n) once by hand: which smaller instances appear?
H2. Ack(1, n) = Ack(0, Ack(1, n - 1)): induction on n. Ack(2, n) = Ack(1, Ack(2, n - 1)): induction
    plus Ack1 at the argument Ack(2, n - 1). Drain: the pair (m, n) decreases lexicographically.
H3. Ack2: if n == 0 { Ack1(1); } else { Ack2(n - 1); Ack1(Ack(2, n - 1)); }    decreases m, n
*/
