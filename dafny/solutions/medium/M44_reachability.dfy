// M44 | Reachability | 12-18 min | least predicate, least lemma
// GOAL
//   Ev and CanReach are defined inductively (smallest predicates closed under their rules).
//   Prove facts about them by induction on derivations, and build derivations (ReachFar: every
//   distance n >= 8 is reachable with steps of 3 and 5).
//
// REFERENCE
//   least predicate P(n: int) { n == 0 || P(n - 2) }   // inductive definition
//   least lemma L(n: int) requires P(n) ensures Q(n) { if n != 0 { L(n - 2); } }
//                                       // induction on the derivation of P(n): the recursive
//                                       // call is allowed on the premise that was used
//   lemma M(n: nat) ensures P(2 * n) { if n > 0 { M(n - 1); } }   // build a derivation
//   assert P(2);                                        // the verifier unfolds P a few times

// BEGIN SPEC
least predicate Ev(n: int) { n == 0 || Ev(n - 2) }

least predicate CanReach(x: int, y: int) { x == y || CanReach(x + 3, y) || CanReach(x + 5, y) }

least lemma {:induction false} EvSound(n: int)
  requires Ev(n)
  ensures n >= 0 && n % 2 == 0
// END SPEC
{
  if n != 0 { EvSound(n - 2); }
}

// BEGIN SPEC
lemma {:induction false} EvComplete(n: nat)
  requires n % 2 == 0
  ensures Ev(n)
// END SPEC
{
  if n > 0 { EvComplete(n - 2); }
}

// BEGIN SPEC
least lemma {:induction false} ReachForward(x: int, y: int)
  requires CanReach(x, y)
  ensures x <= y && y != x + 1
// END SPEC
{
  if x != y {
    if CanReach(x + 3, y) {
      ReachForward(x + 3, y);
    } else {
      ReachForward(x + 5, y);
    }
  }
}

// BEGIN SPEC
lemma {:induction false} ReachFar(x: int, n: int)
  requires n >= 8
  ensures CanReach(x, x + n)
  decreases n
// END SPEC
{
  if n == 8 {
    assert CanReach(x + 3, x + 8);
  } else if n == 9 {
    assert CanReach(x + 6, x + 9);
    assert CanReach(x + 3, x + 9);
  } else if n == 10 {
    assert CanReach(x + 5, x + 10);
  } else {
    ReachFar(x + 3, n - 3);
  }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A least lemma may call itself on whichever premise made the predicate true.
H2. EvSound: if n != 0 then Ev(n - 2) holds, recurse. ReachForward: case on which rule fired.
    ReachFar: every n >= 8 is a sum of 3s and 5s. Handle 8, 9, 10 directly (assert the
    intermediate points), and reduce n >= 11 to n - 3 starting from x + 3.
H3. if x != y { if CanReach(x + 3, y) { ReachForward(x + 3, y); } else { ReachForward(x + 5, y); } }
*/
