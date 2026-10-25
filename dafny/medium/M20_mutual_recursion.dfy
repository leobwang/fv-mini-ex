// M20 | Mutual recursion | 10-15 min | mutually recursive predicates and lemmas
// GOAL
//   Define IsEven and IsOdd in terms of each other (no %), then prove they agree with n % 2.
//
// REFERENCE
//   predicate A(n: nat) { n == 0 || B(n - 1) }     // A calls B ...
//   predicate B(n: nat) { n > 0 && A(n - 1) }      // ... and B calls A: termination by n
//   lemma {:induction false} LA(n: nat) ensures ... { if n > 0 { LB(n - 1); } }
//   lemma {:induction false} LB(n: nat) ensures ... { if n > 0 { LA(n - 1); } }

// BEGIN SPEC
predicate IsEven(n: nat)
// END SPEC
{
  false // TODO
}

// BEGIN SPEC
predicate IsOdd(n: nat)
// END SPEC
{
  false // TODO
}

// BEGIN SPEC
lemma {:induction false} EvenMod(n: nat)
  ensures IsEven(n) <==> n % 2 == 0
// END SPEC
{
}

// BEGIN SPEC
lemma {:induction false} OddMod(n: nat)
  ensures IsOdd(n) <==> n % 2 == 1
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. 0 is even and not odd; n is even iff n - 1 is odd, and vice versa.
H2. The lemmas follow the definitions: each calls the *other* lemma on n - 1.
H3. predicate IsEven: if n == 0 then true else IsOdd(n - 1)      EvenMod: if n > 0 { OddMod(n - 1); }
*/
