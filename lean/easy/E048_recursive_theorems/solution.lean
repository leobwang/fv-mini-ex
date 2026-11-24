/- E048 | Recursive theorems | 3-5 min | recursion, match, two-step induction
GOAL
  Prove `fib n < 2 ^ n` and two facts about a two-step parity test `evenB` with theorems that call
  themselves on smaller arguments from the `n + 2` case: a proof by induction is a recursive function.

BANNED: induction, grind, fun_induction, fun_cases, Nat.rec, Nat.recOn, Nat.casesOn, Nat.recAux, Nat.casesAuxOn, Nat.div2Induction, Nat.strongRecOn, Nat.caseStrongRecOn, exact?, apply?, try?

GUIDE
  Entries R1–R11: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E048

-- BEGIN SPEC
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
-- END SPEC

-- BEGIN SPEC
def evenB : Nat → Bool
  | 0 => true
  | 1 => false
  | n + 2 => evenB n
-- END SPEC

/- SKELETON · fib_lt_two_pow
  1. Split `n` into `fib`'s three cases `0`, `1`, `n + 2`:                  R1
  2. Cases `0` and `1`: closed computations:                                 R2
  3. Case `n + 2`: two recursive calls, at `n` and at `n + 1`:               R3, R3
       h1 : fib n < 2 ^ n      h2 : fib (n + 1) < 2 ^ (n + 1)
  4. One `simp only [...] at *` (R5) listing both `fib` (R4) and
     `Nat.pow_succ` (R6): it unfolds `fib (n + 2)` and turns every
     `2 ^ (k + 1)` into `2 ^ k * 2`, in the goal and in h1, h2:               R4, R6, R5
       h2 : fib (n + 1) < 2 ^ n * 2    ⊢ fib n + fib (n + 1) < 2 ^ n * 2 * 2
  5. Linear arithmetic, `2 ^ n` and `fib _` as unknowns:                     R7
-/
-- BEGIN SPEC
theorem fib_lt_two_pow (n : Nat) : fib n < 2 ^ n :=
-- END SPEC
  match n with
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
    have h1 := fib_lt_two_pow n
    have h2 := fib_lt_two_pow (n + 1)
    simp only [fib, Nat.pow_succ] at *
    omega

/- SKELETON · evenB_double
  1. Split `n` into `0` and `n + 1`:                                         R8
  2. Case `0`: `evenB (2 * 0)` computes to `true`:                           R9
  3. Case `n + 1`: restate the goal as `evenB (2 * n + 2) = true`:           R10
  4. Unfold one `evenB` step:                                                R4
  5. The goal is the statement at `n`: recursive call:                       R11
-/
-- BEGIN SPEC
theorem evenB_double (n : Nat) : evenB (2 * n) = true :=
-- END SPEC
  match n with
  | 0 => rfl
  | n + 1 => by
    show evenB (2 * n + 2) = true
    simp only [evenB]
    exact evenB_double n

/- SKELETON · evenB_double_add_one
  1. Split `n` into `0` and `n + 1`:                                         R8
  2. Case `0`: `evenB (2 * 0 + 1)` computes to `false`:                      R9
  3. Case `n + 1`: restate the goal with `+ 2` outermost,
     `evenB (2 * n + 1 + 2) = false`:                                        R10
  4. Unfold one `evenB` step:                                                R4
  5. The goal is the statement at `n`: recursive call:                       R11
-/
-- BEGIN SPEC
theorem evenB_double_add_one (n : Nat) : evenB (2 * n + 1) = false :=
-- END SPEC
  match n with
  | 0 => rfl
  | n + 1 => by
    show evenB (2 * n + 1 + 2) = false
    simp only [evenB]
    exact evenB_double_add_one n

end E048

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Mirror the definitions. `fib` has cases `0`, `1`, `n + 2`, so `fib_lt_two_pow` can too, and from the
    case `n + 2` you may call `fib_lt_two_pow n` and `fib_lt_two_pow (n + 1)`: two IHs (R1, R3). For
    `evenB`, split `n` as `0 | n + 1`: `2 * (n + 1)` is `2 * n + 2` by computation (R8, R10).
H2. `fib_lt_two_pow`: `match n with | 0 => by decide | 1 => by decide | n + 2 => by …`; in the last case
    add both IHs, unfold `fib` and the powers everywhere, then `omega` (R2, R3, R4–R6, R7).
    `evenB_double(_add_one)`: `match n with | 0 => rfl | n + 1 => by …`; `show` the argument as `_ + 2`,
    unfold one `evenB` step, finish with the recursive call (R9, R10, R4, R11).
H3. `fib_lt_two_pow`, last case: `have h1 := fib_lt_two_pow n; have h2 := fib_lt_two_pow (n + 1)`, then
    `simp only [fib, Nat.pow_succ] at *; omega`.
    `evenB_double`, last case: `show evenB (2 * n + 2) = true; simp only [evenB]; exact evenB_double n`.
    `evenB_double_add_one`, last case: `show evenB (2 * n + 1 + 2) = false`, then the same two steps.
-/
