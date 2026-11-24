/- E011 | omega | 1-3 min | omega, Nat subtraction, Int, casts
GOAL
  Discharge linear arithmetic over `Nat` and `Int` with `omega`, including truncated subtraction.

GUIDE
  Entries R1–R6: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · sub_add_cancel_nat
  1. Check the claim in the truncated case: without `h` it fails at `n = 0, m = 1`
     (`0 - 1 + 1 = 1`), so `h : m ≤ n` must stay in the context:          W1
  2. Linear `Nat` goal with `-`, `h` in the context; close in one step:     R1, R2
-/
-- BEGIN SPEC
theorem sub_add_cancel_nat (n m : Nat) (h : m ≤ n) : n - m + m = n :=
-- END SPEC
  sorry

/- SKELETON · truncated
  1. The subtrahend `n + 3` is larger than `n`, so the difference truncates;
     `n ≤ n + 3` is linear, no hypothesis needed:                            W1
  2. Close in one step:                                                     R3
-/
-- BEGIN SPEC
theorem truncated (n : Nat) : n - (n + 3) = 0 :=
-- END SPEC
  sorry

/- SKELETON · solve_system
  1. Two linear equations over `Int` in `h1`, `h2`; the goal is a `∧`, which
     need not be split first:                                                R4
  2. Close both conjuncts in one step:                                      R4
-/
-- BEGIN SPEC
theorem solve_system (x y : Int) (h1 : 2 * x + y = 7) (h2 : x - y = 2) : x = 3 ∧ y = 1 :=
-- END SPEC
  sorry

/- SKELETON · cast_sub
  1. Read the goal: `↑(n - 1)` truncates (`Nat`), `↑n - 1` does not (`Int`);
     the two cases are `n = 0` (`0 ≥ -1`) and `n ≥ 1` (equal sides):         R2, R5
  2. Close in one step; the case split on `n - 1` is done for you:          R5
-/
-- BEGIN SPEC
theorem cast_sub (n : Nat) : ((n - 1 : Nat) : Int) ≥ (n : Int) - 1 :=
-- END SPEC
  sorry

/- SKELETON · mod_fact
  1. `% 4` and `% 2` have numeral divisors, so they are linear:             R6
  2. `h : a % 4 = 3` is in the context; close in one step:                  R1, R6
-/
-- BEGIN SPEC
theorem mod_fact (a : Nat) (h : a % 4 = 3) : a % 2 = 1 :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every hypothesis and goal here is linear arithmetic over `Nat` or `Int`: numerals are the only
    multipliers and divisors, and `↑` only casts `Nat` into `Int` (R1–R6).
H2. One decision procedure covers all five; it reads `h`, `h1`, `h2` from the context by itself and
    does the truncation case splits (R2, R5) and the remainder bookkeeping (R6) itself.
H3. Each proof is the single tactic `omega`.
-/
