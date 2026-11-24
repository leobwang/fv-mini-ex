/- M066 | Bernoulli's inequality | 10-15 min | induction, nlinarith, casts, mathlib
GOAL
  Prove `n + 1 ≤ 2 ^ n`, then Bernoulli's inequality `1 + n x ≤ (1 + x) ^ n` for `x ≥ -1`.
BANNED: one_add_mul_le_pow, Nat.lt_two_pow_self, Nat.lt_pow_self, one_add_mul_self_le_pow

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M066

/- SKELETON · succ_le_two_pow
  1. Induct on `n`; cases `zero` and `succ n ih`:                                       R1
  2. `zero`: the goal `0 + 1 ≤ 2 ^ 0` is closed by `simp`:                              R2
  3. `succ`: peel one factor `2` off `2 ^ (n + 1)` so the `2 ^ n` of `ih` appears:      R4
     then the goal is linear in `n` and the atom `2 ^ n`; close it from `ih`:           R5
-/
-- BEGIN SPEC
theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n :=
-- END SPEC
  sorry

/- SKELETON · bernoulli
  1. Induct on `n` (`hx` stays in the context); cases `zero` and `succ n ih`:           R1
  2. `zero`: the goal `1 + ↑0 * x ≤ (1 + x) ^ 0` is closed by `simp`:                   R3, R2
  3. `succ`: first the two facts
       h1 : 0 ≤ 1 + x                                  from `hx`:                      have, R6
       h2 : (1 + ↑n * x) * (1 + x) ≤ (1 + x) ^ n * (1 + x)   `ih` times `h1`:          have, R7
  4. Make the goal speak about the atoms of `h2`:
       `↑(n + 1)` → `↑n + 1`                                                            R8
       `(1 + x) ^ (n + 1)` → `(1 + x) ^ n * (1 + x)`                                    R4
  5. Close the polynomial goal from `h2`, giving it the one fact it cannot guess,
       0 ≤ ↑n * x ^ 2                                  as a hint term:                  R12 with R11 (R9, R10)
-/
-- BEGIN SPEC
theorem bernoulli (x : ℝ) (hx : -1 ≤ x) (n : ℕ) : 1 + n * x ≤ (1 + x) ^ n :=
-- END SPEC
  sorry

end M066

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both are inductions on `n`; the step multiplies the IH by `2` (resp. by `1 + x`, which is `≥ 0`
    because `x ≥ -1`).
H2. Bernoulli step: `(1 + x)^(n+1) = (1 + x)^n (1 + x) ≥ (1 + n x)(1 + x) = 1 + (n+1) x + n x² ≥ 1 + (n+1) x`.
    In Lean: `have` the product inequality (R7), `push_cast` and `rw [pow_succ]` so the goal matches
    it, then `nlinarith` with `0 ≤ n x²` as a hint.
H3. `have h2 := mul_le_mul_of_nonneg_right ih h1; push_cast; rw [pow_succ]; nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) (sq_nonneg x)]`.
-/
