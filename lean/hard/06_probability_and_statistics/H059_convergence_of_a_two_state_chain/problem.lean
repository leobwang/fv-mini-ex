/- H059 | Convergence of a 2-state chain | 45-60 min | Markov chain, matrix powers, induction, limits, mathlib
GOAL
  The chain on `{0, 1}` with transition matrix `P a b` jumps `0 → 1` w.p. `a` and `1 → 0` w.p. `b`. Prove
  `Pⁿ = Π + (1 - a - b)ⁿ • (1 - Π)`, where both rows of `Π = Pinf a b` are `π = (b, a) / (a + b)`, and that
  `(Pⁿ) i j → π j` as `n → ∞` from either start `i` when `0 < a + b < 2`.

GUIDE
  Entries R1–R34: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H059

open Filter Topology

-- BEGIN SPEC
/-- the transition matrix: row `i` is the distribution of the next state from state `i` -/
def P (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1 - a, a; b, 1 - b]

/-- the limit matrix: both rows equal the stationary distribution `(b, a) / (a + b)` -/
noncomputable def Pinf (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![b / (a + b), a / (a + b); b / (a + b), a / (a + b)]
-- END SPEC

/- SKELETON · P_mul_Pinf   (MILESTONE 1: used in `P_mul_one_sub` and in the step of `pow_formula`)
  1. Matrix equation → four entry goals:                                    R1, R2
  2. Evaluate each entry: `simp` with `P`, `Pinf` and the product lemmas     R3, R4, R5, R6
       goal (entry 0,0): `(1 - a) * (b / (a + b)) + a * (b / (a + b)) = b / (a + b)`
  3. Clear the denominator `a + b` (needs `hab`), then finish:                R7 → R8
-/
-- MILESTONE (optional: change or delete)
theorem P_mul_Pinf (a b : ℝ) (hab : a + b ≠ 0) : P a b * Pinf a b = Pinf a b := by
  sorry

/- SKELETON · P_mul_one_sub   (MILESTONE 2: used in the step of `pow_formula`)
  1. Distribute, drop `* 1`, then MILESTONE 1, all at the matrix level:       R9, R10, rw [P_mul_Pinf a b hab]
       goal: `P a b - Pinf a b = (1 - a - b) • (1 - Pinf a b)`
  2. Matrix equation → four entry goals:                                    R1, R2
  3. Evaluate the entries: `simp [P, Pinf]`                                  R3, R4, R11, R12, R13
       goal (entry 0,0): `1 - a - b / (a + b) = (1 - a - b) * (1 - b / (a + b))`
  4. Clear the denominator, then finish:                                     R7 → R8
-/
-- MILESTONE (optional: change or delete)
theorem P_mul_one_sub (a b : ℝ) (hab : a + b ≠ 0) :
    P a b * (1 - Pinf a b) = (1 - a - b) • (1 - Pinf a b) := by
  sorry

/- SKELETON · abs_lt_one   (MILESTONE 3: the hypothesis of R25 in `converges`)
  1. Absolute value → two inequalities:                                     R14
  2. Split; each half is linear in `a + b`:                                  constructor, then R15 on both
-/
-- MILESTONE (optional: change or delete)
theorem abs_lt_one (a b : ℝ) (hab : 0 < a + b) (hab2 : a + b < 2) : |1 - a - b| < 1 := by
  sorry

/- SKELETON · pow_formula
  Prove MILESTONES 1 and 2 first: step 3 uses both.
  1. Induction on `n`:                                                       R16
  2. `zero`: plain `simp` closes it (`P a b ^ 0 = 1`, `1 • M = M`, `Π + (1 - Π) = 1`)   R17, R18, R19
  3. `succ n ih`: one `rw` chain, in this order:
       peel one `P a b` off on the LEFT, then substitute the IH               R20, rw [ih]
       distribute `P a b *` over `+`                                         R21
       move the scalar `(1 - a - b) ^ n` out of the product                  R22
       MILESTONE 1, then MILESTONE 2                                         rw [P_mul_Pinf …, P_mul_one_sub …]
         goal: `Pinf a b + (1 - a - b) ^ n • (1 - a - b) • (1 - Pinf a b) =
                Pinf a b + (1 - a - b) ^ (n + 1) • (1 - Pinf a b)`
       merge the two scalars, unfold `^ (n + 1)` on the right (`rw` closes by `rfl`)   R23, R24
-/
-- BEGIN SPEC
theorem pow_formula (a b : ℝ) (hab : a + b ≠ 0) (n : ℕ) :
    P a b ^ n = Pinf a b + (1 - a - b) ^ n • (1 - Pinf a b) :=
-- END SPEC
  sorry

/- SKELETON · converges
  Uses MILESTONE 3 and `pow_formula` (prove them first). `ha ha1 hb hb1` are not needed.
  1. `h0 : Tendsto (fun n => (1 - a - b) ^ n) atTop (𝓝 0)`:                 R25 with `abs_lt_one a b hab hab2`
  2. Under `fun n =>`: rewrite with `pow_formula` (its `a + b ≠ 0` is R26), then split the entry
                                                                             R27, R26, R28, R13
       goal: `Tendsto (fun n => Pinf a b i j + (1 - a - b) ^ n * (1 - Pinf a b) i j) atTop (𝓝 (![…] j))`
  3. `h`: the limit of that sequence as constant + h0 * constant:            R29, R30, R31
       its limit is `Pinf a b i j + 0 * (1 - Pinf a b) i j`
  4. Clean that limit in `h`:                                                R32
  5. Match the goal with `h`; leftover `![b / (a + b), a / (a + b)] j = Pinf a b i j`:   R33
  6. Cases on `i` and `j`, then evaluate with `simp [Pinf]`:                 R2, then R3, R4, R34
-/
-- BEGIN SPEC
theorem converges (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hab : 0 < a + b) (hab2 : a + b < 2) (i j : Fin 2) :
    Tendsto (fun n : ℕ => (P a b ^ n) i j) atTop (𝓝 (![b / (a + b), a / (a + b)] j)) :=
-- END SPEC
  sorry

end H059

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two matrix identities do all the work: `P * Π = Π` (MILESTONE 1) and `P * (1 - Π) = λ • (1 - Π)` with
    `λ = 1 - a - b` (MILESTONE 2; `λ` is the second eigenvalue of `P`). With them `pow_formula` is an induction
    with no entry computations, and `converges` needs only `|λ| < 1` (MILESTONE 3) and `λⁿ → 0`.
H2. Milestones 1 and 2: entrywise (`ext i j; fin_cases i <;> fin_cases j <;> simp [P, Pinf, …]`), then
    `field_simp` and `ring`; for MILESTONE 2 first `rw [mul_sub, mul_one, P_mul_Pinf a b hab]`. `pow_formula`:
    `induction n`, base case `simp`, step a single `rw` chain. `converges`: `simp_rw` the formula and
    `Matrix.add_apply`, `Matrix.smul_apply`, `smul_eq_mul` into the sequence, so its entry is
    `Π i j + λⁿ * (1 - Π) i j`, then build that limit from `λⁿ → 0`.
H3. Step: `Pⁿ⁺¹ = P * Pⁿ` (`pow_succ'`); substitute the IH, distribute (`mul_add`), move `P` past the scalar
    (`mul_smul_comm`), apply both milestones and merge the scalars (`smul_smul`, `pow_succ`).
    Limit: with `h0 := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (abs_lt_one a b hab hab2)`, the key term is
    `(tendsto_const_nhds (x := Pinf a b i j)).add (h0.mul (tendsto_const_nhds (x := (1 - Pinf a b) i j)))`;
    then `rw [zero_mul, add_zero] at h`, `convert h using 2`, and `fin_cases i <;> fin_cases j <;> simp [Pinf]`.
-/
