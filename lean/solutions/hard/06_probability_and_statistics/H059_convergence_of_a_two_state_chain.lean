/- H059 | Convergence of a 2-state chain | 45-60 min | Markov chain, matrix powers, induction, limits, mathlib
GOAL
  A chain on states `{0, 1}` jumps `0 → 1` with probability `a` and `1 → 0` with probability `b`; its
  transition matrix is `P a b`, and `(Pⁿ) i j` is the probability of being in `j` after `n` steps from `i`.
  Prove `Pⁿ = Π + (1 - a - b)ⁿ • (1 - Π)`, where both rows of `Π = Pinf a b` are the stationary
  distribution `π = (b, a) / (a + b)`, then that `(Pⁿ) i j → π j` from either start `i` when `0 < a + b < 2`.

REFERENCE
  `!![p, q; r, s]`: 2×2 matrix (`;` separates rows);  `M i j`: entry (`i j : Fin 2`);  `c • M`: scalar times matrix
  #check Matrix.mul_apply     -- (M * N) i k = ∑ j, M i j * N j k   (with `Fin.sum_univ_two : ∑ i, f i = f 0 + f 1`)
  -- matrix equality entry by entry: `ext i j; fin_cases i <;> fin_cases j`, then compute each entry
  #check Matrix.add_apply     -- (A + B) i j = A i j + B i j      (and `Matrix.smul_apply`, then `smul_eq_mul`)
  #check pow_succ'            -- a ^ (n + 1) = a * a ^ n
  #check mul_smul_comm        -- x * s • y = s • (x * y)          (and `smul_smul : a • b • x = (a * b) • x`)
  `Tendsto f atTop (𝓝 L)` means `f n → L` as `n → ∞`  (`open Filter Topology`).
  #check tendsto_pow_atTop_nhds_zero_of_abs_lt_one  -- |r| < 1 → Tendsto (fun n => r ^ n) atTop (𝓝 0)
  #check Filter.Tendsto.add   -- f → a → g → b → (fun x => f x + g x) → a + b   (also `.mul`, `tendsto_const_nhds`)
NOTE: only `0 < a + b < 2` is needed; `0 ≤ a, b ≤ 1` just make `P` stochastic (expect unused-variable warnings).
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

-- MILESTONE (optional: change or delete)
theorem P_mul_Pinf (a b : ℝ) (hab : a + b ≠ 0) : P a b * Pinf a b = Pinf a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P, Pinf, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

-- MILESTONE (optional: change or delete)
theorem P_mul_one_sub (a b : ℝ) (hab : a + b ≠ 0) :
    P a b * (1 - Pinf a b) = (1 - a - b) • (1 - Pinf a b) := by
  rw [mul_sub, mul_one, P_mul_Pinf a b hab]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P, Pinf] <;> field_simp <;> ring

-- MILESTONE (optional: change or delete)
theorem abs_lt_one (a b : ℝ) (hab : 0 < a + b) (hab2 : a + b < 2) : |1 - a - b| < 1 := by
  rw [abs_lt]
  constructor <;> linarith

-- BEGIN SPEC
theorem pow_formula (a b : ℝ) (hab : a + b ≠ 0) (n : ℕ) :
    P a b ^ n = Pinf a b + (1 - a - b) ^ n • (1 - Pinf a b) :=
-- END SPEC
  by
    induction n with
    | zero => simp
    | succ n ih =>
      -- P^(n+1) = P * P^n, then push `P *` through the closed form
      rw [pow_succ', ih, mul_add, mul_smul_comm, P_mul_Pinf a b hab, P_mul_one_sub a b hab,
        smul_smul, pow_succ]

-- BEGIN SPEC
theorem converges (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hab : 0 < a + b) (hab2 : a + b < 2) (i j : Fin 2) :
    Tendsto (fun n : ℕ => (P a b ^ n) i j) atTop (𝓝 (![b / (a + b), a / (a + b)] j)) :=
-- END SPEC
  by
    have h0 := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (abs_lt_one a b hab hab2)
    simp_rw [pow_formula a b hab.ne', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have h := (tendsto_const_nhds (x := Pinf a b i j)).add
      (h0.mul (tendsto_const_nhds (x := (1 - Pinf a b) i j)))
    rw [zero_mul, add_zero] at h
    convert h using 2
    fin_cases i <;> fin_cases j <;> simp [Pinf]

end H059

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two matrix identities do all the work: `P * Π = Π` and `P * (1 - Π) = λ • (1 - Π)` with `λ = 1 - a - b`
    (the second eigenvalue of `P`). With them, `pow_formula` is an induction with no entry computations.
H2. Prove the identities entrywise (`ext i j; fin_cases i <;> fin_cases j <;> simp [...]`, then `field_simp`
    and `ring`). For the limit, rewrite with `pow_formula` and unfold `+`, `•` entrywise
    (`Matrix.add_apply`, `Matrix.smul_apply`, `smul_eq_mul`): the entry is `Π i j + λⁿ * (1 - Π) i j`, `|λ| < 1`.
H3. Step: `Pⁿ⁺¹ = P * Pⁿ` (`pow_succ'`); substitute the IH, distribute, move `P` past the scalar
    (`mul_smul_comm`), apply both milestones and merge the scalars (`smul_smul`, `pow_succ`).
    Limit: with `h0 : Tendsto (fun n => λ ^ n) atTop (𝓝 0)`, the key term is
    `tendsto_const_nhds.add (h0.mul tendsto_const_nhds)`, whose limit is `Π i j + 0 * (1 - Π) i j`.
-/
