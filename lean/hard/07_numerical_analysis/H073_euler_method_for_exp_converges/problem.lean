/- H073 | Euler's method for y' = y converges to exp | 1-1.5 h | limits, exp bounds, telescoping powers, squeeze_zero', Filter.Eventually, mathlib
GOAL
  Euler's method for `y' = y`, `y(0) = 1`, run from `0` to `x` in steps of size `h = x/n`, is `eulerExp x n k` (the
  value after `k` steps). First show it returns `(1 + x/n)ᵏ`; after `n` steps the exact answer is `eˣ`. Prove the
  first-order error bound `|eˣ − (1 + x/n)ⁿ| ≤ x² e^{|x|} / n` (for `n ≥ |x|`), then deduce `(1 + x/n)ⁿ → eˣ` from it.
  Idea: `eˣ = (e^{x/n})ⁿ`, and `aⁿ − bⁿ` is controlled by `a − b` and `max |a| |b|`.
  (`Tendsto u atTop (𝓝 L)`: `u n → L` as `n → ∞`; `∀ᶠ n in atTop, P n`: `P n` holds for all large `n`.)

REFERENCE
  #check abs_pow_sub_pow_le          -- (a b : α) (n : ℕ) : |a ^ n - b ^ n| ≤ |a - b| * n * max |a| |b| ^ (n - 1)
  #check Real.abs_exp_sub_one_sub_id_le  -- |x| ≤ 1 → |exp x - 1 - x| ≤ x ^ 2
  #check Real.exp_nat_mul            -- exp (n * x) = exp x ^ n
  #check Real.add_one_le_exp         -- x + 1 ≤ exp x      (`Real.abs_exp : |exp x| = exp x`)
  #check Real.exp_le_exp             -- exp x ≤ exp y ↔ x ≤ y
  #check Nat.cast_sub                -- m ≤ n → ((n - m : ℕ) : R) = n - m     (ℕ subtraction is truncated)
  #check squeeze_zero'               -- (∀ᶠ t in l, 0 ≤ f t) → (∀ᶠ t in l, f t ≤ g t) → Tendsto g l (𝓝 0) → Tendsto f l (𝓝 0)
  #check tendsto_const_div_atTop_nhds_zero_nat  -- (C : 𝕜) : Tendsto (fun n : ℕ => C / n) atTop (𝓝 0)
  #check exists_nat_ge               -- (x : R) : ∃ n : ℕ, x ≤ n
  `filter_upwards [eventually_ge_atTop N] with n hn` proves `∀ᶠ n in atTop, P n` given `hn : N ≤ n`.
  `tendsto_iff_norm_sub_tendsto_zero` turns `u n → L` into `‖u n − L‖ → 0`  (`Real.norm_eq_abs`, `abs_sub_comm`).
BANNED: tendsto_one_add_div_pow_exp, tendsto_one_add_div_rpow_exp, tendsto_one_add_div_cpow_exp, tendsto_mul_log_one_add_div_atTop
BANNED: tendsto_one_add_pow_exp_of_tendsto, tendsto_one_add_rpow_exp_of_tendsto, tendsto_one_add_cpow_exp_of_tendsto
BANNED: tendsto_nat_mul_log_one_add_of_tendsto, tendsto_mul_log_one_add_of_tendsto, tendsto_pow_exp_of_isLittleO_sub_add_div
-/
import Mathlib

open Filter Topology

namespace H073

-- BEGIN SPEC
/-- Euler's method for `y' = y`, `y 0 = 1`, with step `x / n`: the value after `k` steps -/
noncomputable def eulerExp (x : ℝ) (n : ℕ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => eulerExp x n k + x / n * eulerExp x n k
-- END SPEC

-- BEGIN SPEC
theorem eulerExp_eq_pow (x : ℝ) (n k : ℕ) : eulerExp x n k = (1 + x / n) ^ k :=
-- END SPEC
  sorry

-- MILESTONE (optional: change or delete)
-- one exact step `e^{x/n}` versus one Euler step `1 + x/n`
theorem exp_step_close (x : ℝ) (n : ℕ) (hn0 : 0 < n) (hn : |x| ≤ n) :
    |Real.exp (x / n) - (1 + x / n)| ≤ (x / n) ^ 2 := by
  sorry

-- MILESTONE (optional: change or delete)
theorem both_le (x : ℝ) (n : ℕ) (hn0 : 0 < n) :
    |Real.exp (x / n)| ≤ Real.exp (|x| / n) ∧ |1 + x / n| ≤ Real.exp (|x| / n) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem pow_bound (x : ℝ) (n : ℕ) (hn0 : 0 < n) : Real.exp (|x| / n) ^ (n - 1) ≤ Real.exp |x| := by
  sorry

-- BEGIN SPEC
theorem euler_exp_error (x : ℝ) (n : ℕ) (hn0 : 0 < n) (hn : |x| ≤ n) :
    |Real.exp x - (1 + x / n) ^ n| ≤ x ^ 2 * Real.exp |x| / n :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem euler_converges_exp (x : ℝ) :
    Tendsto (fun n : ℕ => (1 + x / n) ^ n) atTop (𝓝 (Real.exp x)) :=
-- END SPEC
  sorry

end H073

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Set `a = e^{x/n}`, `b = 1 + x/n`. Then `aⁿ = eˣ`, `|a − b| ≤ (x/n)²` (needs `|x/n| ≤ 1`, i.e. `n ≥ |x|`), and both
    `|a|, |b| ≤ e^{|x|/n}`, so `max |a| |b| ^ (n−1) ≤ e^{(n−1)|x|/n} ≤ e^{|x|}`. Plug into `abs_pow_sub_pow_le`.
H2. `eulerExp_eq_pow`: induct on `k`; `rw [eulerExp]` unfolds one Euler step, then use the IH and `pow_succ`.
    `exp_step_close`: `simpa [sub_sub] using Real.abs_exp_sub_one_sub_id_le hxn`. `both_le`: `Real.abs_exp` then
    `exp_le_exp`; for `b`, `|1 + x/n| ≤ 1 + |x/n| = |x|/n + 1 ≤ e^{|x|/n}`. `pow_bound`: `← Real.exp_nat_mul`, `exp_le_exp`,
    and `Nat.cast_sub` to show `(n − 1)·(|x|/n) = |x| − |x|/n ≤ |x|`. Limit: squeeze `|(1 + x/n)ⁿ − eˣ|` under `C / n`.
H3. `induction k with | zero => rfl | succ k ih => rw [eulerExp, ih, pow_succ]; ring`.
    `calc |a ^ n - b ^ n| ≤ |a - b| * n * max |a| |b| ^ (n - 1) := abs_pow_sub_pow_le a b n
      _ ≤ (x / n) ^ 2 * n * Real.exp |x| := by gcongr ... _ = x ^ 2 * Real.exp |x| / n := by field_simp`.
    Limit: `refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ (tendsto_const_div_atTop_nhds_zero_nat _)`,
    `obtain ⟨N, hN⟩ := exists_nat_ge |x|`, `filter_upwards [eventually_ge_atTop (max N 1)] with n hn`.
-/
