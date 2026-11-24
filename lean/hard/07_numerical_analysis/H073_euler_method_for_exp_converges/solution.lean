/- H073 | Euler's method for y' = y converges to exp | 1-1.5 h | limits, exp bounds, telescoping powers, squeeze_zero', Filter.Eventually, mathlib
GOAL
  Euler's method for `y' = y`, `y(0) = 1`, with `n` steps of size `x/n` is `eulerExp x n k` (value after `k` steps).
  Show it equals `(1 + x/n)ᵏ`, prove the first-order error bound `|eˣ − (1 + x/n)ⁿ| ≤ x² e^{|x|} / n` for
  `n ≥ |x|`, and deduce `(1 + x/n)ⁿ → eˣ` from it.
BANNED: tendsto_one_add_div_pow_exp, tendsto_one_add_div_rpow_exp, tendsto_one_add_div_cpow_exp, tendsto_mul_log_one_add_div_atTop
BANNED: tendsto_one_add_pow_exp_of_tendsto, tendsto_one_add_rpow_exp_of_tendsto, tendsto_one_add_cpow_exp_of_tendsto
BANNED: tendsto_nat_mul_log_one_add_of_tendsto, tendsto_mul_log_one_add_of_tendsto, tendsto_pow_exp_of_isLittleO_sub_add_div

GUIDE
  Entries R1–R43: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · eulerExp_eq_pow
  1. Induct on `k`                                                          R1
  2. zero: both sides compute to `1`                                        rfl
  3. succ: unfold one Euler step, use the IH, split off one factor          R2, rw [ih], R3
     what is left is a ring identity                                        ring
-/
-- BEGIN SPEC
theorem eulerExp_eq_pow (x : ℝ) (n k : ℕ) : eulerExp x n k = (1 + x / n) ^ k :=
-- END SPEC
  by
    induction k with
    | zero => rfl
    | succ k ih => rw [eulerExp, ih, pow_succ]; ring

/- SKELETON · exp_step_close   (MILESTONE 1: the factor `|a - b|` in `euler_exp_error`)
  1. `hnpos : (0 : ℝ) < n`                                                  R4
  2. `hxn : |x / n| ≤ 1`: rewrite it to `|x| ≤ n`, which is `hn`            R5 → R6 → R7
  3. The Taylor bound at `x / n`, matched to the goal's `- (1 + x / n)`     R8 inside R10 (with R9)
-/
-- MILESTONE (optional: change or delete)
-- one exact step `e^{x/n}` versus one Euler step `1 + x/n`
theorem exp_step_close (x : ℝ) (n : ℕ) (hn0 : 0 < n) (hn : |x| ≤ n) :
    |Real.exp (x / n) - (1 + x / n)| ≤ (x / n) ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hxn : |x / n| ≤ 1 := by
    rw [abs_div, abs_of_pos hnpos, div_le_one hnpos]
    exact hn
  simpa [sub_sub] using Real.abs_exp_sub_one_sub_id_le hxn

/- SKELETON · both_le   (MILESTONE 2: bounds `max |a| |b|` in `euler_exp_error`)
  1. `hnpos`                                                                R4
  2. Split the `∧`                                                          constructor
  3. First half: drop `|·|`, compare exponents, cancel `/ n`                R11 → R12 → R13, then R14
  4. Second half, a `calc` chain                                            R15
       `|1 + x / n| ≤ 1 + |x / n|`        triangle inequality              R16 inside R10
       `_ = |x| / n + 1`                                                    R5, R6, ring
       `_ ≤ Real.exp (|x| / n)`                                             R17
-/
-- MILESTONE (optional: change or delete)
theorem both_le (x : ℝ) (n : ℕ) (hn0 : 0 < n) :
    |Real.exp (x / n)| ≤ Real.exp (|x| / n) ∧ |1 + x / n| ≤ Real.exp (|x| / n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  constructor
  · rw [Real.abs_exp, Real.exp_le_exp, div_le_div_iff_of_pos_right hnpos]
    exact le_abs_self x
  · calc |1 + x / n| ≤ 1 + |x / n| := by simpa using abs_add_le 1 (x / n)
      _ = |x| / n + 1 := by rw [abs_div, abs_of_pos hnpos]; ring
      _ ≤ Real.exp (|x| / n) := Real.add_one_le_exp _

/- SKELETON · pow_bound   (MILESTONE 3: the power `^ (n - 1)` in `euler_exp_error`)
  1. `hnpos`                                                                R4
  2. Power into the exponent, then compare exponents                        R18 → R12
  3. `↑(n - 1)` → `↑n - 1` (side goal `1 ≤ n`)                              R19 (R21) → R20
  4. Facts `h1 : (↑n - 1) * (|x| / n) = |x| - |x| / n`                      R22
           `h2 : 0 ≤ |x| / n`                                               R23
  5. Finish                                                                 R24
-/
-- MILESTONE (optional: change or delete)
theorem pow_bound (x : ℝ) (n : ℕ) (hn0 : 0 < n) : Real.exp (|x| / n) ^ (n - 1) ≤ Real.exp |x| := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [← Real.exp_nat_mul, Real.exp_le_exp]
  -- WHY: `n - 1` is truncated ℕ subtraction; `Nat.cast_sub` needs `1 ≤ n`
  rw [Nat.cast_sub (by omega), Nat.cast_one]
  have h1 : ((n : ℝ) - 1) * (|x| / n) = |x| - |x| / n := by field_simp
  have h2 : 0 ≤ |x| / n := by positivity
  linarith

/- SKELETON · euler_exp_error
  Prove the three MILESTONES first: steps 4, 5 and 6 use them.
  1. `hnpos`                                                                R4
  2. Name the two one-step factors `a := Real.exp (x / n)`, `b := 1 + x / n`  R25
  3. `hpow : a ^ n = Real.exp x`                                            R18 → R26 → R22
  4. `ha`, `hb` from `both_le`                                              R27
  5. `hmax : max |a| |b| ^ (n - 1) ≤ Real.exp |x|`:
       `max |a| |b| ^ (n - 1) ≤ Real.exp (|x| / n) ^ (n - 1)`               R28 (its hypotheses: R29 with `abs_nonneg`, R30)
       then chain with `pow_bound`                                          R31
  6. rw [← hpow], then a `calc` chain                                       R15
       `|a ^ n - b ^ n| ≤ |a - b| * n * max |a| |b| ^ (n - 1)`              R32
       `_ ≤ (x / n) ^ 2 * n * Real.exp |x|`                                 R33, then `exp_step_close`
       `_ = x ^ 2 * Real.exp |x| / n`                                       R22
-/
-- BEGIN SPEC
theorem euler_exp_error (x : ℝ) (n : ℕ) (hn0 : 0 < n) (hn : |x| ≤ n) :
    |Real.exp x - (1 + x / n) ^ n| ≤ x ^ 2 * Real.exp |x| / n :=
-- END SPEC
  by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    set a := Real.exp (x / n)
    set b := 1 + x / n
    have hpow : a ^ n = Real.exp x := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    obtain ⟨ha, hb⟩ := both_le x n hn0
    have hmax : max |a| |b| ^ (n - 1) ≤ Real.exp |x| :=
      (pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) (max_le ha hb) _).trans (pow_bound x n hn0)
    rw [← hpow]
    calc |a ^ n - b ^ n| ≤ |a - b| * n * max |a| |b| ^ (n - 1) := abs_pow_sub_pow_le a b n
      _ ≤ (x / n) ^ 2 * n * Real.exp |x| := by gcongr; exact exp_step_close x n hn0 hn
      _ = x ^ 2 * Real.exp |x| / n := by field_simp

/- SKELETON · euler_converges_exp
  Uses `euler_exp_error` (step 6).
  1. `u → L` as `‖u n - L‖ → 0`                                             R34
  2. Squeeze under `C / n` with `C = x ^ 2 * Real.exp |x|`; give the lower
     bound and the limit of `C / n` as arguments, keep the middle as `?_`   R35 (R36 + R37, R38)
  3. An index `N` with `|x| ≤ N`                                            R39
  4. Fix `n ≥ max N 1`                                                      R40
  5. `‖·‖` → `|·|`, then swap the difference                                 R41, R42
  6. `exact euler_exp_error …`: `0 < n` by R21; `|x| ≤ n` from `hN` and
     `N ≤ n`                                                                R43 → R4 → R31
-/
-- BEGIN SPEC
theorem euler_converges_exp (x : ℝ) :
    Tendsto (fun n : ℕ => (1 + x / n) ^ n) atTop (𝓝 (Real.exp x)) :=
-- END SPEC
  by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
      (tendsto_const_div_atTop_nhds_zero_nat (x ^ 2 * Real.exp |x|))
    obtain ⟨N, hN⟩ := exists_nat_ge |x|
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact euler_exp_error x n (by omega) (hN.trans (by exact_mod_cast le_of_max_le_left hn))

end H073

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Set `a = e^{x/n}` (one exact step) and `b = 1 + x/n` (one Euler step). Then `aⁿ = eˣ`, and
    `abs_pow_sub_pow_le` (R32) bounds `|aⁿ − bⁿ|` by `|a − b| · n · max |a| |b| ^ (n−1)`. The three
    milestones bound the three factors: `(x/n)²` (needs `|x/n| ≤ 1`, i.e. `n ≥ |x|`), `e^{|x|/n}`, `e^{|x|}`.
H2. `eulerExp_eq_pow`: induct on `k` and unfold one Euler step with `rw [eulerExp]`. `exp_step_close`: the Taylor
    bound R8 at `x / n`, with `sub_sub` to match the goal. `both_le`: `Real.abs_exp`, `Real.exp_le_exp`; for
    `b`, the chain `|1 + x/n| ≤ 1 + |x/n| = |x|/n + 1 ≤ e^{|x|/n}`. `pow_bound`: pull the power into the
    exponent, then `(n − 1)·(|x|/n) = |x| − |x|/n ≤ |x|` (watch the ℕ subtraction). The error bound: a `calc`
    from R32 with `gcongr`. The limit: squeeze `|(1 + x/n)ⁿ − eˣ|` under `C / n` for `n ≥ max N 1`.
H3. `induction k with | zero => rfl | succ k ih => rw [eulerExp, ih, pow_succ]; ring`.
    `simpa [sub_sub] using Real.abs_exp_sub_one_sub_id_le hxn`.  `rw [Nat.cast_sub (by omega), Nat.cast_one]`.
    `calc |a ^ n - b ^ n| ≤ |a - b| * n * max |a| |b| ^ (n - 1) := abs_pow_sub_pow_le a b n
      _ ≤ (x / n) ^ 2 * n * Real.exp |x| := by gcongr; exact exp_step_close x n hn0 hn
      _ = x ^ 2 * Real.exp |x| / n := by field_simp`   (with `hmax` already in the context).
    Limit: `refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ (tendsto_const_div_atTop_nhds_zero_nat _)`,
    `obtain ⟨N, hN⟩ := exists_nat_ge |x|`, `filter_upwards [eventually_ge_atTop (max N 1)] with n hn`.
-/
