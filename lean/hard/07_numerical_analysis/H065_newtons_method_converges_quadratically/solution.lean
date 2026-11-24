/- H065 | Newton's method converges quadratically | 45-75 min | Taylor, iteration, quadratic convergence, mathlib
GOAL
  Newton's step is `newton f x = x - f x / f'(x)`. If `|f'| ≥ m > 0` and `|f''| ≤ M`, one step from `x` toward
  a root `r` gives `|newton f x - r| ≤ C|x - r|²` with `C = M/(2m)`; iterating, `C|xₙ - r| ≤ (Cδ)^(2ⁿ)` (digits double),
  where `xₙ = (newton f)^[n] x₀` is the n-th iterate and `δ` bounds the initial error, `|x₀ - r| ≤ δ`.

GUIDE
  Entries R1–R37: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Set

namespace H065

-- BEGIN SPEC
noncomputable def newton (f : ℝ → ℝ) (x : ℝ) : ℝ := x - f x / deriv f x
-- END SPEC

/- SKELETON · taylor1   (milestone; prove it first: used in `newton_error_eq`)
  1. Split `x = y` / `x ≠ y`:                                                  R1
       `x = y`: witness `x`; every `(x - x)` term vanishes                      R2
  2. `x ≠ y`: Taylor of order 1 with Lagrange remainder on `uIcc x y`:          R3 → R4
     then choose its `ξ` as the witness                                        refine ⟨ξ, ?_⟩
  3. Prove `hu : UniqueDiffOn ℝ (uIcc x y)`: split `x < y` / `y < x`,
       each case: `uIcc` → `Icc`, then the `Icc` fact                          R5, R6 / R7, R8
  4. Prove `d1 : iteratedDerivWithin 1 f (uIcc x y) x = deriv f x`:
       rewrite with R11 (arguments: `hu`, R9, R10), then R12                   R11, R9, R10, R12
  5. Expand the Taylor polynomial in `hξ`, insert `d1`, THEN tidy numerals:     R13 → R14 → rw [d1] at hξ → R15
  6. Goal and `hξ` now agree up to ring arithmetic:                            R16
-/
-- MILESTONE (optional: change or delete)
-- First-order Taylor with Lagrange remainder, for `y` on either side of `x` (M111's step, generalised).
theorem taylor1 (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x y : ℝ) :
    ∃ ξ, f y = f x + deriv f x * (y - x) + iteratedDeriv 2 f ξ / 2 * (y - x) ^ 2 := by
  rcases eq_or_ne x y with rfl | hxy
  · exact ⟨x, by simp⟩
  obtain ⟨ξ, -, hξ⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hxy hf.contDiffOn
  refine ⟨ξ, ?_⟩
  have hu : UniqueDiffOn ℝ (uIcc x y) := by
    rcases hxy.lt_or_gt with h | h
    · rw [uIcc_of_le h.le]; exact uniqueDiffOn_Icc h
    · rw [uIcc_of_ge h.le]; exact uniqueDiffOn_Icc h
  -- WHY: Taylor's coefficients are derivatives *within* `uIcc x y`; convert them to `deriv`.
  have d1 : iteratedDerivWithin 1 f (uIcc x y) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.contDiffAt.of_le (by norm_num)) left_mem_uIcc,
      iteratedDeriv_one]
  rw [taylorWithinEval_succ, taylor_within_zero_eval, d1] at hξ
  norm_num at hξ
  linear_combination hξ

/- SKELETON · newton_error_eq   (milestone; uses `taylor1`; used in `newton_quadratic`)
  1. `taylor1` at `x`, evaluated at `y := r`: obtain `ξ` and the identity `hξ : f r = …`
  2. `h0 : f x + deriv f x * (r - x) + iteratedDeriv 2 f ξ / 2 * (r - x) ^ 2 = 0`
       from `hξ` and `hroot`:                                                  R17
  3. Witness `ξ`, then unfold the Newton step:                                 refine ⟨ξ, ?_⟩, R18
  4. Clear the denominators `deriv f x` and `2` (uses `hd0`):                   R19
  5. Close with a multiple of `h0`; compare the `f x` terms of goal and `h0`:  R16
-/
-- MILESTONE (optional: change or delete)
-- The exact Newton error: expand `f` at `x`, evaluate at the root `r`, divide by `f'(x)`.
theorem newton_error_eq (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (r x : ℝ) (hroot : f r = 0)
    (hd0 : deriv f x ≠ 0) :
    ∃ ξ, newton f x - r = iteratedDeriv 2 f ξ / 2 * (r - x) ^ 2 / deriv f x := by
  obtain ⟨ξ, hξ⟩ := taylor1 f hf x r
  have h0 : f x + deriv f x * (r - x) + iteratedDeriv 2 f ξ / 2 * (r - x) ^ 2 = 0 :=
    hξ.symm.trans hroot
  refine ⟨ξ, ?_⟩
  unfold newton
  field_simp
  linear_combination -2 * h0

/- SKELETON · bound_nonneg   (milestone; used in `newton_quadratic`, `scaled_step`, `newton_converges`)
  1. `0 ≤ |g 0|` (any point works):                                            R20
  2. chain it with `hM 0 : |g 0| ≤ M`:                                         R21
-/
-- MILESTONE (optional: change or delete)
theorem bound_nonneg (g : ℝ → ℝ) (M : ℝ) (hM : ∀ t, |g t| ≤ M) : 0 ≤ M :=
  (abs_nonneg _).trans (hM 0)

/- SKELETON · newton_quadratic   (milestones first: `taylor1` → `newton_error_eq`, `bound_nonneg`)
  1. `hdpos : 0 < |deriv f x|` from `hm` and `hd`:                              R21
  2. The exact error: `newton_error_eq`, its `deriv f x ≠ 0` from `hdpos`:      R22
       obtain `ξ` and `e : newton f x - r = …`
  3. `hM0 : 0 ≤ M` from the milestone `bound_nonneg`
  4. Rewrite the goal: `rw [e]`, split the absolute value
       (`abs_div` twice: the outer `/ deriv f x` and the `/ 2`),
       flip `|r - x|` to `|x - r|`, clear `/ |deriv f x|` with `hdpos`:         R23, R24, R23, R25, R26, R27, R28
  5. A three-step chain:                                                       R29
       |f''(ξ)| / 2 · |x - r|²  ≤  M / 2 · |x - r|²         R30, then `hM ξ`
                                =  M / (2m) · |x - r|² · m   R19
                                ≤  M / (2m) · |x - r|² · |deriv f x|   R30 (uses `hM0`, `hd`)
-/
-- BEGIN SPEC
theorem newton_quadratic (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (r x m M : ℝ) (hm : 0 < m)
    (hroot : f r = 0) (hd : m ≤ |deriv f x|) (hM : ∀ t, |iteratedDeriv 2 f t| ≤ M) :
    |newton f x - r| ≤ M / (2 * m) * |x - r| ^ 2 :=
-- END SPEC
  by
    have hdpos : 0 < |deriv f x| := hm.trans_le hd
    obtain ⟨ξ, e⟩ := newton_error_eq f hf r x hroot (abs_pos.mp hdpos)
    have hM0 : 0 ≤ M := bound_nonneg _ M hM
    rw [e, abs_div, abs_mul, abs_div, abs_two, abs_pow, abs_sub_comm r x, div_le_iff₀ hdpos]
    calc |iteratedDeriv 2 f ξ| / 2 * |x - r| ^ 2 ≤ M / 2 * |x - r| ^ 2 := by gcongr; exact hM ξ
      _ = M / (2 * m) * |x - r| ^ 2 * m := by field_simp
      _ ≤ M / (2 * m) * |x - r| ^ 2 * |deriv f x| := by gcongr

/- SKELETON · scaled_step   (milestone; uses `bound_nonneg`, `newton_quadratic`; used in `newton_converges`)
  Write `C = M / (2 * m)`.
  1. `hC : 0 ≤ C`: get `0 ≤ M` from `bound_nonneg`, then                       R31
  2. A two-step chain:                                                         R29
       C · |newton f x - r|  ≤  C · (C · |x - r|²)     R30, then `newton_quadratic`
                             =  (C · |x - r|)²         ring
-/
-- MILESTONE (optional: change or delete)
-- Multiply the one-step bound by `C = M/(2m)`: the scaled error squares at each step.
theorem scaled_step (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (r x m M : ℝ) (hm : 0 < m)
    (hroot : f r = 0) (hd : m ≤ |deriv f x|) (hM : ∀ t, |iteratedDeriv 2 f t| ≤ M) :
    M / (2 * m) * |newton f x - r| ≤ (M / (2 * m) * |x - r|) ^ 2 := by
  have hC : 0 ≤ M / (2 * m) := by have := bound_nonneg _ M hM; positivity
  calc M / (2 * m) * |newton f x - r| ≤ M / (2 * m) * (M / (2 * m) * |x - r| ^ 2) := by
        gcongr; exact newton_quadratic f hf r x m M hm hroot hd hM
    _ = (M / (2 * m) * |x - r|) ^ 2 := by ring

/- SKELETON · newton_converges   (milestones first: `bound_nonneg` for `hC`, `scaled_step` in step 4)
  Write `C = M / (2 * m)` and `xₙ = (newton f)^[n] x₀`.
  1. `hC : 0 ≤ C`, as in `scaled_step`:                                         R31
  2. Induction on `n`, naming the hypothesis `ih`:                             R32
  3. `zero`: multiply `hx₀` by `C` (R33), then simplify `g^[0]` and `^ 2 ^ 0`:  R33, R34
  4. `succ`: peel the last Newton step, split the exponent `2 ^ (n + 1)`:       R35, R36, R37
       then a two-step chain:                                                  R29
       C · |newton f xₙ - r|  ≤  (C · |xₙ - r|)²       `scaled_step` at `xₙ` (with `hd _`)
                              ≤  ((Cδ) ^ 2 ^ n) ^ 2    R30 with `ih`
-/
-- BEGIN SPEC
theorem newton_converges (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (r m M δ x₀ : ℝ) (hm : 0 < m)
    (hroot : f r = 0) (hd : ∀ t, m ≤ |deriv f t|) (hM : ∀ t, |iteratedDeriv 2 f t| ≤ M)
    (hx₀ : |x₀ - r| ≤ δ) (n : ℕ) :
    M / (2 * m) * |(newton f)^[n] x₀ - r| ≤ (M / (2 * m) * δ) ^ (2 ^ n) :=
-- END SPEC
  by
    have hC : 0 ≤ M / (2 * m) := by have := bound_nonneg _ M hM; positivity
    induction n with
    | zero => simpa using mul_le_mul_of_nonneg_left hx₀ hC
    | succ n ih =>
      rw [Function.iterate_succ_apply', pow_succ, pow_mul]
      calc M / (2 * m) * |newton f ((newton f)^[n] x₀) - r|
          ≤ (M / (2 * m) * |(newton f)^[n] x₀ - r|) ^ 2 :=
            scaled_step f hf r _ m M hm hroot (hd _) hM
        _ ≤ ((M / (2 * m) * δ) ^ 2 ^ n) ^ 2 := by gcongr

end H065

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Expand `f` around the iterate `x` and evaluate at the root: `0 = f r = f x + f'(x)(r - x) + f''(ξ)/2·(r - x)²`.
    Dividing by `f'(x)` shows `newton f x - r = f''(ξ)/2·(r - x)²/f'(x)`; then `|f''(ξ)| ≤ M` and `|f'(x)| ≥ m`.
    The milestones are exactly these steps; prove them in file order.
H2. `taylor1`: case `x = y` (witness `x`, `simp`) versus `x ≠ y` (R4 with `n := 1`; R13, R14; turn
    `iteratedDerivWithin 1 f (uIcc x y) x` into `deriv f x` with R11, R12, which needs `UniqueDiffOn` on
    `uIcc x y`: split `x < y` / `y < x`; only then `norm_num at hξ`). Main bound: substitute the exact error,
    split `|·|` (R23–R27), clear the denominator (R28), finish with a `calc` of `gcongr` steps.
    Convergence: induction on `n`, with `C eₙ₊₁ ≤ (C eₙ)² ≤ ((Cδ)^(2ⁿ))² = (Cδ)^(2ⁿ⁺¹)`.
H3. `newton_error_eq`: from `h0 : f x + deriv f x * (r - x) + iteratedDeriv 2 f ξ / 2 * (r - x) ^ 2 = 0`,
    `unfold newton; field_simp; linear_combination -2 * h0`. Main bound: `rw [e, abs_div, abs_mul, abs_div, abs_two,
    abs_pow, abs_sub_comm r x, div_le_iff₀ hdpos]`, then `M/2·e² = (M/(2m))·e²·m ≤ (M/(2m))·e²·|f'(x)|`.
    Induction step: `rw [Function.iterate_succ_apply', pow_succ, pow_mul]` and chain `scaled_step` with the IH.
-/
