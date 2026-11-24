/- M123 | Backward Euler is A-stable | 15-20 min | implicit methods, field_simp, geometric sequences, Tendsto, mathlib
GOAL
  Backward (implicit) Euler for y' = λy defines yₙ₊₁ by `yₙ₊₁ = yₙ + hλyₙ₊₁`, solved as `yₙ₊₁ = yₙ / (1 - hλ)`.
  Show it solves the implicit equation, never grows when λ ≤ 0 for *every* step h ≥ 0 (A-stability: no
  step-size limit, unlike explicit Euler's `h|λ| ≤ 2`), and decays to 0 when λ < 0.
BANNED: grind, try?

GUIDE
  Entries R1–R23: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib
open Filter Topology

namespace M123

-- BEGIN SPEC
/-- backward Euler for y' = λy, with the implicit equation already solved for yₙ₊₁ -/
noncomputable def beuler (lam h y₀ : ℝ) : ℕ → ℝ
  | 0 => y₀
  | n + 1 => beuler lam h y₀ n / (1 - h * lam)
-- END SPEC

/- SKELETON · beuler_implicit
  1. Unfold `beuler … (n + 1)` on both sides:                                R1
  2. Clear the denominator `1 - h * lam` (`hne` is in the context):         R2
  3. Finish the polynomial identity:                                        ring
-/
-- BEGIN SPEC
theorem beuler_implicit (lam h y₀ : ℝ) (hne : 1 - h * lam ≠ 0) (n : ℕ) :
    beuler lam h y₀ (n + 1) = beuler lam h y₀ n + h * (lam * beuler lam h y₀ (n + 1)) :=
-- END SPEC
  by
    simp only [beuler]
    field_simp
    ring

/-- the iterates form a geometric sequence with ratio `(1 - hλ)⁻¹` -/
theorem beuler_closed (lam h y₀ : ℝ) (n : ℕ) : beuler lam h y₀ n = (1 - h * lam)⁻¹ ^ n * y₀ := by
  induction n with
  | zero => simp [beuler]
  | succ n ih => rw [beuler, ih, pow_succ]; field_simp

/- SKELETON · beuler_stable
  0. MILESTONE, prove it first (a helper theorem between `beuler_implicit` and this one, outside the
     spec regions); it is used here in step 1 and in `beuler_tendsto_zero` step 4:
       beuler_closed (lam h y₀ : ℝ) (n : ℕ) : beuler lam h y₀ n = (1 - h * lam)⁻¹ ^ n * y₀
     proof: induction on n                                                  R3
       zero: unfold and simplify                                            simp [beuler] (R1)
       succ: unfold, rw [ih], split the power, clear the denominator        R1, rw [ih], R4, R2
             (here R2 closes the goal by itself: no `ring` after it)
  1. Rewrite with the closed form, then split |rⁿ · y₀|:                    rw [beuler_closed], R7, R8
  2. h1 : 1 ≤ 1 - h * lam                                                   R5
  3. hr : |(1 - h * lam)⁻¹| ≤ 1                                             R9 → R10 (side goal: R6) → R11
  4. The bound |r| ^ n * |y₀| ≤ 1 * |y₀| = |y₀|:                            R12
       first step: drop |y₀|, then bound the power                          R13 → R14 with R15, hr
       second step:                                                         R16
-/
-- BEGIN SPEC
theorem beuler_stable (lam h y₀ : ℝ) (hl : lam ≤ 0) (hh : 0 ≤ h) (n : ℕ) :
    |beuler lam h y₀ n| ≤ |y₀| :=
-- END SPEC
  by
    rw [beuler_closed, abs_mul, abs_pow]
    have h1 : 1 ≤ 1 - h * lam := by nlinarith
    have hr : |(1 - h * lam)⁻¹| ≤ 1 := by
      rw [abs_inv, abs_of_pos (by linarith)]
      exact inv_le_one_of_one_le₀ h1
    calc |(1 - h * lam)⁻¹| ^ n * |y₀| ≤ 1 * |y₀| := by
          gcongr
          exact pow_le_one₀ (abs_nonneg _) hr
      _ = |y₀| := one_mul _

/- SKELETON · beuler_tendsto_zero
  1. h1 : 1 < 1 - h * lam                                                   R5
  2. hr0 : 0 ≤ (1 - h * lam)⁻¹,  hr1 : (1 - h * lam)⁻¹ < 1                  R17, R18
  3. hlim : rⁿ · y₀ → 0 · y₀, then make the limit 0:                        R19 → R20, R21
  4. Transfer the limit to `beuler` with the milestone `beuler_closed`:     R22 with R23
-/
-- BEGIN SPEC
theorem beuler_tendsto_zero (lam h y₀ : ℝ) (hl : lam < 0) (hh : 0 < h) :
    Tendsto (beuler lam h y₀) atTop (𝓝 0) :=
-- END SPEC
  by
    have h1 : 1 < 1 - h * lam := by nlinarith
    have hr0 : 0 ≤ (1 - h * lam)⁻¹ := by positivity
    have hr1 : (1 - h * lam)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
    have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const y₀
    rw [zero_mul] at hlim
    exact hlim.congr fun n => (beuler_closed lam h y₀ n).symm

end M123

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Parts 2 and 3 need a closed form: the iterates are a geometric sequence with ratio `r = (1 - hλ)⁻¹`.
    For λ ≤ 0, h ≥ 0 we have `1 ≤ 1 - hλ`, so `0 < r ≤ 1`; for λ < 0, h > 0, `1 < 1 - hλ`, so `r < 1`.
H2. Implicit: unfold, `field_simp`, `ring`. Helper `beuler lam h y₀ n = (1 - h * lam)⁻¹ ^ n * y₀` by
    `induction n with`. Stable: rewrite with the helper, split the absolute values, bound `|r| ≤ 1` and
    finish with `calc` and `gcongr`. Limit: `rⁿ → 0` times the constant `y₀`, then `Tendsto.congr`.
H3. Implicit: `simp only [beuler]; field_simp; ring`. Helper, succ case: `rw [beuler, ih, pow_succ]; field_simp`.
    Stable: `rw [beuler_closed, abs_mul, abs_pow]`, `have h1 : 1 ≤ 1 - h * lam := by nlinarith`,
    `rw [abs_inv, abs_of_pos (by linarith)]; exact inv_le_one_of_one_le₀ h1`, and `pow_le_one₀ (abs_nonneg _) hr`.
    Limit: `have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const y₀`, `rw [zero_mul] at hlim`,
    `exact hlim.congr fun n => (beuler_closed lam h y₀ n).symm`.
-/
