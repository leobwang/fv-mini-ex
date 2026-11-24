/- M118 | Euler's method on y' = λy | 15-20 min | recursion, closed form, exp bounds, stability, Tendsto atTop, mathlib
GOAL
  Forward Euler `yₙ₊₁ = yₙ + h·(λ yₙ)` on the test equation `y' = λy` gives `yₙ = (1 + hλ)ⁿ y₀`. For λ ≥ 0 it
  underestimates the exact solution `e^(λ·nh) y₀`. For λ ≤ 0 it is stable (`|yₙ| ≤ |y₀|`) if `h|λ| ≤ 2`, and if
  `h|λ| > 2` every nonzero start blows up (`|yₙ| → ∞`), so the step-size restriction is sharp.
BANNED: try?

GUIDE
  Entries R1–R22: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Filter

namespace M118

-- BEGIN SPEC
def euler (lam h y₀ : ℝ) : ℕ → ℝ
  | 0 => y₀
  | n + 1 => euler lam h y₀ n + h * (lam * euler lam h y₀ n)
-- END SPEC

/- SKELETON · euler_closed_form
  1. Induction on `n`:                                                      R1
  2. Base case `euler lam h y₀ 0 = (1 + h * lam) ^ 0 * y₀`:
       unfold the `| 0` equation and clean up `^ 0`, `1 *` (`simp [euler]`)  R2
  3. Step case: unfold one step, replace `euler lam h y₀ n` by `ih`,
     split the power:                                                       R3, rw [ih], R4
  4. What is left is a ring identity:                                       ring
-/
-- BEGIN SPEC
theorem euler_closed_form (lam h y₀ : ℝ) (n : ℕ) : euler lam h y₀ n = (1 + h * lam) ^ n * y₀ :=
-- END SPEC
  sorry

/- SKELETON · euler_le_exact
  1. Rewrite with the closed form (proved above, used like a library lemma): R5
  2. Drop the common factor `y₀` (its side goal `0 ≤ y₀` is `hy`):          R6
  3. Chain the bound through `Real.exp (h * lam) ^ n`:                       R7
       (1 + h * lam) ^ n ≤ Real.exp (h * lam) ^ n                           R8, then R10 with R9
       _ = Real.exp (lam * (n * h))                                         R11 (right to left), R12
-/
-- BEGIN SPEC
theorem euler_le_exact (lam h y₀ : ℝ) (hl : 0 ≤ lam) (hh : 0 ≤ h) (hy : 0 ≤ y₀) (n : ℕ) :
    euler lam h y₀ n ≤ Real.exp (lam * (n * h)) * y₀ :=
-- END SPEC
  sorry

/- SKELETON · euler_stable
  1. Closed form, then split the absolute value:                            R5, R13, R14
  2. Prove the amplification bound first:
       hamp : |1 + h * lam| ≤ 1                                             R15, constructor, R16 on both
  3. Chain `|1 + h * lam| ^ n * |y₀| ≤ 1 ^ n * |y₀| = |y₀|`:                 R7
       first step: one `gcongr` through `* |y₀|` and `^ n`, closed by hamp   R8
       second step:                                                         R17 (`simp`)
-/
-- BEGIN SPEC
theorem euler_stable (lam h y₀ : ℝ) (hl : lam ≤ 0) (hh : 0 ≤ h) (hstab : h * (-lam) ≤ 2) (n : ℕ) :
    |euler lam h y₀ n| ≤ |y₀| :=
-- END SPEC
  sorry

/- SKELETON · euler_unstable
  1. Prove the growth fact first (no sign hypothesis on λ is needed):
       h1 : 1 < |1 + h * lam|                                               R18, side goal by R10; then R10
  2. Closed form and absolute values, under `fun n => …`:                   R19 with R5, R13, R14
  3. The goal is now `Tendsto (fun n => |1 + h * lam| ^ n * |y₀|) atTop atTop`:
       powers of `|1 + h * lam| > 1` → ∞, times the constant `|y₀| > 0`     R20 (from h1), R21, R22 (from hy)
     one `exact` with dot notation, as in guide W3
-/
-- BEGIN SPEC
theorem euler_unstable (lam h y₀ : ℝ) (hstab : 2 < h * (-lam)) (hy : y₀ ≠ 0) :
    Tendsto (fun n => |euler lam h y₀ n|) atTop atTop :=
-- END SPEC
  sorry

end M118

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove `euler_closed_form` first, by induction on `n`, and start every other proof by rewriting with it
    (`rw`, or `simp_rw` under `fun n => …`). Everything is then about the amplification factor `1 + hλ`.
H2. Exact: drop `y₀` with `gcongr`, then `calc` through `Real.exp (h * lam) ^ n` using `x + 1 ≤ eˣ` and
    `(eˣ)ⁿ = e^(n·x)`. Stable: `|yₙ| = |1 + hλ|ⁿ |y₀|`; prove `|1 + hλ| ≤ 1` with `abs_le` (two bounds; the
    upper one needs the product `h·λ ≤ 0`, so `nlinarith`), then `gcongr` against `1 ^ n`. Unstable:
    `2 < h(-λ)` forces `1 + hλ < -1`, so `1 < |1 + hλ|`; `rⁿ → ∞` for `1 < r`, and `· |y₀|` with `|y₀| > 0` keeps it.
H3. Closed form step: `rw [euler, ih, pow_succ]; ring`. Exact: `rw [euler_closed_form]; gcongr`, then
    `calc (1 + h * lam) ^ n ≤ Real.exp (h * lam) ^ n := by gcongr; linarith [Real.add_one_le_exp (h * lam)]`
    and `_ = … := by rw [← Real.exp_nat_mul]; ring_nf`.
    Stable: `have hamp : |1 + h * lam| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith`.
    Unstable: `have h1 : 1 < |1 + h * lam| := by rw [abs_of_neg (by linarith)]; linarith`, then
    `simp_rw [euler_closed_form, abs_mul, abs_pow]` and
    `exact (tendsto_pow_atTop_atTop_of_one_lt h1).atTop_mul_const (abs_pos.mpr hy)`.
-/
