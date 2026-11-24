/- M125 | Gauss and Chebyshev nodes | 15-20 min | intervalIntegral, method of moments, linear_combination, Chebyshev polynomials, trig, mathlib
GOAL
  (1) A two-point rule `w₁ f(x₁) + w₂ f(x₂)` exact for `1, x, x², x³` on `[-1, 1]` is Gauss–Legendre:
  `x₁ + x₂ = 0`, `x₁ x₂ = -1/3` (nodes `±1/√3`), `w₁ = w₂ = 1`; (2) it is not exact for `x⁴`; (3) the
  Chebyshev nodes `cos((2k+1)π/(2n))`, `k < n`, are roots of `Tₙ` (`Tₙ(cos θ) = cos(nθ)`).

GUIDE
  Entries R1–R19: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M125

/- SKELETON · gauss_nodes_forced
  Write s = x₁ + x₂, p = x₁ * x₂.
  1. The four moment equations h0–h3 (k = 0, 1, 2, 3):                      R1 (four times)
  2. Evaluate their integrals; the right sides become 2, 0, 2 / 3, 0:      R3 (it uses R2)
  3. hs : x₁ + x₂ = 0        is a multiple of  h3 - s·h2 + p·h1:            R4
     hp : x₁ * x₂ = -1 / 3   is a multiple of  h2 - s·h1 + p·h0:            R4
  4. hx : x₁ ≠ 0: assume x₁ = 0, then hp reads 0 = -1 / 3:                  R5, R6
  5. hw : w₁ = w₂: first (w₁ - w₂) * x₁ = 0 from h1 and hs,                 R4
     then cancel x₁ using hx:                                               R7 → R8 → R9
  6. Split the goal, filling the first two parts with hs, hp:               refine ⟨hs, hp, ?_, ?_⟩
     the weights follow from h0 and hw:                                     R10
-/
-- BEGIN SPEC
theorem gauss_nodes_forced (w₁ w₂ x₁ x₂ : ℝ)
    (hexact : ∀ k ≤ 3, w₁ * x₁ ^ k + w₂ * x₂ ^ k = ∫ x in (-1:ℝ)..1, x ^ k) :
    x₁ + x₂ = 0 ∧ x₁ * x₂ = -1 / 3 ∧ w₁ = 1 ∧ w₂ = 1 :=
-- END SPEC
  by
    have h0 := hexact 0 (by norm_num)
    have h1 := hexact 1 (by norm_num)
    have h2 := hexact 2 (by norm_num)
    have h3 := hexact 3 (by norm_num)
    -- the moments: h0 : w₁ + w₂ = 2, h1 : … = 0, h2 : … = 2 / 3, h3 : … = 0
    norm_num [integral_pow] at h0 h1 h2 h3
    -- WHY: x² - (x₁ + x₂) x + x₁ x₂ is 0 at both nodes, so weighting it by wᵢ (and by wᵢ xᵢ) gives 0
    have hs : x₁ + x₂ = 0 := by
      linear_combination (3 / 2 : ℝ) * (h3 - (x₁ + x₂) * h2 + (x₁ * x₂) * h1)
    have hp : x₁ * x₂ = -1 / 3 := by
      linear_combination (-1 / 2 : ℝ) * (h2 - (x₁ + x₂) * h1 + (x₁ * x₂) * h0)
    have hx : x₁ ≠ 0 := by
      rintro rfl
      norm_num at hp
    have hw : w₁ = w₂ := by
      have : (w₁ - w₂) * x₁ = 0 := by linear_combination h1 - w₂ * hs
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hx)
    refine ⟨hs, hp, ?_, ?_⟩ <;> linarith

/- SKELETON · gauss_not_exact_quartic
  1. hs : √3 ^ 2 = 3:                                                       R11
  2. Evaluate the integral:                                                 R2
  3. Rewrite each node power into the form 1 / (√3 ^ 2) ^ 2 (one `show`
     per power, as in R12), then substitute hs:                             R12 (twice), rw [hs]
  4. Both sides are numerals now (2 / 5 vs 2 / 9):                          norm_num
-/
-- BEGIN SPEC
theorem gauss_not_exact_quartic :
    ∫ x in (-1:ℝ)..1, x ^ 4 ≠ (-1 / √3) ^ 4 + (1 / √3) ^ 4 :=
-- END SPEC
  by
    have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    rw [integral_pow, show (-1 / √3) ^ 4 = 1 / (√3 ^ 2) ^ 2 by ring,
      show (1 / √3) ^ 4 = 1 / (√3 ^ 2) ^ 2 by ring, hs]
    norm_num

/- SKELETON · chebyshev_node_root
  1. T at cos θ → cos (n * θ):                                              R13
  2. cos (…) = 0 → ∃ j : ℤ, … = (2 * j + 1) * π / 2:                         R14
  3. hn : (n : ℝ) ≠ 0: first 0 < n from hk, then the real cast:             R17, R18
  4. Give the witness k:                                                    R15
  5. Merge the casts ↑↑n, ↑↑k into ↑n, ↑k, then cancel n using hn:          R16, R19
-/
-- BEGIN SPEC
theorem chebyshev_node_root (n k : ℕ) (hk : k < n) :
    (Polynomial.Chebyshev.T ℝ n).eval (Real.cos ((2 * k + 1) * Real.pi / (2 * n))) = 0 :=
-- END SPEC
  by
    rw [Polynomial.Chebyshev.T_real_cos, Real.cos_eq_zero_iff]
    have hn : (n : ℝ) ≠ 0 := by
      have : 0 < n := by omega
      positivity
    refine ⟨k, ?_⟩
    push_cast
    field_simp

end M125

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. (1) Specialize `hexact` at `k = 0, 1, 2, 3` and evaluate the integrals: the moments are `2, 0, 2/3, 0`.
    With `s = x₁ + x₂`, `p = x₁ x₂`, the polynomial `q(x) = x² - s x + p` vanishes at both nodes.
    (2) `norm_num` cannot simplify `(1 / √3) ^ 4` by itself; make `√3 ^ 2` appear first.
    (3) `Tₙ(cos θ) = cos (n θ)`, and `cos` vanishes exactly at the odd multiples of `π / 2`.
H2. (1) `Σ wᵢ q(xᵢ) = 0` is `h2 - s·h1 + p·h0`, i.e. `2/3 + 2p = 0`; `Σ wᵢ xᵢ q(xᵢ) = 0` is
    `h3 - s·h2 + p·h1`, i.e. `-(2/3) s = 0`: one `linear_combination` each (R4). Then `x₁ ≠ 0` (R5, R6), and
    `(w₁ - w₂) x₁ = 0` gives `w₁ = w₂` (R7 → R8 → R9); `linarith` (R10) finishes the weights.
    (2) R2, then rewrite both powers as `1 / (√3 ^ 2) ^ 2` (R12) and use `√3 ^ 2 = 3` (R11).
    (3) R13, R14, witness `k` (R15); with `(n : ℝ) ≠ 0` in the context (R17, R18), `push_cast` then `field_simp`.
H3. (1) `linear_combination (-1 / 2 : ℝ) * (h2 - (x₁ + x₂) * h1 + (x₁ * x₂) * h0)` proves `x₁ * x₂ = -1 / 3`;
    `(3 / 2 : ℝ) * (h3 - …)` likewise proves `x₁ + x₂ = 0`; for the weights, `(w₁ - w₂) * x₁ = 0` is
    `linear_combination h1 - w₂ * hs`, and `sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hx)`.
    (2) `rw [integral_pow, show (1 / √3) ^ 4 = 1 / (√3 ^ 2) ^ 2 by ring, …, hs]; norm_num`.
    (3) `rw [Polynomial.Chebyshev.T_real_cos, Real.cos_eq_zero_iff]`, then `have hn : (n : ℝ) ≠ 0` (R17, R18),
    then `refine ⟨k, ?_⟩; push_cast; field_simp`.
-/
