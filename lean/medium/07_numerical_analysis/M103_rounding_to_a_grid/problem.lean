/- M103 | Rounding to a grid | 15-20 min | round, zpow, relative error, floating point, field_simp, mathlib
GOAL
  Rounding `x` to the nearest point of the grid `h ℤ = {…, -h, 0, h, 2h, …}` has absolute error `≤ h/2`.
  Floats with `p` fraction bits in the binade `[2^e, 2^(e+1))` lie on the grid of spacing `2^(e-p)`;
  rounding any `x ≥ 2^e` to that grid gives `x (1 + δ)` with `|δ| ≤ u = 2^(-p-1)` (the unit roundoff).

REFERENCE
  #check abs_sub_round   -- (x : α) : |x - round x| ≤ 1 / 2     (`round x : ℤ`, nearest integer)
  #check abs_div         -- |a / b| = |a| / |b|                  (also `abs_mul`, `abs_of_pos`)
  #check div_le_iff₀     -- 0 < c → (b / c ≤ a ↔ b ≤ a * c)
  #check zpow_add₀       -- a ≠ 0 → a ^ (m + n) = a ^ m * a ^ n   (exponents m n : ℤ)
  example (e : ℤ) (p : ℕ) : e - (p : ℤ) = (-(p : ℤ) - 1 + e) + 1 := by ring
  example (h x : ℝ) (hh : 0 < h) : h * (x / h) = x := by field_simp
  example (e : ℤ) : (0 : ℝ) < 2 ^ e := by positivity
  `(2 : ℝ) ^ (k : ℤ)` is `zpow` (integer exponent); `(p : ℤ)` casts the natural number `p` to ℤ.
-/
import Mathlib

namespace M103

-- BEGIN SPEC
-- nearest point of the grid h ℤ (ties go up, like `round`)
noncomputable def roundTo (h x : ℝ) : ℝ := h * round (x / h)
-- END SPEC

-- BEGIN SPEC
theorem roundTo_error (h x : ℝ) (hh : 0 < h) : |roundTo h x - x| ≤ h / 2 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem binade_relative_error (p : ℕ) (e : ℤ) (x : ℝ) (hx : 2 ^ e ≤ x) :
    ∃ δ : ℝ, |δ| ≤ 2 ^ (-(p : ℤ) - 1) ∧ roundTo (2 ^ (e - p)) x = x * (1 + δ) :=
-- END SPEC
  sorry

end M103

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `roundTo h x - x = h * (round (x/h) - x/h)`: the error is `h` times the error of rounding `x/h`.
H2. For the binade: the witness is the relative error itself, `δ := (roundTo h x - x) / x` with
    `h = 2 ^ (e - p)`. Its bound is `|roundTo h x - x| / x ≤ (h / 2) / x`, and `h / 2 = 2^(-p-1) * 2^e ≤ 2^(-p-1) * x`.
H3. First theorem: rewrite to `-(h * (x / h - round (x / h)))` (by `unfold roundTo; field_simp; ring`),
    then `rw [abs_neg, abs_mul, abs_of_pos hh]` and `nlinarith [abs_sub_round (x / h)]`. Second: first
    `have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx`; after `rw [abs_div, abs_of_pos hx0, div_le_iff₀ hx0]`, prove `(2:ℝ) ^ (e - p) / 2 = 2 ^ (-(p:ℤ) - 1) * 2 ^ e`
    by rewriting the exponent as `(-p - 1 + e) + 1` and `zpow_add₀ two_ne_zero` twice.
-/
