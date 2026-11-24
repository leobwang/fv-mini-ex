/- H098 | Mean-field Curie–Weiss transition | 1-1.5 h | tanh inequalities, derivative monotonicity, intermediate value theorem, mathlib
GOAL
  Mean-field (Curie–Weiss) theory: the magnetisation per spin `m` solves `m = tanh (a * m)`, where
  `a = βJz` (β = 1/(kB T), J = coupling, z = number of neighbours). Prove a solution `m > 0`
  (spontaneous magnetisation) exists iff `a > 1`, i.e. iff `T < T_c = Jz/kB`.

REFERENCE
  #check Real.tanh_eq         -- tanh x = (exp x - exp (-x)) / (exp x + exp (-x))
  #check Real.add_one_le_exp  -- x + 1 ≤ exp x   (strict: `Real.add_one_lt_exp : x ≠ 0 → x + 1 < exp x`)
  #check strictMonoOn_of_deriv_pos  -- Convex ℝ D → ContinuousOn f D → (∀ x ∈ interior D, 0 < deriv f x) → StrictMonoOn f D
  #check interior_Ici         -- interior (Set.Ici a) = Set.Ioi a    (convexity: `convex_Ici 0`)
  #check HasDerivAt.deriv     -- HasDerivAt f f' x → deriv f x = f'   (`.mul`, `.sub`, `.congr_deriv` combine them)
  example (x : ℝ) : HasDerivAt (fun y => Real.exp (-2 * y)) (Real.exp (-2 * x) * (-2)) x := by simpa using ((hasDerivAt_id x).const_mul (-2)).exp
  #check intermediate_value_Icc'  -- a ≤ b → ContinuousOn f (Icc a b) → Icc (f b) (f a) ⊆ f '' Icc a b
  #check Real.tanh_lt_one     -- tanh x < 1
  #check Real.tanh_eq_sinh_div_cosh  -- Mathlib has no `Real.continuous_tanh`: go through sinh / cosh
  #check div_lt_iff₀          -- 0 < c → (b / c < a ↔ b < a * c)   (two fractions: `div_le_div_iff₀`)
NOTE: `Set.Icc a b = [a, b]`, `Set.Ici a = [a, ∞)`, `Set.Ioi a = (a, ∞)`; `f '' s` is the image of `s`.
-/
import Mathlib

namespace H098

-- MILESTONE (optional: change or delete)
theorem tanh_exp_form (y : ℝ) :
    Real.tanh y = (Real.exp (2 * y) - 1) / (Real.exp (2 * y) + 1) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem tanh_lt_self (y : ℝ) (hy : 0 < y) : Real.tanh y < y := by
  sorry

-- MILESTONE (optional: change or delete)
theorem le_tanh (y : ℝ) (hy : 0 ≤ y) : y / (1 + y) ≤ Real.tanh y := by
  sorry

-- MILESTONE (optional: change or delete)
theorem continuous_tanh : Continuous Real.tanh := by
  sorry

-- BEGIN SPEC
theorem mean_field_transition (a : ℝ) (ha : 0 < a) :
    1 < a ↔ ∃ m : ℝ, 0 < m ∧ Real.tanh (a * m) = m :=
-- END SPEC
  sorry

end H098

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. (←) If `a ≤ 1` and `m > 0` solved it, `m = tanh (a m) < a m ≤ m`. (→) `g m = tanh (a m) - m` is
    positive for small `m > 0` and negative at `m = 1` (`tanh < 1`): use the intermediate value theorem.
H2. With `tanh y = (e^{2y} - 1)/(e^{2y} + 1)`: `tanh y < y` ⇔ `1 - y < (1 + y) e^{-2y}`; the right side
    minus the left, `f y = (1 + y) e^{-2y} - (1 - y)`, has `f 0 = 0` and `f' y = 1 - (1 + 2y) e^{-2y} > 0`
    for `y > 0` (since `e^{2y} > 1 + 2y`), so `f` is strictly increasing on `[0, ∞)`.
    The lower bound `y/(1+y) ≤ tanh y` is cross-multiplication plus `e^{2y} ≥ 1 + 2y`.
H3. (→): take `m₀ = (a - 1) / (2 * a)`, so `a m₀ = (a - 1)/2` and `le_tanh` gives `g m₀ ≥ 0`; then
    `obtain ⟨m, hm, hgm⟩ := intermediate_value_Icc' hm₀1 hcont ⟨hg1, hg0⟩` on `Set.Icc m₀ 1`.
    `tanh_lt_self`: `apply strictMonoOn_of_deriv_pos (convex_Ici 0)`, then `rw [hd.deriv]` where
    `hd : HasDerivAt f (1 - (1 + 2 * x) * Real.exp (-2 * x)) x`; finish with `nlinarith` using
    `Real.exp (2 * x) * Real.exp (-2 * x) = 1`.
-/
