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
  rw [Real.tanh_eq, show 2 * y = y + y by ring, Real.exp_add, Real.exp_neg]
  have := Real.exp_pos y
  field_simp

-- MILESTONE (optional: change or delete)
theorem tanh_lt_self (y : ℝ) (hy : 0 < y) : Real.tanh y < y := by
  -- f y = (1 + y) e^{-2y} - (1 - y) vanishes at 0 and is strictly increasing on [0, ∞)
  let f : ℝ → ℝ := fun y => (1 + y) * Real.exp (-2 * y) - (1 - y)
  have hmono : StrictMonoOn f (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop)
    intro x hx
    rw [interior_Ici] at hx
    have hd : HasDerivAt f (1 - (1 + 2 * x) * Real.exp (-2 * x)) x := by
      have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
        simpa using (hasDerivAt_id x).const_add 1
      have h2 : HasDerivAt (fun y : ℝ => Real.exp (-2 * y)) (Real.exp (-2 * x) * (-2)) x := by
        simpa using ((hasDerivAt_id x).const_mul (-2)).exp
      have h3 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub 1
      exact ((h1.mul h2).sub h3).congr_deriv (by ring)
    rw [hd.deriv]
    have hx0 : (0 : ℝ) < x := hx
    have hlt : 2 * x + 1 < Real.exp (2 * x) := Real.add_one_lt_exp (by positivity)
    have hinv : Real.exp (2 * x) * Real.exp (-2 * x) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-2 * x)]
  have key := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy.le) hy
  simp only [f, mul_zero, Real.exp_zero, add_zero, sub_zero, mul_one, sub_self] at key
  rw [tanh_exp_form, div_lt_iff₀ (by positivity)]
  have hinv : Real.exp (2 * y) * Real.exp (-2 * y) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (2 * y), Real.exp_pos (-2 * y)]

-- MILESTONE (optional: change or delete)
theorem le_tanh (y : ℝ) (hy : 0 ≤ y) : y / (1 + y) ≤ Real.tanh y := by
  rw [tanh_exp_form, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [Real.add_one_le_exp (2 * y)]

-- MILESTONE (optional: change or delete)
theorem continuous_tanh : Continuous Real.tanh := by
  rw [show Real.tanh = fun x => Real.sinh x / Real.cosh x from funext Real.tanh_eq_sinh_div_cosh]
  exact Continuous.div (by fun_prop) (by fun_prop) fun x => (Real.cosh_pos x).ne'

-- BEGIN SPEC
theorem mean_field_transition (a : ℝ) (ha : 0 < a) :
    1 < a ↔ ∃ m : ℝ, 0 < m ∧ Real.tanh (a * m) = m :=
-- END SPEC
  by
    constructor
    · intro h1
      -- g m = tanh (a m) - m changes sign on [m₀, 1]
      set m₀ := (a - 1) / (2 * a) with hm₀
      have hm₀pos : 0 < m₀ := div_pos (by linarith) (by linarith)
      have hm₀1 : m₀ ≤ 1 := by rw [hm₀, div_le_one (by linarith)]; linarith
      have ham₀ : a * m₀ = (a - 1) / 2 := by rw [hm₀]; field_simp
      let g : ℝ → ℝ := fun m => Real.tanh (a * m) - m
      have hg0 : 0 ≤ g m₀ := by
        have h := le_tanh (a * m₀) (by positivity)
        have hk : m₀ ≤ a * m₀ / (1 + a * m₀) := by
          rw [le_div_iff₀ (by positivity), ham₀]
          nlinarith
        simp only [g]
        linarith
      have hg1 : g 1 ≤ 0 := by
        simp only [g, mul_one]
        linarith [Real.tanh_lt_one a]
      have hcont : ContinuousOn g (Set.Icc m₀ 1) := by
        have := continuous_tanh
        exact (by fun_prop : Continuous g).continuousOn
      obtain ⟨m, hm, hgm⟩ := intermediate_value_Icc' hm₀1 hcont ⟨hg1, hg0⟩
      refine ⟨m, lt_of_lt_of_le hm₀pos hm.1, ?_⟩
      simp only [g] at hgm
      linarith
    · rintro ⟨m, hm, heq⟩
      by_contra h
      push Not at h
      -- m = tanh (a m) < a m ≤ m
      have := tanh_lt_self (a * m) (by positivity)
      nlinarith

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
