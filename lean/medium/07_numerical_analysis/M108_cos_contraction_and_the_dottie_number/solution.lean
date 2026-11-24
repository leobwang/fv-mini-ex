/- M108 | cos on [0,1]: contraction and the Dottie number | 15-20 min | mean value theorem, Convex, trig bounds, IVT, ExistsUnique, mathlib
GOAL
  `cos` maps [0,1] into itself and is Lipschitz there with constant `sin 1 < 1` (mean value theorem:
  `|cos'| = |sin| ≤ sin 1` on [0,1]). Payoff: `cos p = p` has exactly one solution in [0,1] (≈ 0.739).

REFERENCE
  `Set.MapsTo f s t` unfolds to `∀ ⦃x⦄, x ∈ s → f x ∈ t`;  `x ∈ Set.Icc a b` unfolds to `a ≤ x ∧ x ≤ b`.
  `∃! p, P p` (exactly one): build it with `refine ⟨p, hp, fun q hq => ?_⟩`, then show `q = p`.
  #check Convex.norm_image_sub_le_of_norm_hasDerivWithin_le  -- (∀ t ∈ s, HasDerivWithinAt f (f' t) s t) → (∀ t ∈ s, ‖f' t‖ ≤ C) → Convex ℝ s → x ∈ s → y ∈ s → ‖f y - f x‖ ≤ C * ‖y - x‖
  example (t : ℝ) : HasDerivWithinAt Real.cos (-Real.sin t) (Set.Icc 0 1) t := (Real.hasDerivAt_cos t).hasDerivWithinAt
  #check Real.sin_le_sin_of_le_of_le_pi_div_two  -- -(π / 2) ≤ x → y ≤ π / 2 → x ≤ y → sin x ≤ sin y
  #check Real.sin_lt                             -- 0 < x → sin x < x
  #check Real.sin_nonneg_of_nonneg_of_le_pi      -- 0 ≤ x → x ≤ π → 0 ≤ sin x
  #check Real.cos_nonneg_of_mem_Icc   -- x ∈ Set.Icc (-(π / 2)) (π / 2) → 0 ≤ cos x   (and Real.cos_le_one x)
  #check Real.pi_gt_three             -- 3 < π
  #check intermediate_value_Icc'      -- a ≤ b → ContinuousOn f (Icc a b) → Icc (f b) (f a) ⊆ f '' Icc a b
  #check Real.norm_eq_abs             -- ‖r‖ = |r|   (on ℝ the norm is the absolute value)
-/
import Mathlib

namespace M108

-- BEGIN SPEC
theorem cos_maps_to : Set.MapsTo Real.cos (Set.Icc 0 1) (Set.Icc 0 1) :=
-- END SPEC
  by
    intro x ⟨h0, h1⟩
    exact ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩,
      Real.cos_le_one x⟩

-- BEGIN SPEC
theorem cos_contracts (x y : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1) :
    |Real.cos x - Real.cos y| ≤ Real.sin 1 * |x - y| :=
-- END SPEC
  by
    have hd : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖-Real.sin t‖ ≤ Real.sin 1 := fun t ⟨h0, h1⟩ => by
      rw [norm_neg, Real.norm_eq_abs,
        abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_gt_three]))]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        (by linarith [Real.pi_gt_three]) h1
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (Real.hasDerivAt_cos t).hasDerivWithinAt) hd (convex_Icc 0 1) hy hx
    simpa [Real.norm_eq_abs] using this

-- BEGIN SPEC
theorem sin_one_lt_one : Real.sin 1 < 1 :=
-- END SPEC
  Real.sin_lt one_pos

-- BEGIN SPEC
theorem dottie_unique : ∃! p, p ∈ Set.Icc (0:ℝ) 1 ∧ Real.cos p = p :=
-- END SPEC
  by
    obtain ⟨p, hp, hfix⟩ : ∃ p ∈ Set.Icc (0:ℝ) 1, Real.cos p - p = 0 :=
      intermediate_value_Icc' (by norm_num) (by fun_prop)
        ⟨by linarith [Real.cos_le_one 1], by simp⟩
    refine ⟨p, ⟨hp, by linarith⟩, fun q ⟨hq, hqfix⟩ => ?_⟩
    have hc := cos_contracts q p hq hp
    rw [hqfix, show Real.cos p = p by linarith] at hc
    -- WHY: `|q - p| ≤ s * |q - p|` with `s < 1` leaves only `|q - p| = 0`.
    have h0 : |q - p| ≤ 0 := by nlinarith [abs_nonneg (q - p), sin_one_lt_one]
    linarith [abs_nonpos_iff.mp h0]

end M108

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. [0,1] sits inside [0, π/2] because π > 3, so `cos ≥ 0` and `0 ≤ sin t ≤ sin 1` for `t ∈ [0,1]`
    (sin is increasing on [-π/2, π/2]); and `sin 1 < 1` because `sin x < x` for `x > 0`.
H2. `cos_contracts`: apply the MVT bound with `f' := fun t => -Real.sin t`, `C := Real.sin 1`, `s := Set.Icc 0 1`,
    then `simpa [Real.norm_eq_abs]`. `dottie_unique`: existence by IVT on `fun x => Real.cos x - x`;
    uniqueness: two fixed points `p, q` give `|q - p| ≤ sin 1 * |q - p|`, which forces `|q - p| ≤ 0`.
H3. Existence: `obtain ⟨p, hp, hfix⟩ : ∃ p ∈ Set.Icc (0:ℝ) 1, Real.cos p - p = 0 :=
    intermediate_value_Icc' (by norm_num) (by fun_prop) ⟨_, _⟩` (endpoint goals: `cos 1 - 1 ≤ 0` and `0 ≤ cos 0 - 0`).
    Uniqueness: `have := cos_contracts q p hq hp`, rewrite both fixed points, then
    `nlinarith [abs_nonneg (q - p), sin_one_lt_one]` gives `|q - p| ≤ 0`; finish with `abs_nonpos_iff`.
-/
