/- H049 | Rolle and the mean value theorem | 45-75 min | HasDerivAt, IsLocalMax, compactness, ContinuousOn, mathlib
GOAL
  Prove Rolle's theorem from the extreme value theorem and Fermat's "derivative vanishes at an interior
  extremum" (both from Mathlib), then the mean value theorem by tilting `f` by a line, then "zero derivative
  on `(a, b)` ⇒ constant on `[a, b]`". `HasDerivAt f d x`: `f` has derivative `d` at `x`; `ContinuousOn f s`: `f` restricted to `s` is continuous.

REFERENCE
  #check isCompact_Icc                  -- IsCompact (Set.Icc a b)        (`Set.Icc a b` = [a, b], `Set.Ioo a b` = (a, b))
  #check IsCompact.exists_isMaxOn       -- IsCompact s → s.Nonempty → ContinuousOn f s → ∃ x ∈ s, IsMaxOn f s x   (also _isMinOn)
  example (f : ℝ → ℝ) (s : Set ℝ) (c : ℝ) : IsMaxOn f s c ↔ ∀ x ∈ s, f x ≤ f c := Iff.rfl
  #check IsMaxOn.isLocalMax             -- IsMaxOn f s a → s ∈ 𝓝 a → IsLocalMax f a      (`s ∈ 𝓝 a`: s is a neighbourhood of a; `IsLocalMax f a`: f ≤ f a near a; also IsMinOn.isLocalMin)
  #check Icc_mem_nhds                   -- a < x → x < b → Set.Icc a b ∈ 𝓝 x
  #check IsLocalMax.hasDerivAt_eq_zero  -- IsLocalMax f a → HasDerivAt f f' a → f' = 0   (Fermat; also IsLocalMin.)
  #check Set.nonempty_Icc               -- (Set.Icc a b).Nonempty ↔ a ≤ b
  #check HasDerivAt.const_mul           -- (c) → HasDerivAt d d' x → HasDerivAt (fun y => c * d y) (c * d') x   (also hasDerivAt_id x, .sub_const c)
  #check HasDerivAt.sub                 -- HasDerivAt f f' x → HasDerivAt g g' x → HasDerivAt (f - g) (f' - g') x
  example (f : ℝ → ℝ) (k a b : ℝ) (h : ContinuousOn f (Set.Icc a b)) : ContinuousOn (fun y => f y - k * (y - a)) (Set.Icc a b) := h.sub (by fun_prop)
  #check ContinuousOn.mono              -- ContinuousOn f s → t ⊆ s → ContinuousOn f t   (Set.Icc_subset_Icc_right : b₂ ≤ b₁ → Icc a b₂ ⊆ Icc a b₁; Set.Ioo_subset_Icc_self)
BANNED: exists_hasDerivAt_eq_zero, exists_hasDerivAt_eq_zero', exists_deriv_eq_zero, exists_deriv_eq_zero', exists_hasDerivAt_eq_slope, exists_ratio_hasDerivAt_eq_ratio_slope, exists_ratio_hasDerivAt_eq_ratio_slope', exists_deriv_eq_slope, exists_deriv_eq_slope', exists_ratio_deriv_eq_ratio_slope, exists_ratio_deriv_eq_ratio_slope'
BANNED: exists_isLocalExtr_Ioo, exists_Ioo_extr_on_Icc, exists_isExtrOn_Ioo_of_tendsto, exists_isLocalExtr_Ioo_of_tendsto, exists_uIoo_isExtrOn_uIcc, exists_isLocalExtr_uIoo, exists_isExtrOn_uIoo_of_tendsto, exists_isLocalExtr_uIoo_of_tendsto
BANNED: constant_of_has_deriv_right_zero, constant_of_derivWithin_zero, eq_of_has_deriv_right_eq, eq_of_derivWithin_eq, is_const_of_deriv_eq_zero, IsOpen.is_const_of_deriv_eq_zero, IsOpen.exists_is_const_of_deriv_eq_zero, IsOpen.exists_eq_add_of_deriv_eq, norm_image_sub_le_of_norm_deriv_le_segment, norm_image_sub_le_of_norm_deriv_le_segment'
BANNED: HasDerivWithinAt, hasDerivWithinAt, derivWithin, deriv, DifferentiableOn, differentiableOn, DifferentiableAt, differentiableAt
BANNED: image_le_of_liminf_slope_right_lt_deriv_boundary', image_le_of_liminf_slope_right_lt_deriv_boundary, image_le_of_liminf_slope_right_le_deriv_boundary, image_le_of_deriv_right_lt_deriv_boundary', image_le_of_deriv_right_lt_deriv_boundary, image_le_of_deriv_right_le_deriv_boundary, image_norm_le_of_norm_deriv_right_le_deriv_boundary, norm_image_sub_le_of_norm_deriv_right_le_segment, norm_image_sub_le_of_norm_hasDerivWithin_le, norm_image_sub_le_of_norm_hasFDerivWithin_le, norm_image_sub_le_of_norm_hasFDerivWithin_le', lipschitzOnWith_of_nnnorm_hasDerivWithin_le, lipschitzOnWith_of_nnnorm_hasFDerivWithin_le, is_const_of_fderivWithin_eq_zero, is_const_of_fderiv_eq_zero, eqOn_of_fderivWithin_eq, eq_of_fderiv_eq, isLocallyConstant_of_fderiv_eq_zero
BANNED: monotoneOn_of_hasDerivWithinAt_nonneg, antitoneOn_of_hasDerivWithinAt_nonpos, strictMonoOn_of_hasDerivWithinAt_pos, strictAntiOn_of_hasDerivWithinAt_neg, monotone_of_hasDerivAt_nonneg, antitone_of_hasDerivAt_nonpos, strictMono_of_hasDerivAt_pos, strictAnti_of_hasDerivAt_neg, monotoneOn_of_deriv_nonneg, antitoneOn_of_deriv_nonpos, strictMonoOn_of_deriv_pos, strictAntiOn_of_deriv_neg, mul_sub_le_image_sub_of_le_deriv, image_sub_le_mul_sub_of_deriv_le, mul_sub_lt_image_sub_of_lt_deriv, image_sub_lt_mul_sub_of_deriv_lt, domain_mvt
BANNED: exists_hasDerivWithinAt_eq_of_gt_of_lt, exists_hasDerivWithinAt_eq_of_lt_of_gt, exists_hasDerivWithinAt_eq_of_ge_of_le, exists_hasDerivWithinAt_eq_of_le_of_ge, image_hasDerivWithinAt, hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne
BANNED: integral_eq_sub_of_hasDerivAt_of_le, integral_eq_sub_of_hasDerivAt, integral_eq_sub_of_hasDerivAt_of_tendsto, integral_eq_sub_of_hasDeriv_right_of_le, integral_eq_sub_of_hasDeriv_right, integral_eq_sub_of_hasDeriv_right_of_le_real, integral_le_sub_of_hasDeriv_right_of_le, sub_le_integral_of_hasDeriv_right_of_le, sub_le_integral_of_hasDeriv_right_of_le_Ico, integral_deriv_eq_sub, integral_deriv_eq_sub', integral_deriv_eq_sub_uIoo, integral_deriv_mul_eq_sub_of_hasDerivAt, integral_deriv_mul_eq_sub_of_hasDeriv_right, integral_mul_deriv_eq_deriv_mul_of_hasDerivAt, integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right, integral_comp_mul_deriv''', integral_comp_mul_deriv'', integral_comp_mul_deriv', integral_comp_mul_deriv, integral_deriv_smul_comp''', integral_deriv_smul_comp'', lintegral_image_eq_lintegral_abs_deriv_mul, integral_image_eq_integral_abs_deriv_smul
BANNED: ODE_solution_unique_of_mem_Ioo, ODE_solution_unique_of_mem_Icc, ODE_solution_unique_of_mem_Icc_right, ODE_solution_unique_of_mem_Icc_left, ODE_solution_unique_of_eventually, eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right, dist_le_of_trajectories_ODE_of_mem, dist_le_of_trajectories_ODE, taylor_mean_remainder, taylor_mean_remainder_lagrange, taylor_mean_remainder_cauchy
BANNED: HasFDerivWithinAt, hasFDerivWithinAt, HasFDerivAt, hasFDerivAt, HasDerivAtFilter, hasDerivAtFilter, HasFDerivAtFilter
NOTE: Mathlib's Rolle/MVT, derivative-sign monotonicity, Darboux, FTC/substitution and ODE-uniqueness lemmas are banned; the EVT, Fermat and HasDerivAt-arithmetic lemmas above are allowed.
-/
import Mathlib

namespace H049

-- MILESTONE (optional: change or delete)
-- A point of `[a, b]` that is not in `(a, b)` is an endpoint.
theorem endpoint {a b c : ℝ} (hc : c ∈ Set.Icc a b) (hc' : c ∉ Set.Ioo a b) : c = a ∨ c = b := by
  simp only [Set.mem_Icc, Set.mem_Ioo, not_and_or, not_lt] at hc hc'
  rcases hc' with h | h
  · left; linarith
  · right; linarith

-- MILESTONE (optional: change or delete)
-- Fermat on an interval: a maximum on `[a, b]` attained inside `(a, b)` has derivative 0.
theorem interior_max {f : ℝ → ℝ} {a b c d : ℝ} (hc : c ∈ Set.Ioo a b) (hmax : IsMaxOn f (Set.Icc a b) c)
    (hd : HasDerivAt f d c) : d = 0 := by
  exact (hmax.isLocalMax (Icc_mem_nhds hc.1 hc.2)).hasDerivAt_eq_zero hd

-- MILESTONE (optional: change or delete)
-- The line `y ↦ k * (y - a)` has slope `k` everywhere.
theorem line_hasDerivAt (k a x : ℝ) : HasDerivAt (fun y => k * (y - a)) k x := by
  simpa using ((hasDerivAt_id x).sub_const a).const_mul k

-- BEGIN SPEC
theorem rolle (f f' : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hfc : ContinuousOn f (Set.Icc a b))
    (hff' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) (hfab : f a = f b) :
    ∃ c ∈ Set.Ioo a b, f' c = 0 :=
-- END SPEC
  by
    have hne : (Set.Icc a b).Nonempty := Set.nonempty_Icc.mpr hab.le
    obtain ⟨c, hc, hcmax⟩ := isCompact_Icc.exists_isMaxOn hne hfc
    obtain ⟨d, hd, hdmin⟩ := isCompact_Icc.exists_isMinOn hne hfc
    by_cases hc' : c ∈ Set.Ioo a b
    · exact ⟨c, hc', interior_max hc' hcmax (hff' c hc')⟩
    by_cases hd' : d ∈ Set.Ioo a b
    · exact ⟨d, hd', (hdmin.isLocalMin (Icc_mem_nhds hd'.1 hd'.2)).hasDerivAt_eq_zero (hff' d hd')⟩
    -- WHY: both extrema sit at endpoints, so max = min = f a and `f` is constant on `[a, b]`.
    have hfc' : f c = f a := by rcases endpoint hc hc' with rfl | rfl <;> simp [hfab]
    have hfd' : f d = f a := by rcases endpoint hd hd' with rfl | rfl <;> simp [hfab]
    have hm : (a + b) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
    have hmax : IsMaxOn f (Set.Icc a b) ((a + b) / 2) := by
      intro x hx
      have h1 : f x ≤ f c := hcmax hx
      have h2 : f d ≤ f ((a + b) / 2) := hdmin (Set.Ioo_subset_Icc_self hm)
      show f x ≤ f ((a + b) / 2)
      linarith
    exact ⟨(a + b) / 2, hm, interior_max hm hmax (hff' _ hm)⟩

-- BEGIN SPEC
theorem mvt (f f' : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hfc : ContinuousOn f (Set.Icc a b))
    (hff' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Set.Ioo a b, f' c = (f b - f a) / (b - a) :=
-- END SPEC
  by
    set k := (f b - f a) / (b - a) with hk
    have hba : b - a ≠ 0 := by linarith
    obtain ⟨c, hc, h⟩ := rolle (fun x => f x - k * (x - a)) (fun x => f' x - k) a b hab
      (hfc.sub (by fun_prop)) (fun x hx => (hff' x hx).sub (line_hasDerivAt k a x))
      (by simp only [sub_self, mul_zero, sub_zero, hk]; field_simp; ring)
    exact ⟨c, hc, by linarith⟩

-- BEGIN SPEC
theorem const_of_deriv_zero (f : ℝ → ℝ) (a b : ℝ) (hfc : ContinuousOn f (Set.Icc a b))
    (hf : ∀ x ∈ Set.Ioo a b, HasDerivAt f 0 x) : ∀ x ∈ Set.Icc a b, f x = f a :=
-- END SPEC
  by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hax
    · rfl
    obtain ⟨c, -, h⟩ := mvt f (fun _ => 0) a x hax (hfc.mono (Set.Icc_subset_Icc_right hx.2))
      (fun y hy => hf y ⟨hy.1, hy.2.trans_le hx.2⟩)
    have : x - a ≠ 0 := by linarith
    field_simp at h
    linarith

end H049

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Rolle: take a max point `c` and a min point `d` of `f` on `[a, b]` (compactness). If either lies in `(a, b)`, Fermat finishes. If both are endpoints, `f c = f d = f a`, so `f` is constant on `[a, b]` and every interior point (say `(a + b) / 2`) is a max point.
H2. MVT: with `k = (f b - f a) / (b - a)`, apply `rolle` to `g x = f x - k * (x - a)` and `g' x = f' x - k`; `g a = g b` is algebra (`field_simp`). Constant: for `a < x`, apply `mvt` on `[a, x]` with `f' = fun _ => 0`.
H3. Rolle, interior case: `exact ⟨c, hc', (hcmax.isLocalMax (Icc_mem_nhds hc'.1 hc'.2)).hasDerivAt_eq_zero (hff' c hc')⟩`. MVT: `obtain ⟨c, hc, h⟩ := rolle (fun x => f x - k * (x - a)) (fun x => f' x - k) a b hab (hfc.sub (by fun_prop)) (fun x hx => (hff' x hx).sub (line_hasDerivAt k a x)) ?_`.
-/
