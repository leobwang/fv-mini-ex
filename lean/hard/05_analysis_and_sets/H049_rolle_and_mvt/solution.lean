/- H049 | Rolle and the mean value theorem | 45-75 min | HasDerivAt, IsLocalMax, compactness, ContinuousOn, mathlib
GOAL
  Prove Rolle's theorem from the extreme value theorem and Fermat's interior-extremum lemma (Mathlib),
  then the mean value theorem by tilting `f` by a line, then "derivative 0 on `(a, b)` ⇒ constant on
  `[a, b]`". Mathlib's own Rolle/MVT, monotonicity and FTC lemmas are banned (cheatsheet: Traps).
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

GUIDE
  Entries R1–R42: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H049

/- SKELETON · endpoint   (milestone 1; used in `rolle`, step 5)
  1. Turn both memberships into inequalities, in one call:
       simp only [Set.mem_Icc, Set.mem_Ioo, not_and_or, not_lt] at hc hc'   R1, R2, R3, R4
     now hc : a ≤ c ∧ c ≤ b   and   hc' : c ≤ a ∨ b ≤ c
  2. Split hc' into its two cases:                                         R5
  3. Each case: choose the side of the goal, then linarith (it reads both
     halves of the conjunction hc, R7):                                    R6, R7
-/
-- MILESTONE (optional: change or delete)
-- A point of `[a, b]` that is not in `(a, b)` is an endpoint.
theorem endpoint {a b c : ℝ} (hc : c ∈ Set.Icc a b) (hc' : c ∉ Set.Ioo a b) : c = a ∨ c = b := by
  simp only [Set.mem_Icc, Set.mem_Ioo, not_and_or, not_lt] at hc hc'
  rcases hc' with h | h
  · left; linarith
  · right; linarith

/- SKELETON · interior_max   (milestone 2; used in `rolle`, steps 3 and 5)
  1. [a, b] is a neighbourhood of c, from the two parts of hc:              R8, R9
  2. The max on [a, b] is a local max:                                      R10
  3. Fermat with hd:                                                        R11
-/
-- MILESTONE (optional: change or delete)
-- Fermat on an interval: a maximum on `[a, b]` attained inside `(a, b)` has derivative 0.
theorem interior_max {f : ℝ → ℝ} {a b c d : ℝ} (hc : c ∈ Set.Ioo a b) (hmax : IsMaxOn f (Set.Icc a b) c)
    (hd : HasDerivAt f d c) : d = 0 := by
  exact (hmax.isLocalMax (Icc_mem_nhds hc.1 hc.2)).hasDerivAt_eq_zero hd

/- SKELETON · line_hasDerivAt   (milestone 3; used in `mvt`, step 2)
  1. Build the derivative from the identity: id, then `- a`, then `k * _`:  R12 → R13 → R14
  2. The result says slope `k * 1` and mentions `id`; clean up and close:   R15
-/
-- MILESTONE (optional: change or delete)
-- The line `y ↦ k * (y - a)` has slope `k` everywhere.
theorem line_hasDerivAt (k a x : ℝ) : HasDerivAt (fun y => k * (y - a)) k x := by
  simpa using ((hasDerivAt_id x).sub_const a).const_mul k

/- SKELETON · rolle   (prove milestones 1 `endpoint` and 2 `interior_max` first)
  1. hne : (Set.Icc a b).Nonempty                                           R16, R17
  2. A max point c and a min point d of f on [a, b] (EVT):
       obtain ⟨c, hc, hcmax⟩ := …   obtain ⟨d, hd, hdmin⟩ := …               R18, R19, R20, R21
  3. by_cases hc' : c ∈ Set.Ioo a b.  If so: witness c, milestone 2:        R22, R23
  4. by_cases hd' : d ∈ Set.Ioo a b.  If so: witness d, Fermat at a min
     (as milestone 2, but inline):                                          R22, R8, R9, R24, R25, R23
  5. Both are endpoints (milestone 1 on hc hc' and on hd hd'):
       hfc' : f c = f a,  hfd' : f d = f a                                  R26, simp [hfab]
       hm : (a + b) / 2 ∈ Set.Ioo a b                                       R31, R7
       hmax : IsMaxOn f (Set.Icc a b) ((a + b) / 2): take x hx, then
         f x ≤ f c (from hcmax) and f d ≤ f ((a + b) / 2) (from hdmin, via R30),
         restate the goal as an inequality, finish:                         R27, R29, R30, R28, R7
     witness (a + b) / 2, milestone 2 with hmax:                            R23
-/
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

/- SKELETON · mvt   (uses `rolle` and milestone 3 `line_hasDerivAt`)
  1. Name the slope and record b - a ≠ 0:
       set k := (f b - f a) / (b - a) with hk;   hba : b - a ≠ 0            R32, R7
  2. Prove rolle's three hypotheses for the tilted function first (`_` or `?_` in
     the `obtain` of step 3 is an error; inline `(by …)` terms also work):
       h1 : ContinuousOn (fun x => f x - k * (x - a)) (Set.Icc a b)        R33 with R34
       h2 : ∀ x ∈ Set.Ioo a b, HasDerivAt (fun x => f x - k * (x - a)) (f' x - k) x
            from hff' x hx and milestone 3:                                 R35
       h3 : f a - k * (a - a) = f b - k * (b - a)
            clean up (include hk), clear b - a, finish:                     R36 → R37 → ring
  3. obtain ⟨c, hc, h⟩ := rolle (fun x => f x - k * (x - a)) (fun x => f' x - k) a b hab h1 h2 h3
                                                                            R21
  4. h : f' c - k = 0 and the goal reads f' c = k; witness c:              R23, R7
-/
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

/- SKELETON · const_of_deriv_zero   (uses `mvt`)
  1. intro x hx; split a ≤ x (hx.1) into a = x or a < x:                    R8, R38, R26
  2. a = x: rfl
  3. a < x: obtain ⟨c, -, h⟩ := mvt f (fun _ => 0) a x hax (…) (…), the two
     arguments written out as terms (`_` / `?_` there is an error):         R21
       continuity on [a, x] ⊆ [a, b] (hx.2):                               R39 with R40
       derivative 0 at y ∈ (a, x) ⊆ (a, b): fun y hy => hf y ⟨hy.1, …⟩      R31, R41
  4. h : 0 = (f x - f a) / (x - a): record x - a ≠ 0, clear it, finish:     R7, R42, R7
-/
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
H1. Rolle: EVT gives a max point `c` and a min point `d` of `f` on `[a, b]`. If either is in `(a, b)`,
    Fermat finishes. If both are endpoints, `f c = f d = f a`, so `f` is constant on `[a, b]` and the
    midpoint `(a + b) / 2` is a max point. MVT: Rolle for `f` minus the chord's line. Constant: MVT on `[a, x]`.
H2. Rolle: `obtain` both extrema (R19–R21), `by_cases` on each being in `Set.Ioo a b` (R22), milestone
    `interior_max` (and its min twin, R24–R25) for the interior cases, milestone `endpoint` + `rcases … with
    rfl | rfl` for the last. MVT: `set k := (f b - f a) / (b - a)`, apply `rolle` to
    `fun x => f x - k * (x - a)` and `fun x => f' x - k`; `g a = g b` is `simp only` + `field_simp` + `ring`.
    Constant: `rcases eq_or_lt_of_le hx.1 with rfl | hax`, then `mvt f (fun _ => 0) a x hax …`.
H3. Rolle, interior min: `exact ⟨d, hd', (hdmin.isLocalMin (Icc_mem_nhds hd'.1 hd'.2)).hasDerivAt_eq_zero (hff' d hd')⟩`.
    MVT: `obtain ⟨c, hc, h⟩ := rolle (fun x => f x - k * (x - a)) (fun x => f' x - k) a b hab
    (hfc.sub (by fun_prop)) (fun x hx => (hff' x hx).sub (line_hasDerivAt k a x))
    (by simp only [sub_self, mul_zero, sub_zero, hk]; field_simp; ring)`.
    Constant: `mvt f (fun _ => 0) a x hax (hfc.mono (Set.Icc_subset_Icc_right hx.2)) (fun y hy => hf y ⟨hy.1, hy.2.trans_le hx.2⟩)`.
-/
