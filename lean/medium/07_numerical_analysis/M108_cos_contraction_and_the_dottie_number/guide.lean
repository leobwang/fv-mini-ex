/- Guide for M108 (cos on [0,1]: contraction and the Dottie number).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (sin instead of cos, other
intervals, other functions).
Assumed: Lean basics.
-/
import Mathlib

namespace M108Guide

/-! # Part R · Reference entries -/

/-! ## Intervals and `Set.MapsTo` -/

/-! ### R1. `intro x ⟨h0, h1⟩` on `Set.MapsTo f (Set.Icc a b) t` · context gains `x`, `h0`, `h1`
`Set.MapsTo f s t` is `∀ ⦃x⦄, x ∈ s → f x ∈ t`, and `x ∈ Set.Icc a b` is `a ≤ x ∧ x ≤ b`, so one
`intro` with a pattern takes both apart. The same pattern works on `∀ x ∈ Set.Icc a b, P x`. -/
example (f : ℝ → ℝ) (a b : ℝ) (t : Set ℝ) (h : ∀ x, a ≤ x → x ≤ b → f x ∈ t) :
    Set.MapsTo f (Set.Icc a b) t := by
  intro x ⟨h0, h1⟩
  exact h x h0 h1

/-! ### R2. `refine ⟨?_, ?_⟩` on `y ∈ Set.Icc a b` · goal → two goals `a ≤ y`, `y ≤ b`
`exact ⟨e₀, e₁⟩` does the same in one go when both proofs are at hand. -/
example (a b y : ℝ) (h0 : a ≤ y) (h1 : y ≤ b) : y ∈ Set.Icc a b := by
  refine ⟨?_, ?_⟩
  exacts [h0, h1]

/-! ## Trig bounds -/

/-! ### R3. `Real.cos_nonneg_of_mem_Icc` · `x ∈ Icc (-(π/2)) (π/2) → 0 ≤ cos x` · goal `0 ≤ cos x` → membership -/
example (x : ℝ) (h : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) : 0 ≤ Real.cos x := by
  apply Real.cos_nonneg_of_mem_Icc
  exact h

/-! ### R4. `Real.cos_le_one x` · the fact `cos x ≤ 1`, for every real `x` -/
example (x : ℝ) : Real.cos x ≤ 1 := by
  exact Real.cos_le_one x

/-! ### R5. `linarith [Real.pi_pos, Real.pi_gt_three]` · closes a linear (in)equality
`linarith` uses the hypotheses plus the extra facts in `[…]`: `Real.pi_pos : 0 < π`,
`Real.pi_gt_three : 3 < π`. It treats `π`, `Real.cos 1`, `|d|` as unknowns. -/
example (x : ℝ) (h1 : x ≤ 1) : x ≤ Real.pi / 2 := by
  linarith [Real.pi_gt_three]

/-! ### R13. `Real.sin_nonneg_of_nonneg_of_le_pi` · `0 ≤ x → x ≤ π → 0 ≤ sin x` · goal → two side goals -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi) : 0 ≤ Real.sin x := by
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  exacts [h0, h1]

/-! ### R14. `Real.sin_le_sin_of_le_of_le_pi_div_two` · `-(π/2) ≤ x → y ≤ π/2 → x ≤ y → sin x ≤ sin y`
sin is increasing on [-π/2, π/2]. `apply` leaves the three hypotheses as goals, in this order. -/
example (x y : ℝ) (hx : -(Real.pi / 2) ≤ x) (hy : y ≤ Real.pi / 2) (hxy : x ≤ y) :
    Real.sin x ≤ Real.sin y := by
  apply Real.sin_le_sin_of_le_of_le_pi_div_two
  exacts [hx, hy, hxy]

/-! ### R16. `Real.sin_lt` · `0 < x → sin x < x` -/
example (x : ℝ) (hx : 0 < x) : Real.sin x < x := by
  exact Real.sin_lt hx

/-! ### R17. `one_pos` · the fact `0 < 1` in any ordered field such as `ℝ` -/
example : (0 : ℝ) < 1 := by
  exact one_pos

/-! ## Derivatives and the mean value theorem -/

/-! ### R6. `Real.hasDerivAt_cos t` · the fact `HasDerivAt Real.cos (-Real.sin t) t` -/
example (t : ℝ) : HasDerivAt Real.cos (-Real.sin t) t := by
  exact Real.hasDerivAt_cos t

/-! ### R7. `HasDerivAt.hasDerivWithinAt` · a derivative at `t` is a derivative within any set `s` at `t`
Written with dot notation: `(hd : HasDerivAt f f' t).hasDerivWithinAt`. -/
example (f : ℝ → ℝ) (f' t : ℝ) (s : Set ℝ) (hd : HasDerivAt f f' t) :
    HasDerivWithinAt f f' s t := by
  exact hd.hasDerivWithinAt

/-! ### R8. `convex_Icc a b` · the fact `Convex ℝ (Set.Icc a b)` -/
example (a b : ℝ) : Convex ℝ (Set.Icc a b) := by
  exact convex_Icc a b

/-! ### R9. `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` (mean value bound) · context gains the bound
`(∀ t ∈ s, HasDerivWithinAt f (f' t) s t) → (∀ t ∈ s, ‖f' t‖ ≤ C) → Convex ℝ s → x ∈ s → y ∈ s →
 ‖f y - f x‖ ≤ C * ‖y - x‖`. Mind the order: the conclusion is about `f y - f x`. -/
example (f f' : ℝ → ℝ) (s : Set ℝ) (C x y : ℝ) (hf : ∀ t ∈ s, HasDerivWithinAt f (f' t) s t)
    (hC : ∀ t ∈ s, ‖f' t‖ ≤ C) (hs : Convex ℝ s) (hx : x ∈ s) (hy : y ∈ s) (G : Prop)
    (g : ‖f y - f x‖ ≤ C * ‖y - x‖ → G) : G := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hf hC hs hx hy
  exact g h

/-! ## Norms and absolute values -/

/-! ### R10. `norm_neg` · `‖-a‖ = ‖a‖` -/
example {E : Type} [SeminormedAddGroup E] (a : E) (P : ℝ → Prop) (h : P ‖a‖) : P ‖-a‖ := by
  rw [norm_neg]
  exact h

/-! ### R11. `Real.norm_eq_abs` · `‖r‖ = |r|`: on `ℝ` the norm is the absolute value -/
example (r : ℝ) (P : ℝ → Prop) (h : P |r|) : P ‖r‖ := by
  rw [Real.norm_eq_abs]
  exact h

/-! ### R12. `abs_of_nonneg` · `0 ≤ a → |a| = a` · goal rewritten, plus side goal `0 ≤ a` -/
example (a : ℝ) (P : ℝ → Prop) (h : P a) (ha : 0 ≤ a) : P |a| := by
  rw [abs_of_nonneg]
  exact h
  exact ha

/-! ### R15. `simpa [Real.norm_eq_abs] using h` · closes the goal from `h` once both are simplified -/
example (a b c : ℝ) (h : ‖a‖ ≤ c * ‖b‖) : |a| ≤ c * |b| := by
  simpa [Real.norm_eq_abs] using h

/-! ## Existence: the intermediate value theorem -/

/-! ### R18. `intermediate_value_Icc'` · context gains a point `p` where `f p = y`
`a ≤ b → ContinuousOn f (Set.Icc a b) → Set.Icc (f b) (f a) ⊆ f '' Set.Icc a b` (the primed version is
for `f` going DOWN: `f b ≤ y ≤ f a`). `y ∈ f '' s` unfolds to `∃ p, p ∈ s ∧ f p = y`, so `obtain`
takes it apart. -/
example (f : ℝ → ℝ) (a b y : ℝ) (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (h1 : f b ≤ y) (h2 : y ≤ f a) (G : Prop) (g : ∀ p ∈ Set.Icc a b, f p = y → G) : G := by
  obtain ⟨p, hp, hfp⟩ := intermediate_value_Icc' hab hf ⟨h1, h2⟩
  exact g p hp hfp

/-! ### R19. `fun_prop` · closes `Continuous …` / `ContinuousOn …` for functions built from continuous pieces -/
example (a b : ℝ) : ContinuousOn (fun x => Real.sin x + 2 * x) (Set.Icc a b) := by
  fun_prop

/-! ### R20. `Real.cos_zero` · `cos 0 = 1`; `simp` applies it (and `sub_zero`) by itself -/
example (P : ℝ → Prop) (h : P 1) : P (Real.cos 0 - 0) := by
  simp
  exact h

/-! ## Uniqueness -/

/-! ### R21. `refine ⟨a, ha, fun y hy => ?_⟩` on `∃! x, P x` · goal → `y = a`, context gains `y`, `hy`
`∃! x, P x` means `∃ x, P x ∧ ∀ y, P y → y = x`: give the witness, its proof, then show any other
`y` with `P y` equals it. -/
example {α : Type} (P : α → Prop) (a : α) (ha : P a) (h : ∀ y, P y → y = a) : ∃! x, P x := by
  refine ⟨a, ha, fun y hy => ?_⟩
  exact h y hy

/-! ### R22. `rw [h₁, h₂] at h` · context: rewrites inside hypothesis `h`, goal unchanged
An equation proved on the spot works too: `rw [show u = v by linarith] at h`. -/
example (u v w : ℝ) (P : ℝ → ℝ → Prop) (h₁ : u = w) (h₂ : v = w) (h : P u v) : P w w := by
  rw [h₁, h₂] at h
  exact h

/-! ### R23. `abs_nonneg a` · the fact `0 ≤ |a|` -/
example (a : ℝ) : 0 ≤ |a| := by
  exact abs_nonneg a

/-! ### R24. `nlinarith [facts]` · closes a goal that needs products of hypotheses
Here it multiplies `1 - s > 0` by the negated goal `d > 0`. `linarith` cannot: `s * d` is a product of unknowns.
Extra facts go in brackets, as for `linarith`: `nlinarith [abs_nonneg d, hs]`. -/
example (d s : ℝ) (hs : s < 1) (h : d ≤ s * d) : d ≤ 0 := by
  nlinarith

/-! ### R25. `abs_nonpos_iff` · `|a| ≤ 0 ↔ a = 0`; `.mp` turns `|a| ≤ 0` into `a = 0` -/
example (a : ℝ) (G : Prop) (h0 : |a| ≤ 0) (g : a = 0 → G) : G := by
  have h := abs_nonpos_iff.mp h0
  exact g h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `sin` maps [0,1] into [0,1]: R1, R2, R13, R5, then `Real.sin_le_one` -/
example : Set.MapsTo Real.sin (Set.Icc 0 1) (Set.Icc 0 1) := by
  intro x ⟨h0, h1⟩
  exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_gt_three]), Real.sin_le_one x⟩

/-! ### W2. Mean value bound for `sin` on [-1,2] (`|sin'| = |cos| ≤ 1`): R6–R11, R15 -/
example (u v : ℝ) (hu : u ∈ Set.Icc (-1:ℝ) 2) (hv : v ∈ Set.Icc (-1:ℝ) 2) :
    |Real.sin u - Real.sin v| ≤ 1 * |u - v| := by
  have hd : ∀ t ∈ Set.Icc (-1:ℝ) 2, ‖Real.cos t‖ ≤ 1 := fun t _ => by
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one t
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (Real.hasDerivAt_sin t).hasDerivWithinAt) hd (convex_Icc (-1) 2) hv hu
  simpa [Real.norm_eq_abs] using this

/-! ### W3. IVT on a decreasing function, `2 - x - x³` on [0,1]: R18 with R19 and `norm_num` -/
example : ∃ p ∈ Set.Icc (0:ℝ) 1, 2 - p - p ^ 3 = 1 := by
  obtain ⟨p, hp, hfp⟩ : ∃ p ∈ Set.Icc (0:ℝ) 1, 2 - p - p ^ 3 = 1 :=
    intermediate_value_Icc' (by norm_num) (by fun_prop) ⟨by norm_num, by norm_num⟩
  exact ⟨p, hp, hfp⟩

/-! ### W4. Uniqueness from a strict contraction: R21, R22, R23, R24, R25 -/
example (g : ℝ → ℝ) (hg : ∀ u v : ℝ, |g u - g v| ≤ (1 / 2) * |u - v|) (a : ℝ) (ha : g a = a) :
    ∃! x, g x = x := by
  refine ⟨a, ha, fun y hy => ?_⟩
  have hc := hg y a
  rw [hy, ha] at hc
  have h0 : |y - a| ≤ 0 := by nlinarith [abs_nonneg (y - a)]
  linarith [abs_nonpos_iff.mp h0]

end M108Guide
