/- Guide for H098 (Mean-field Curie–Weiss transition).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. `G : Prop`
is an arbitrary goal, and a hypothesis `k : … → G` is only there to consume the new fact, so the entry
shows what entered the context. A hypothesis `h` that finishes an example shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (`(2 + y) e^{3y}`, `y² = 2`).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace H098Guide

/-! # Part R · Reference entries -/

/-! ## The exponential form of tanh (milestone `tanh_exp_form`) -/

/-! ### R1. `rw [Real.tanh_eq]` · goal: `tanh x` → `(eˣ - e⁻ˣ) / (eˣ + e⁻ˣ)` -/
example (x : ℝ) (P : ℝ → Prop) (h : P ((Real.exp x - Real.exp (-x)) / (Real.exp x + Real.exp (-x)))) :
    P (Real.tanh x) := by
  rw [Real.tanh_eq]
  exact h

/-! ### R2. `rw [show 3 * x = x + x + x by ring]` · goal: rewrite with an equation proved on the spot -/
example (x : ℝ) (P : ℝ → Prop) (h : P (x + x + x)) : P (3 * x) := by
  rw [show 3 * x = x + x + x by ring]
  exact h

/-! ### R3. `Real.exp_add` · `exp (x + y) = exp x * exp y` · goal -/
example (x y : ℝ) (P : ℝ → Prop) (h : P (Real.exp x * Real.exp y)) : P (Real.exp (x + y)) := by
  rw [Real.exp_add]
  exact h

/-! ### R4. `Real.exp_neg` · `exp (-x) = (exp x)⁻¹` · goal -/
example (x : ℝ) (P : ℝ → Prop) (h : P (Real.exp x)⁻¹) : P (Real.exp (-x)) := by
  rw [Real.exp_neg]
  exact h

/-! ### R5. `have hx := Real.exp_pos x` · context gains `hx : 0 < Real.exp x` -/
example (x : ℝ) (G : Prop) (k : 0 < Real.exp x → G) : G := by
  have hx := Real.exp_pos x
  exact k hx

/-! ### R6. `field_simp` · goal: denominators cleared, using `≠ 0` / `0 <` facts from the context -/
example (x y a : ℝ) (ha : 0 < a) (h : x = a * y) : x / a = y := by
  field_simp
  exact h

/-! ## `tanh y < y` by a monotone function (milestone `tanh_lt_self`) -/

/-! ### R7. `let f : ℝ → ℝ := fun y => …` · context gains a local definition `f` -/
example (G : Prop) (k : (ℝ → ℝ) → G) : G := by
  let f : ℝ → ℝ := fun y => y ^ 2 + 1
  exact k f

/-! ### R8. `apply strictMonoOn_of_deriv_pos (convex_Ici c)` · goal list: monotonicity → continuity, `deriv > 0`
`Set.Ici c = [c, ∞)`; `convex_Ici c : Convex ℝ (Set.Ici c)`; `interior s` is the set of interior points. -/
example (f : ℝ → ℝ) (c : ℝ) (hc : ContinuousOn f (Set.Ici c))
    (hd : ∀ x ∈ interior (Set.Ici c), 0 < deriv f x) : StrictMonoOn f (Set.Ici c) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici c)
  exact hc
  exact hd

/-! ### R9. `fun_prop` · closes `Continuous …` / `ContinuousOn …` of a formula
It knows `+ - * /` (with a `≠ 0` side condition), `Real.exp`, `Real.sinh`, `Real.cosh`, and uses
`Continuous g` hypotheses from the context for unknown functions `g`. -/
example (c : ℝ) : ContinuousOn (fun y : ℝ => y * Real.exp (c * y) - 1) (Set.Ici c) := by
  fun_prop

example (g : ℝ → ℝ) (c : ℝ) (hg : Continuous g) : Continuous (fun y => g (c * y) - y) := by
  fun_prop

/-! ### R10. `rw [interior_Ici] at hx` · context: `x ∈ interior (Set.Ici c)` → `x ∈ Set.Ioi c`
`Set.Ioi c = (c, ∞)`, and `x ∈ Set.Ioi c` is by definition `c < x` (second example). -/
example (c x : ℝ) (G : Prop) (hx : x ∈ interior (Set.Ici c)) (k : x ∈ Set.Ioi c → G) : G := by
  rw [interior_Ici] at hx
  exact k hx

example (c x : ℝ) (hx : x ∈ Set.Ioi c) (G : Prop) (k : c < x → G) : G := by
  have hx0 : c < x := hx
  exact k hx0

/-! ## Building a derivative: `HasDerivAt f f' x` means `f` has derivative `f'` at `x` -/

/-! ### R11. `hasDerivAt_id x` · context gains `HasDerivAt id 1 x` (`id y = y`) -/
example (x : ℝ) (G : Prop) (k : HasDerivAt id 1 x → G) : G := by
  have h := hasDerivAt_id x
  exact k h

/-! ### R12. `hf.const_add c` · `HasDerivAt f f' x → HasDerivAt (fun y => c + f y) f' x` · context -/
example (f : ℝ → ℝ) (f' c x : ℝ) (hf : HasDerivAt f f' x) (G : Prop)
    (k : HasDerivAt (fun y => c + f y) f' x → G) : G := by
  have h := hf.const_add c
  exact k h

/-! ### R13. `hf.const_mul c` · `… → HasDerivAt (fun y => c * f y) (c * f') x` · context -/
example (f : ℝ → ℝ) (f' c x : ℝ) (hf : HasDerivAt f f' x) (G : Prop)
    (k : HasDerivAt (fun y => c * f y) (c * f') x → G) : G := by
  have h := hf.const_mul c
  exact k h

/-! ### R14. `hf.exp` · chain rule: `… → HasDerivAt (fun y => Real.exp (f y)) (Real.exp (f x) * f') x` -/
example (f : ℝ → ℝ) (f' x : ℝ) (hf : HasDerivAt f f' x) (G : Prop)
    (k : HasDerivAt (fun y => Real.exp (f y)) (Real.exp (f x) * f') x → G) : G := by
  have h := hf.exp
  exact k h

/-! ### R15. `hf.const_sub c` · `… → HasDerivAt (fun y => c - f y) (-f') x` · context -/
example (f : ℝ → ℝ) (f' c x : ℝ) (hf : HasDerivAt f f' x) (G : Prop)
    (k : HasDerivAt (fun y => c - f y) (-f') x → G) : G := by
  have h := hf.const_sub c
  exact k h

/-! ### R16. `simpa using h` · closes the goal when `h` and the goal agree after `simp` on both
Here `simp` turns `id y` into `y` and `c * 1` into `c`. -/
example (c x : ℝ) (h : HasDerivAt (fun y => c * id y) (c * 1) x) : HasDerivAt (fun y => c * y) c x := by
  simpa using h

/-! ### R17. `hf.mul hg` · product rule: `HasDerivAt (f * g) (f' * g x + f x * g') x` · context -/
example (f g : ℝ → ℝ) (f' g' x : ℝ) (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) (G : Prop)
    (k : HasDerivAt (f * g) (f' * g x + f x * g') x → G) : G := by
  have h := hf.mul hg
  exact k h

/-! ### R18. `hf.sub hg` · `HasDerivAt (f - g) (f' - g') x` · context -/
example (f g : ℝ → ℝ) (f' g' x : ℝ) (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) (G : Prop)
    (k : HasDerivAt (f - g) (f' - g') x → G) : G := by
  have h := hf.sub hg
  exact k h

/-! ### R19. `apply hf.congr_deriv` · goal: `HasDerivAt f g' x` → `f' = g'` (restate the derivative) -/
example (f : ℝ → ℝ) (f' g' x : ℝ) (hf : HasDerivAt f f' x) (h : f' = g') : HasDerivAt f g' x := by
  apply hf.congr_deriv
  exact h

/-! ### R20. `rw [hf.deriv]` (`HasDerivAt.deriv`) · goal: `deriv f x` → `f'`
`deriv f x` is the derivative of `f` at `x` as a number (it is `0` when `f` is not differentiable). -/
example (f : ℝ → ℝ) (f' x : ℝ) (hf : HasDerivAt f f' x) (P : ℝ → Prop) (h : P f') : P (deriv f x) := by
  rw [hf.deriv]
  exact h

/-! ## Inequalities with `exp` -/

/-! ### R21. `positivity` · closes `0 < e`, `0 ≤ e` or `e ≠ 0`, reading `e`'s shape and `0 < x` hypotheses -/
example (x : ℝ) (hx : 0 < x) : 0 < 2 * x * Real.exp x + x ^ 2 := by
  positivity

example (x : ℝ) (hx : 0 < x) : 2 * x ≠ 0 := by
  positivity

/-! ### R22. `Real.add_one_lt_exp` · `x ≠ 0 → x + 1 < exp x` · context -/
example (x : ℝ) (hx : x ≠ 0) (G : Prop) (k : x + 1 < Real.exp x → G) : G := by
  have h := Real.add_one_lt_exp hx
  exact k h

/-! ### R23. `Real.exp_zero` · `exp 0 = 1` · goal; `simp` uses it, so `simp` closes `exp (t + -t) = 1` -/
example (P : ℝ → Prop) (h : P 1) : P (Real.exp 0) := by
  rw [Real.exp_zero]
  exact h

example (t : ℝ) : Real.exp (t + -t) = 1 := by
  simp

/-! ### R24. `nlinarith [p₁, p₂]` · closes a goal that follows from products of pairs of hypotheses
(the hints `pᵢ` included) by linear arithmetic -/
example (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) : u * u ≤ v * v := by
  nlinarith

example (y : ℝ) (hy : 0 < y) : y < y * (1 + Real.exp y) := by
  nlinarith [Real.exp_pos y]

/-! ## Using strict monotonicity -/

/-! ### R25. `hmono ha hb hab` · `StrictMonoOn f s` applied to `a ∈ s`, `b ∈ s`, `a < b` · context -/
example (f : ℝ → ℝ) (s : Set ℝ) (a b : ℝ) (hmono : StrictMonoOn f s) (ha : a ∈ s) (hb : b ∈ s)
    (hab : a < b) (G : Prop) (k : f a < f b → G) : G := by
  have key := hmono ha hb hab
  exact k key

/-! ### R26. `Set.mem_Ici.mpr` · `c ≤ x → x ∈ Set.Ici c` · context (`le_rfl : c ≤ c`, `h.le : a ≤ b` from `h : a < b`) -/
example (c x : ℝ) (h : c ≤ x) (G : Prop) (k : x ∈ Set.Ici c → G) : G := by
  have hx := Set.mem_Ici.mpr h
  exact k hx

/-! ### R27. `simp only [f] at h` · context: unfold a `let`-bound `f` inside `h` (on the goal: `simp only [f]`) -/
example (g : ℝ → ℝ) (a b : ℝ) (hab : g a < g b) (G : Prop) (k : g a + 1 < g b + 1 → G) : G := by
  let f : ℝ → ℝ := fun y => g y + 1
  have h : f a < f b := by show g a + 1 < g b + 1; linarith
  simp only [f] at h
  exact k h

/-! ### R28. `simp only [mul_zero, Real.exp_zero, add_zero, sub_zero, mul_one, sub_self] at h` · context:
evaluate a formula at `0` (`x * 0 = 0`, `exp 0 = 1`, `x + 0 = x`, `x - 0 = x`, `x * 1 = x`, `x - x = 0`) -/
example (c q : ℝ) (h : (2 + 0) * Real.exp (c * 0) - (2 - 0) < q) (G : Prop) (k : 0 < q → G) : G := by
  simp only [mul_zero, Real.exp_zero, add_zero, sub_zero, mul_one, sub_self] at h
  exact k h

/-! ## Clearing denominators in inequalities -/

/-! ### R29. `rw [div_lt_iff₀ hc]` · `0 < c → (b / c < a ↔ b < a * c)` · goal -/
example (a b c : ℝ) (hc : 0 < c) (h : b < a * c) : b / c < a := by
  rw [div_lt_iff₀ hc]
  exact h

/-! ### R30. `rw [div_le_div_iff₀ hb hd]` · `0 < b → 0 < d → (a / b ≤ c / d ↔ a * d ≤ c * b)` · goal -/
example (a b c d : ℝ) (hb : 0 < b) (hd : 0 < d) (h : a * d ≤ c * b) : a / b ≤ c / d := by
  rw [div_le_div_iff₀ hb hd]
  exact h

/-! ### R31. `Real.add_one_le_exp x` · `x + 1 ≤ exp x` for every `x` · context (a hint for `nlinarith`) -/
example (x : ℝ) (G : Prop) (k : x + 1 ≤ Real.exp x → G) : G := by
  have h := Real.add_one_le_exp x
  exact k h

/-! ## Continuity of tanh (milestone `continuous_tanh`)
Mathlib has no `Real.continuous_tanh`; `Real.tanh_eq_sinh_div_cosh x : tanh x = sinh x / cosh x`. -/

/-! ### R32. `rw [show g = (fun x => …) from funext hg]` · goal: a function name → its formula -/
example (g k : ℝ → ℝ) (hg : ∀ x, g x = k x / 2) (P : (ℝ → ℝ) → Prop) (h : P (fun x => k x / 2)) :
    P g := by
  rw [show g = (fun x => k x / 2) from funext hg]
  exact h

example : ∀ x, Real.tanh x = Real.sinh x / Real.cosh x := Real.tanh_eq_sinh_div_cosh

/-! ### R33. `refine Continuous.div ?_ ?_ ?_` · goal list: `Continuous (fun x => f x / g x)` → three goals -/
example (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (h0 : ∀ x, g x ≠ 0) :
    Continuous (fun x => f x / g x) := by
  refine Continuous.div ?_ ?_ ?_
  exact hf
  exact hg
  exact h0

/-! ### R34. `(Real.cosh_pos x).ne'` · `0 < cosh x`, and `.ne'` turns `0 < e` into `e ≠ 0` · context -/
example (x : ℝ) (G : Prop) (k : Real.cosh x ≠ 0 → G) : G := by
  have h := (Real.cosh_pos x).ne'
  exact k h

/-! ## The transition (`mean_field_transition`) -/

/-! ### R35. `set t₀ := e with ht₀` · context gains `t₀ := e` and `ht₀ : t₀ = e`; goal: `e` → `t₀` -/
example (a : ℝ) (P : ℝ → Prop) (h : ∀ t, P t) : P ((a + 1) / 3) := by
  set t₀ := (a + 1) / 3 with ht₀
  exact h t₀

/-! ### R36. `apply div_pos` · `0 < a → 0 < b → 0 < a / b` · goal list: two sign goals -/
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  apply div_pos
  exact ha
  exact hb

/-! ### R37. `linarith` · closes a goal that is a linear combination of hypotheses (`<`, `≤`, `=`) -/
example (a b : ℝ) (h1 : 1 < a) (h2 : b ≤ a - 1) : b < 2 * a := by
  linarith

/-! ### R38. `rw [div_le_one hb]` · `0 < b → (a / b ≤ 1 ↔ a ≤ b)` · goal -/
example (a b : ℝ) (hb : 0 < b) (h : a ≤ b) : a / b ≤ 1 := by
  rw [div_le_one hb]
  exact h

/-! ### R39. `rw [le_div_iff₀ hc]` · `0 < c → (a ≤ b / c ↔ a * c ≤ b)` · goal -/
example (a b c : ℝ) (hc : 0 < c) (h : a * c ≤ b) : a ≤ b / c := by
  rw [le_div_iff₀ hc]
  exact h

/-! ### R40. `Real.tanh_lt_one x` · `tanh x < 1` · context -/
example (x : ℝ) (G : Prop) (k : Real.tanh x < 1 → G) : G := by
  have h := Real.tanh_lt_one x
  exact k h

/-! ### R41. `apply Continuous.continuousOn` · goal: `ContinuousOn f s` → `Continuous f` -/
example (f : ℝ → ℝ) (s : Set ℝ) (hf : Continuous f) : ContinuousOn f s := by
  apply Continuous.continuousOn
  exact hf

/-! ### R42. `intermediate_value_Icc' hab hf ⟨h1, h2⟩` · IVT for a function that goes down · context
`a ≤ b → ContinuousOn f (Set.Icc a b) → Set.Icc (f b) (f a) ⊆ f '' Set.Icc a b`. A `⊆` is applied to a
membership proof; `y ∈ Set.Icc (f b) (f a)` is the pair `⟨f b ≤ y, y ≤ f a⟩`. -/
example (f : ℝ → ℝ) (a b y : ℝ) (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b)) (h1 : f b ≤ y)
    (h2 : y ≤ f a) (G : Prop) (k : y ∈ f '' Set.Icc a b → G) : G := by
  have h := intermediate_value_Icc' hab hf ⟨h1, h2⟩
  exact k h

/-! ### R43. `obtain ⟨m, hm, hfm⟩ := h` · context: `h : y ∈ f '' s` → a point `m`, `m ∈ s`, `f m = y` -/
example (f : ℝ → ℝ) (s : Set ℝ) (y : ℝ) (h : y ∈ f '' s) (G : Prop) (k : ∀ m ∈ s, f m = y → G) :
    G := by
  obtain ⟨m, hm, hfm⟩ := h
  exact k m hm hfm

/-! ### R44. `apply lt_of_lt_of_le h1` · `a < b → b ≤ c → a < c` · goal: `a < c` → `b ≤ c`
For `hm : m ∈ Set.Icc a b`, `hm.1 : a ≤ m` and `hm.2 : m ≤ b`. -/
example (a b c : ℝ) (h1 : a < b) (h2 : b ≤ c) : a < c := by
  apply lt_of_lt_of_le h1
  exact h2

/-! ### R45. `by_contra h` · goal `G` → `False`, context gains `h : ¬G` -/
example (G : Prop) (hg : G) : G := by
  by_contra h
  exact h hg

/-! ### R46. `push Not at h` · context: push `¬` inward, `¬a < b` → `b ≤ a` (also written `push_neg at h`) -/
example (a b : ℝ) (G : Prop) (h : ¬a < b) (k : b ≤ a → G) : G := by
  push Not at h
  exact k h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A derivative assembled from R11–R19: `(2 + y) e^{3y} - y` -/
example (x : ℝ) :
    HasDerivAt (fun y => (2 + y) * Real.exp (3 * y) - y) ((7 + 3 * x) * Real.exp (3 * x) - 1) x := by
  have h1 : HasDerivAt (fun y : ℝ => 2 + y) 1 x := by
    simpa using (hasDerivAt_id x).const_add 2
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (3 * y)) (Real.exp (3 * x) * 3) x := by
    simpa using ((hasDerivAt_id x).const_mul 3).exp
  exact ((h1.mul h2).sub (hasDerivAt_id x)).congr_deriv (by ring)

/-! ### W2. Strictly increasing from `deriv > 0`: `y ↦ y + eʸ` on `[0, ∞)` (R8, R9, R10, R20, R21) -/
example : StrictMonoOn (fun y : ℝ => y + Real.exp y) (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop)
  intro x hx
  rw [interior_Ici] at hx
  have hd : HasDerivAt (fun y : ℝ => y + Real.exp y) (1 + Real.exp x) x :=
    (hasDerivAt_id x).add (Real.hasDerivAt_exp x)
  rw [hd.deriv]
  positivity

/-! ### W3. IVT on `[1, 2]` for a decreasing sign change: some `m` has `2 - m² = 0` (R41–R43) -/
example : ∃ m ∈ Set.Icc (1 : ℝ) 2, 2 - m ^ 2 = 0 := by
  have hcont : ContinuousOn (fun m : ℝ => 2 - m ^ 2) (Set.Icc 1 2) := by
    apply Continuous.continuousOn
    fun_prop
  have h1 : (fun m : ℝ => 2 - m ^ 2) 2 ≤ 0 := by norm_num
  have h2 : 0 ≤ (fun m : ℝ => 2 - m ^ 2) 1 := by norm_num
  have h := intermediate_value_Icc' (by norm_num : (1 : ℝ) ≤ 2) hcont ⟨h1, h2⟩
  obtain ⟨m, hm, hfm⟩ := h
  exact ⟨m, hm, hfm⟩

end H098Guide
