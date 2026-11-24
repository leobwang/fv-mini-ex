/- Guide for E105 (Derivatives with HasDerivAt).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `g`, `k` or `e` in an entry is only there to finish the example; it shows what the step produced.
Part W: worked combinations on functions that are NOT the exercise's.
Assumed: Lean basics.
-/
import Mathlib

namespace E105Guide

/-! # Part R · Reference entries -/

/-! ## Basic derivative facts (each is a proof term; `have h := …` shows its statement) -/

/-! ### R1. `hasDerivAt_pow n x` · context gains the power rule `HasDerivAt (fun x => x ^ n) (↑n * x ^ (n - 1)) x` -/
example (n : ℕ) (x : ℝ) (G : Prop) (g : HasDerivAt (fun x => x ^ n) (↑n * x ^ (n - 1)) x → G) : G := by
  have h := hasDerivAt_pow n x
  exact g h

/-! ### R2. `hasDerivAt_id' x` · context gains `HasDerivAt (fun x => x) 1 x` -/
example (x : ℝ) (G : Prop) (g : HasDerivAt (fun x => x) 1 x → G) : G := by
  have h := hasDerivAt_id' x
  exact g h

/-! ## Combining facts (dot notation: `hf.const_mul c` is `HasDerivAt.const_mul c hf`) -/

/-! ### R3. `hf.const_mul c` · context gains the constant-multiple rule for `fun y => c * f y` -/
example (f : ℝ → ℝ) (f' x c : ℝ) (hf : HasDerivAt f f' x) (G : Prop)
    (g : HasDerivAt (fun y => c * f y) (c * f') x → G) : G := by
  have h := hf.const_mul c
  exact g h

/-! ### R4. `hf.add hg` · context gains the sum rule; the function is printed `f + g` -/
example (f g : ℝ → ℝ) (f' g' x : ℝ) (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) (G : Prop)
    (k : HasDerivAt (f + g) (f' + g') x → G) : G := by
  have h := hf.add hg
  exact k h

/-! ### R5. `refine hf.congr_deriv ?_` · goal `HasDerivAt f g' x` → `f' = g'` (same function, new derivative) -/
example (f : ℝ → ℝ) (f' g' x : ℝ) (hf : HasDerivAt f f' x) (e : f' = g') : HasDerivAt f g' x := by
  refine hf.congr_deriv ?_
  exact e

/-! ### R6. `norm_num` · closes numeral arithmetic with casts `↑k` and `ℕ` exponents such as `4 - 1` -/
example (b : ℝ) : ((4 : ℕ) : ℝ) * b ^ (4 - 1) + 5 * 1 = 4 * b ^ 3 + 5 := by
  norm_num

/-! ## The exponential, sine and cosine -/

/-! ### R7. `Real.hasDerivAt_exp x` · context gains `HasDerivAt Real.exp (Real.exp x) x` -/
example (x : ℝ) (G : Prop) (g : HasDerivAt Real.exp (Real.exp x) x → G) : G := by
  have h := Real.hasDerivAt_exp x
  exact g h

/-! ### R8. `Real.hasDerivAt_sin x`, `Real.hasDerivAt_cos x` · context gains `sin' = cos`, `cos' = -sin` -/
example (x : ℝ) (G : Prop) (g : HasDerivAt Real.sin (Real.cos x) x → HasDerivAt Real.cos (-Real.sin x) x → G) :
    G := by
  have hs := Real.hasDerivAt_sin x
  have hc := Real.hasDerivAt_cos x
  exact g hs hc

/-! ### R9. `hf.mul hg` · context gains the product rule; the function is printed `f * g` -/
example (f g : ℝ → ℝ) (f' g' x : ℝ) (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) (G : Prop)
    (k : HasDerivAt (f * g) (f' * g x + f x * g') x → G) : G := by
  have h := hf.mul hg
  exact k h

/-! ## From `HasDerivAt` to `deriv` -/

/-! ### R10. `rw [hf.deriv]` (`HasDerivAt.deriv`) · goal: `deriv f x` → the number `f'` -/
example (f : ℝ → ℝ) (f' x : ℝ) (hf : HasDerivAt f f' x) (P : ℝ → Prop) (h : P f') : P (deriv f x) := by
  rw [hf.deriv]
  exact h

/-! # Part W · Worked combinations (not the exercise's functions) -/

/-! ### W1. A polynomial: R1, R3, R2, R4 in one `have`, then R5, R6, and `ring` for what `norm_num` leaves -/
example (b : ℝ) : HasDerivAt (fun x => 3 * x ^ 2 + x) (6 * b + 1) b := by
  have h := ((hasDerivAt_pow 2 b).const_mul 3).add (hasDerivAt_id' b)
  refine h.congr_deriv ?_
  norm_num
  ring

/-! ### W2. A product: R2, R7, R9. `exact` accepts `(fun x => x) * Real.exp` for `fun y => y * Real.exp y`
because the two unfold to the same function (definitional equality). -/
example (x : ℝ) : HasDerivAt (fun y => y * Real.exp y) (1 * Real.exp x + x * Real.exp x) x := by
  have h := (hasDerivAt_id' x).mul (Real.hasDerivAt_exp x)
  exact h

/-! ### W3. `deriv` of a sum: `rw` needs the function written exactly as in the goal, so state the fact
with that function in a `have` (Lean accepts `g + fun x => x` there by definitional equality), then R10. -/
example (g : ℝ → ℝ) (hg : HasDerivAt g 5 1) : deriv (fun x => g x + x) 1 = 6 := by
  have h : HasDerivAt (fun x => g x + x) (5 + 1) 1 := hg.add (hasDerivAt_id' 1)
  rw [h.deriv]
  norm_num

end E105Guide
