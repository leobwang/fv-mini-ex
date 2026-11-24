/- Guide for H071 (Jacobi iteration converges).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Vectors are functions `Fin n → ℝ` (or `ι → ℝ` for any index type `ι`); `‖v‖` on them is the sup norm.
Part W: worked combinations on objects that are NOT the exercise's (a halving map, a scalar iteration).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Matrix Finset Filter Topology

namespace H071Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · The solution is a fixed point (`jacobi_fixed`) -/

/-! ### R1. `funext i` · goal `f = g` (functions, e.g. vectors) → context gains `i`, goal `f i = g i` -/
example {ι : Type} (f g : ι → ℝ) (h : ∀ i, f i = g i) : f = g := by
  funext i
  exact h i

/-! ### R2. `congrFun h i` · from `h : f = g` get `f i = g i` · context, with `have` -/
example {ι : Type} (f g : ι → ℝ) (i : ι) (Q : Prop) (h : f = g) (hQ : f i = g i → Q) : Q := by
  have hi := congrFun h i
  exact hQ hi

/-! ### R3. `simp only [mulVec, dotProduct] at h` · context: `(M *ᵥ v) i` → `∑ j, M i j * v j` -/
example {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v c : Fin n → ℝ) (i : Fin n) (Q : Prop)
    (h : (M *ᵥ v) i = c i) (hQ : ∑ j, M i j * v j = c i → Q) : Q := by
  simp only [mulVec, dotProduct] at h
  exact hQ h

/-! ### R4. `Finset.add_sum_erase` · `a ∈ s → f a + ∑ x ∈ s.erase a, f x = ∑ x ∈ s, f x` · goal
Right to left (`rw [← …]`) it splits the term `a` off a sum. `s.erase a` is `s` without `a`. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (a : ι) (P : ℝ → Prop)
    (h : P (f a + ∑ x ∈ univ.erase a, f x)) : P (∑ x, f x) := by
  rw [← add_sum_erase _ _ (mem_univ a)]
  exact h

/-! ### R5. `Finset.mem_univ` · `a ∈ univ`: every element of a finite type is in `univ` · closes the goal -/
example {ι : Type} [Fintype ι] (a : ι) : a ∈ (univ : Finset ι) := by
  exact mem_univ a

/-! ### R6. `div_eq_iff` · `c ≠ 0 → (a / c = b ↔ a = b * c)` · goal: clears a division -/
example (a b c : ℝ) (hc : c ≠ 0) (h : a = b * c) : a / c = b := by
  rw [div_eq_iff hc]
  exact h

/-! ### R7. `linarith` · closes a linear (in)equality that follows from the hypotheses
A product such as `d * x` counts as one unknown (and `x * d` is the same one). -/
example (d s c x : ℝ) (h : d * x + s = c) : c - s = x * d := by
  linarith

/-! ## Part 2 · One sweep is a contraction (`jacobi_contract`) -/

/-! ### R8. `pi_norm_le_iff_of_nonneg` · `0 ≤ r → (‖v‖ ≤ r ↔ ∀ i, ‖v i‖ ≤ r)` · goal: sup norm → coordinates -/
example {n : ℕ} (v : Fin n → ℝ) (r : ℝ) (hr : 0 ≤ r) (h : ∀ i, ‖v i‖ ≤ r) : ‖v‖ ≤ r := by
  rw [pi_norm_le_iff_of_nonneg hr]
  exact h

/-! ### R9. `positivity` · closes `0 ≤ e` / `0 < e` from the shape of `e` (and hypotheses `0 ≤ x`) -/
example {n : ℕ} (r : ℝ) (v : Fin n → ℝ) (hr : 0 ≤ r) : 0 ≤ r * ‖v‖ := by
  positivity

/-! ### R10. `abs_pos` · `0 < |a| ↔ a ≠ 0` · goal; term form `abs_pos.mpr ha` -/
example (a : ℝ) (ha : a ≠ 0) : 0 < |a| := by
  rw [abs_pos]
  exact ha

/-! ### R11. `Pi.sub_apply` · `(f - g) i = f i - g i` · goal -/
example {ι : Type} (f g : ι → ℝ) (i : ι) (P : ℝ → Prop) (h : P (f i - g i)) : P ((f - g) i) := by
  rw [Pi.sub_apply]
  exact h

/-! ### R12. `Real.norm_eq_abs` · `‖r‖ = |r|` for a real number `r` · goal -/
example (r : ℝ) (P : ℝ → Prop) (h : P |r|) : P ‖r‖ := by
  rw [Real.norm_eq_abs]
  exact h

/-! ### R13. `sub_div` · `(a - b) / c = a / c - b / c`; right to left: `rw [← sub_div]` · goal -/
example (a b c : ℝ) (P : ℝ → Prop) (h : P ((a - b) / c)) : P (a / c - b / c) := by
  rw [← sub_div]
  exact h

/-! ### R14. `abs_div` · `|a / b| = |a| / |b|` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (|a| / |b|)) : P |a / b| := by
  rw [abs_div]
  exact h

/-! ### R15. `div_le_iff₀` · `0 < c → (a / c ≤ b ↔ a ≤ b * c)` · goal: clears a positive denominator -/
example (a b c : ℝ) (hc : 0 < c) (h : a ≤ b * c) : a / c ≤ b := by
  rw [div_le_iff₀ hc]
  exact h

/-! ### R16. `mul_sub` · `a * (b - c) = a * b - a * c` · goal; under `∑` use `simp only [mul_sub]` -/
example {ι : Type} (s : Finset ι) (a u v : ι → ℝ) (P : ℝ → Prop)
    (h : P (∑ j ∈ s, (a j * u j - a j * v j))) : P (∑ j ∈ s, a j * (u j - v j)) := by
  simp only [mul_sub]
  exact h

/-! ### R17. `Finset.sum_sub_distrib` · `∑ j ∈ s, (f j - g j) = ∑ j ∈ s, f j - ∑ j ∈ s, g j` · goal -/
example {ι : Type} (s : Finset ι) (f g : ι → ℝ) (P : ℝ → Prop)
    (h : P (∑ j ∈ s, f j - ∑ j ∈ s, g j)) : P (∑ j ∈ s, (f j - g j)) := by
  rw [sum_sub_distrib]
  exact h

/-! ### R18. `abs_neg` · `|-a| = |a|` · goal -/
example (a : ℝ) (P : ℝ → Prop) (h : P |a|) : P |-a| := by
  rw [abs_neg]
  exact h

/-! ### R19. `calc` · closes `a ≤ d` from a chain `a ≤ b = c ≤ d`, one proof per link
The first term may be `_`: it then stands for the left side of the goal. -/
example (a b c d : ℝ) (h1 : a ≤ b) (h2 : b = c) (h3 : c ≤ d) : a ≤ d := by
  calc _ ≤ b := h1
    _ = c := h2
    _ ≤ d := h3

/-! ### R20. `Finset.abs_sum_le_sum_abs` · `|∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i|` (triangle inequality) -/
example {ι : Type} (s : Finset ι) (f : ι → ℝ) : |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i| := by
  exact abs_sum_le_sum_abs f s

/-! ### R21. `h.trans` (`le_trans`) · goal `a ≤ c` with `h : a ≤ b` → goal `b ≤ c` -/
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  refine h₁.trans ?_
  exact h₂

/-! ### R22. `Finset.sum_le_sum` · `(∀ i ∈ s, f i ≤ g i) → ∑ f ≤ ∑ g` · goal: compare term by term -/
example {ι : Type} (s : Finset ι) (f g : ι → ℝ) (h : ∀ j, f j ≤ g j) :
    ∑ j ∈ s, f j ≤ ∑ j ∈ s, g j := by
  refine sum_le_sum fun j _ => ?_
  exact h j

/-! ### R23. `abs_mul` · `|a * b| = |a| * |b|` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (|a| * |b|)) : P |a * b| := by
  rw [abs_mul]
  exact h

/-! ### R24. `gcongr` · goal `x * u ≤ x * w` → `u ≤ w` (same shape both sides; `0 ≤ x` found itself)
It closes the new goal on its own when that goal is a hypothesis. -/
example (a u : ℝ) : |a| * u ≤ |a| * |u| := by
  gcongr
  exact le_abs_self u

/-! ### R25. `norm_le_pi_norm` · `‖v j‖ ≤ ‖v‖`: one coordinate is at most the sup norm -/
example {n : ℕ} (v : Fin n → ℝ) (j : Fin n) : ‖v j‖ ≤ ‖v‖ := by
  exact norm_le_pi_norm v j

/-! ### R26. `simpa [l] using e` · simplifies both `e`'s type and the goal, then closes the goal with `e` -/
example {n : ℕ} (u w : Fin n → ℝ) (j : Fin n) (r : ℝ) (h : ‖(u - w) j‖ ≤ r) : |u j - w j| ≤ r := by
  simpa [Real.norm_eq_abs] using h

/-! ### R27. `Finset.sum_mul` · `(∑ i ∈ s, f i) * c = ∑ i ∈ s, f i * c` · goal -/
example {ι : Type} (s : Finset ι) (f : ι → ℝ) (c : ℝ) (P : ℝ → Prop) (h : P (∑ i ∈ s, f i * c)) :
    P ((∑ i ∈ s, f i) * c) := by
  rw [sum_mul]
  exact h

/-! ## Part 3 · Error after `k` sweeps (`jacobi_error`) -/

/-! ### R28. `induction k with | zero => ?_ | succ k ih => ?_` · goal list: base case and step -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ k, P k → P (k + 1)) (k : ℕ) : P k := by
  induction k with | zero => ?_ | succ k ih => ?_
  exacts [h0, hs k ih]

/-! ### R29. `Function.iterate_zero_apply` · `f^[0] x = x` · goal (`simp` applies it by itself) -/
example {α : Type} (f : α → α) (x : α) (P : α → Prop) (h : P x) : P (f^[0] x) := by
  rw [Function.iterate_zero_apply]
  exact h

/-! ### R30. `Function.iterate_succ_apply'` · `f^[k + 1] x = f (f^[k] x)` · goal: peel off the last step -/
example {α : Type} (f : α → α) (x : α) (k : ℕ) (P : α → Prop) (h : P (f (f^[k] x))) :
    P (f^[k + 1] x) := by
  rw [Function.iterate_succ_apply']
  exact h

/-! ### R31. `conv_lhs => rw [← hp]` · goal: rewrite only the left side of `≤` / `=`
With `hp : f p = p`, it turns the `p` on the left into `f p`; a plain `rw [← hp]` would change every `p`. -/
example {α : Type} (f : α → α) (p y : α) (hp : f p = p) (d : α → α → ℝ) (c : ℝ)
    (h : d (f y) (f p) ≤ c * d y p) : d (f y) p ≤ c * d y p := by
  conv_lhs => rw [← hp]
  exact h

/-! ## Part 4 · Convergence (`jacobi_tendsto`) -/

/-! ### R32. `tendsto_iff_norm_sub_tendsto_zero` · goal: `u k → L` ↔ `‖u k - L‖ → 0` -/
example {n : ℕ} (u : ℕ → Fin n → ℝ) (L : Fin n → ℝ)
    (h : Tendsto (fun k => ‖u k - L‖) atTop (𝓝 0)) : Tendsto u atTop (𝓝 L) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact h

/-! ### R33. `tendsto_pow_atTop_nhds_zero_of_lt_one` · `0 ≤ r → r < 1 → rᵏ → 0` · context, with `have` -/
example (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) (Q : Prop)
    (hQ : Tendsto (fun k : ℕ => r ^ k) atTop (𝓝 0) → Q) : Q := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  exact hQ h

/-! ### R34. `Tendsto.mul_const` · `u k → a` gives `u k * c → a * c` · context, with `have` -/
example (u : ℕ → ℝ) (c : ℝ) (Q : Prop) (h : Tendsto u atTop (𝓝 0))
    (hQ : Tendsto (fun k => u k * c) atTop (𝓝 (0 * c)) → Q) : Q := by
  have h' := h.mul_const c
  exact hQ h'

/-! ### R35. `zero_mul` · `0 * a = 0` · context, with `rw … at h`; `simpa using h` does the same -/
example (u : ℕ → ℝ) (c : ℝ) (h : Tendsto u atTop (𝓝 (0 * c))) : Tendsto u atTop (𝓝 0) := by
  rw [zero_mul] at h
  exact h

/-! ### R36. `squeeze_zero` · `0 ≤ f ≤ g` pointwise and `g → 0` give `f → 0` · goal list: two side goals -/
example (f g : ℕ → ℝ) (h0 : ∀ k, 0 ≤ f k) (hle : ∀ k, f k ≤ g k) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  refine squeeze_zero ?_ ?_ hg
  exacts [h0, hle]

/-! ### R37. `norm_nonneg` · `0 ≤ ‖v‖` · closes the goal -/
example {n : ℕ} (v : Fin n → ℝ) : 0 ≤ ‖v‖ := by
  exact norm_nonneg v

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Split one term off a full sum and solve for it: R3-style hypothesis, R4 with R5, R7 -/
example {n : ℕ} (w : Fin n → ℝ) (i : Fin n) (h : ∑ j, w j = 1) :
    w i = 1 - ∑ j ∈ univ.erase i, w j := by
  rw [← add_sum_erase _ _ (mem_univ i)] at h
  linarith

/-! ### W2. A coordinatewise map is a contraction in the sup norm: R8, R9, R11, R12, R13, R14, R15, R25 -/
noncomputable def half {n : ℕ} (u : Fin n → ℝ) : Fin n → ℝ := fun i => u i / 2

example {n : ℕ} (u w : Fin n → ℝ) : ‖half u - half w‖ ≤ 1 / 2 * ‖u - w‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  simp only [Pi.sub_apply, half, Real.norm_eq_abs]
  rw [← sub_div, abs_div, div_le_iff₀ (by norm_num)]
  have hi : |u i - w i| ≤ ‖u - w‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm (u - w) i
  rw [abs_two]
  linarith

/-! ### W3. Error of a scalar iteration with fixed point 2: R28, R29, R30, R31, R19, R24 -/
/-- the scalar map `q x = x / 2 + 1`; its fixed point is `2` -/
noncomputable def q (x : ℝ) : ℝ := x / 2 + 1

theorem q_contract (x y : ℝ) : |q x - q y| ≤ 1 / 2 * |x - y| := by
  have e : q x - q y = (x - y) / 2 := by simp only [q]; ring
  rw [e, abs_div, abs_two]
  linarith

theorem q_error (a : ℝ) (k : ℕ) : |q^[k] a - 2| ≤ (1 / 2) ^ k * |a - 2| := by
  induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      have hfix : q 2 = 2 := by norm_num [q]
      conv_lhs => rw [← hfix]
      calc _ ≤ 1 / 2 * |q^[k] a - 2| := q_contract _ _
        _ ≤ 1 / 2 * ((1 / 2) ^ k * |a - 2|) := by gcongr
        _ = (1 / 2) ^ (k + 1) * |a - 2| := by ring

/-! ### W4. Pass to the limit: R32, R33, R34, R35, R36, R37 -/
example (a : ℝ) : Tendsto (fun k => q^[k] a) atTop (𝓝 2) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k * |a - 2|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_const |a - 2|
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) h0
  rw [Real.norm_eq_abs]
  exact q_error a k

end H071Guide
