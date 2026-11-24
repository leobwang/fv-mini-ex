/- Guide for H070 (Diagonally dominant ⇒ invertible).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`G : Prop` is an arbitrary goal, finished with `hG`; it exists only so a new hypothesis can be shown.
Vectors are functions `ι → ℝ` on any finite index type `ι` (`[Fintype ι]`); the exercise uses `Fin n`.
Part W: worked combinations on objects that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Matrix Finset

namespace H070Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · One row of a vector equation -/

/-! ### R1. `congrFun h i` · context: from `h : f = g` (functions), get `f i = g i` -/
example {ι β : Type} (f g : ι → β) (i : ι) (h : f = g) (G : Prop) (hG : f i = g i → G) : G := by
  have hi := congrFun h i
  exact hG hi

/-! ### R2. `Matrix.mulVec`, `dotProduct` · goal (or `at h`): `(A *ᵥ v) i` → `∑ j, A i j * v j` -/
example {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (v : ι → ℝ) (i : ι) (P : ℝ → Prop)
    (h : P (∑ j, A i j * v j)) : P ((A *ᵥ v) i) := by
  simp only [mulVec, dotProduct]
  exact h

/-! ### R3. `Pi.zero_apply` · context: `(0 : ι → ℝ) i` (written `0 i`) → `0` -/
example {ι : Type} (x : ℝ) (i : ι) (G : Prop) (h : x = (0 : ι → ℝ) i) (hG : x = 0 → G) : G := by
  simp only [Pi.zero_apply] at h
  exact hG h

/-! ### R4. `Finset.mem_univ` · closes `i ∈ univ`: every element is in the full finite set -/
example {ι : Type} [Fintype ι] (i : ι) : i ∈ (univ : Finset ι) := by
  exact mem_univ i

/-! ### R5. `Finset.add_sum_erase` · `a ∈ s → f a + ∑ x ∈ s.erase a, f x = ∑ x ∈ s, f x`
Right to left (`rw [← …]`, or `rw [← …] at h`) it splits the term `i` off a full sum · goal -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (i : ι) (P : ℝ → Prop)
    (h : P (f i + ∑ j ∈ univ.erase i, f j)) : P (∑ j, f j) := by
  rw [← add_sum_erase _ _ (mem_univ i)]
  exact h

/-! ### R6. `linarith` · closes a linear (in)equality that follows from the hypotheses
Products such as `a * x` and sums `∑ …` count as single unknowns. -/
example (a x s c : ℝ) (h : a * x + s = c) : a * x = c - s := by
  linarith

/-! ## Part 2 · A coordinate of largest absolute value -/

/-! ### R7. `by_contra hc` · goal `Q` → `False`, context gains `hc : ¬Q` -/
example (Q : Prop) (hQ : ¬¬Q) : Q := by
  by_contra hc
  exact hQ hc

/-! ### R8. `Finset.not_nonempty_iff_eq_empty` · `¬s.Nonempty ↔ s = ∅` · context, with `rw … at` -/
example {ι : Type} (s : Finset ι) (G : Prop) (hc : ¬s.Nonempty) (hG : s = ∅ → G) : G := by
  rw [not_nonempty_iff_eq_empty] at hc
  exact hG hc

/-! ### R9. `Finset.univ_eq_empty_iff` · `univ = ∅ ↔ IsEmpty ι` · context, with `rw … at` -/
example {ι : Type} [Fintype ι] (G : Prop) (hc : (univ : Finset ι) = ∅) (hG : IsEmpty ι → G) :
    G := by
  rw [univ_eq_empty_iff] at hc
  exact hG hc

/-! ### R10. `IsEmpty.false`, `False.elim` · an element of an empty type gives `False`, and
`False` proves any goal -/
example {ι : Type} (hc : IsEmpty ι) (i : ι) (Q : Prop) : Q := by
  have hf := hc.false i
  exact hf.elim

/-! ### R11. `funext j` · goal `v = w` (functions) → `v j = w j` for a fresh `j`
Term form: `funext fun j => (proof of v j = w j)`. -/
example {ι : Type} (v : ι → ℝ) (h : ∀ j, v j = 0) : v = 0 := by
  funext j
  exact h j

/-! ### R12. `Finset.exists_max_image` · `s.Nonempty → ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x` · context
`obtain ⟨i, hi, hmax⟩ := …` names the parts; write `-` instead of `hi` to drop a part. -/
example {ι : Type} (s : Finset ι) (f : ι → ℝ) (hs : s.Nonempty) (G : Prop)
    (hG : ∀ i ∈ s, (∀ j ∈ s, f j ≤ f i) → G) : G := by
  obtain ⟨i, hi, hmax⟩ := exists_max_image s f hs
  exact hG i hi hmax

/-! ### R13. `push Not at hc` · context: pushes `¬` inward; `¬0 < a` becomes `a ≤ 0` -/
example (a : ℝ) (G : Prop) (hc : ¬0 < a) (hG : a ≤ 0 → G) : G := by
  push Not at hc
  exact hG hc

/-! ### R14. `abs_nonpos_iff` · `|a| ≤ 0 ↔ a = 0`; `.mp` is the direction `→` · context -/
example (a : ℝ) (h : |a| ≤ 0) (G : Prop) (hG : a = 0 → G) : G := by
  have h0 := abs_nonpos_iff.mp h
  exact hG h0

/-! ### R15. `le_trans`, written `h.trans` · `a ≤ b → b ≤ c → a ≤ c` · goal `a ≤ c` → `b ≤ c` -/
example (a b c : ℝ) (h : a ≤ b) (h' : b ≤ c) : a ≤ c := by
  refine h.trans ?_
  exact h'

/-! ## Part 3 · Bounding one row with the triangle inequality -/

/-! ### R16. `abs_mul` · `|a * b| = |a| * |b|`; right to left: `rw [← abs_mul]` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P |a * b|) : P (|a| * |b|) := by
  rw [← abs_mul]
  exact h

/-! ### R17. `abs_neg` · `|-a| = |a|` · goal -/
example (a : ℝ) (P : ℝ → Prop) (h : P |a|) : P |-a| := by
  rw [abs_neg]
  exact h

/-! ### R18. `Finset.sum_mul` · `(∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a` · goal -/
example {ι : Type} (s : Finset ι) (f : ι → ℝ) (a : ℝ) (P : ℝ → Prop) (h : P (∑ i ∈ s, f i * a)) :
    P ((∑ i ∈ s, f i) * a) := by
  rw [sum_mul]
  exact h

/-! ### R19. `Finset.abs_sum_le_sum_abs` · `|∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i|`, used with R15
· goal `|∑ i ∈ s, f i| ≤ c` → `∑ i ∈ s, |f i| ≤ c` -/
example {ι : Type} (s : Finset ι) (f : ι → ℝ) (c : ℝ) (h : ∑ i ∈ s, |f i| ≤ c) :
    |∑ i ∈ s, f i| ≤ c := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  exact h

/-! ### R20. `Finset.sum_le_sum` · `(∀ i ∈ s, f i ≤ g i) → ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i`
· goal: a sum inequality → one term, with `j` and `hj : j ∈ s` in the context -/
example {ι : Type} (s : Finset ι) (f g : ι → ℝ) (h : ∀ i, f i ≤ g i) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i := by
  refine sum_le_sum fun j hj => ?_
  exact h j

/-! ### R21. `mul_le_mul_of_nonneg_left` · `b ≤ c → 0 ≤ a → a * b ≤ a * c` · goal → two goals -/
example (a b c : ℝ) (hbc : b ≤ c) (ha : 0 ≤ a) : a * b ≤ a * c := by
  refine mul_le_mul_of_nonneg_left ?_ ?_
  exact hbc
  exact ha

/-! ### R22. `abs_nonneg` · `0 ≤ |a|` · closes the goal -/
example (a : ℝ) : 0 ≤ |a| := by
  exact abs_nonneg a

/-! ## Part 4 · The eigenvalue row -/

/-! ### R23. `Pi.smul_apply`, `smul_eq_mul` · `(c • v) i` → `c • v i` → `c * v i` · context -/
example {ι : Type} (c x : ℝ) (v : ι → ℝ) (i : ι) (G : Prop) (h : x = (c • v) i)
    (hG : x = c * v i → G) : G := by
  simp only [Pi.smul_apply] at h
  simp only [smul_eq_mul] at h
  exact hG h

/-! ## Part 5 · Determinant and kernel -/

/-! ### R24. `intro hab` on `a ≠ b` · `a ≠ b` is `a = b → False`: goal → `False`, context gains `a = b` -/
example (a b : ℝ) (h : a = b → False) : a ≠ b := by
  intro hab
  exact h hab

/-! ### R25. `Matrix.exists_mulVec_eq_zero_iff` · `(∃ v, v ≠ 0 ∧ M *ᵥ v = 0) ↔ M.det = 0`
`.mpr` is the direction `←`: a zero determinant gives a nonzero kernel vector · context -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hdet : M.det = 0) (G : Prop)
    (hG : ∀ v : ι → ℝ, v ≠ 0 → M *ᵥ v = 0 → G) : G := by
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact hG v hv hMv

/-! ### R26. `mul_lt_mul_of_pos_right` · `b < c → 0 < a → b * a < c * a` · context -/
example (a b c : ℝ) (h : b < c) (ha : 0 < a) (G : Prop) (hG : b * a < c * a → G) : G := by
  have h2 := mul_lt_mul_of_pos_right h ha
  exact hG h2

/-! ## Part 6 · Cancelling a positive factor -/

/-! ### R27. `le_of_mul_le_mul_right` · `a * c ≤ b * c → 0 < c → a ≤ b`
· goal `a ≤ b` → `a * c ≤ b * c` -/
example (a b c : ℝ) (hc : 0 < c) (h : a * c ≤ b * c) : a ≤ b := by
  refine le_of_mul_le_mul_right ?_ hc
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Row `i` of a linear system `A x = b` (the Jacobi update): R1, R2, R5 with R4, R6 -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (x b : ι → ℝ) (h : A *ᵥ x = b)
    (i : ι) : A i i * x i = b i - ∑ j ∈ univ.erase i, A i j * x j := by
  have hi := congrFun h i
  simp only [mulVec, dotProduct] at hi
  rw [← add_sum_erase _ _ (mem_univ i)] at hi
  linarith

/-! ### W2. A weighted triangle inequality: R18, R19, R20, R16, R21, R22 -/
example {ι : Type} (s : Finset ι) (a x : ι → ℝ) (M : ℝ) (hx : ∀ j, |x j| ≤ M) :
    |∑ j ∈ s, a j * x j| ≤ (∑ j ∈ s, |a j|) * M := by
  rw [sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _)

end H070Guide
