/- Guide for M120 (Gershgorin discs for a symmetric matrix).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal" and `Q` for "the rest of a hypothesis": the step changes only
the part shown inside `P (…)` / `Q (…)`. `G` is a goal the step leaves alone. A hypothesis `h` in an
entry is only there to finish the example; it shows what the goal (or hypothesis) became.
Part W: worked combinations on a matrix that is NOT the exercise's.
Assumed: Lean basics.
-/
import Mathlib

namespace M120Guide

/-! # Part R · Reference entries -/

/-! ## From the eigenvalue to one inequality -/

/-! ### R1. `obtain ⟨k, hk⟩ := eigenvalue_mem_ball hμ` · context: gains a row `k` and its disc `hk`
Gershgorin: an eigenvalue lies in the disc of some row `k`. -/
example {K : Type} [NormedField K] {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n K) (μ : K)
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' M) μ) (G : Prop)
    (h : ∀ k, μ ∈ Metric.closedBall (M k k) (∑ j ∈ Finset.univ.erase k, ‖M k j‖) → G) : G := by
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hμ
  exact h k hk

/-! ### R2. `Metric.mem_closedBall` · context: `x ∈ closedBall c r` → `dist x c ≤ r` -/
example {α : Type} [PseudoMetricSpace α] (x c : α) (r : ℝ) (G : Prop)
    (hx : x ∈ Metric.closedBall c r) (h : dist x c ≤ r → G) : G := by
  rw [Metric.mem_closedBall] at hx
  exact h hx

/-! ### R3. `Real.dist_eq` · context: `dist x y` → `|x - y|` on `ℝ` -/
example (x y r : ℝ) (G : Prop) (hx : dist x y ≤ r) (h : |x - y| ≤ r → G) : G := by
  rw [Real.dist_eq] at hx
  exact h hx

/-! ## One case per row -/

/-! ### R4. `fin_cases k` · goal list: one goal per value of `k : Fin 3`; `k` is replaced everywhere,
in the goal and in hypotheses such as `hk : Q k`. `(fun i => i) ⟨0, ⋯⟩` is how Lean prints `0`. -/
example (P Q : Fin 3 → Prop) (k : Fin 3) (hk : Q k) (h : ∀ i, Q i → P i) : P k := by
  fin_cases k
  all_goals exact h _ hk

/-! ## Evaluating the disc of one row -/

/-! ### R5. `simp [D]` · goal: unfold the name `D`, then evaluate entries of `!![…]`
`D 2 2` becomes a number; `D 0 j` with `j` unknown becomes the row vector `![…] j`.
`simp [D] at hk` does the same to a hypothesis. -/
def D : Matrix (Fin 3) (Fin 3) ℝ := !![2, 0, 1; 0, 3, 0; 1, 0, 7]
example (P : ℝ → ℝ → Prop) (j : Fin 3) (h : P 7 (![2, 0, 1] j)) : P (D 2 2) (D 0 j) := by
  simp [D]
  exact h

/-! ### R6. `Real.norm_eq_abs` · context: `‖r‖` → `|r|` on `ℝ` (`simp` applies it by itself) -/
example (r : ℝ) (Q : ℝ → Prop) (G : Prop) (hk : Q ‖r‖) (h : Q |r| → G) : G := by
  rw [Real.norm_eq_abs] at hk
  exact h hk

/-! ### R7. `Finset.sum_erase_eq_sub` · goal: sum without one term → full sum minus that term
Side condition `a ∈ s`; for `s = Finset.univ` it is `Finset.mem_univ a` (`simp` does all this itself). -/
example {β : Type} [AddCommGroup β] (f : Fin 3 → β) (a : Fin 3) (P : β → Prop)
    (h : P (∑ x, f x - f a)) : P (∑ x ∈ Finset.univ.erase a, f x) := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ a)]
  exact h

/-! ### R8. `Fin.sum_univ_succ` · goal: peel the first term off a sum over `Fin (n + 1)`
`rw` peels one term; `simp [Fin.sum_univ_succ]` peels them all. You must name it: `simp` does not. -/
example {β : Type} [AddCommMonoid β] (f : Fin 3 → β) (P : β → Prop) (h : P (f 0 + (f 1 + f 2))) :
    P (∑ x, f x) := by
  rw [Fin.sum_univ_succ]
  simp [Fin.sum_univ_succ]
  exact h

/-! ## From `|·| ≤ ·` to the two bounds -/

/-! ### R9. `abs_le` · context: `abs_le.mp hab` turns `hab : |a| ≤ b` into `-b ≤ a ∧ a ≤ b`
The lemma is `abs_le : |a| ≤ b ↔ -b ≤ a ∧ a ≤ b`; `.mp` uses it left to right. -/
example {α : Type} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (a b : α) (G : Prop)
    (hab : |a| ≤ b) (h : -b ≤ a ∧ a ≤ b → G) : G := by
  have h' := abs_le.mp hab
  exact h h'

/-! ### R10. `linarith [e]` · closes a linear inequality from the hypotheses plus the extra fact `e`
`e` may be a conjunction; `linarith` uses both halves. It treats `|a - b|` as an unknown. -/
example (a b c : ℝ) (hab : |a - b| ≤ c) : b - c ≤ a := by
  linarith [abs_le.mp hab]

/-! # Part W · Worked combinations (the matrix `D` of R5, not the exercise's) -/

/-! ### W1. One row's disc as an explicit inequality: R2, R3, then `simp` with R5–R8
Here the disc is the goal; at a hypothesis `hk` write the same steps with `at hk`. -/
example (μ : ℝ) (h : |μ - 2| ≤ 1) :
    μ ∈ Metric.closedBall (D 0 0) (∑ j ∈ Finset.univ.erase 0, ‖D 0 j‖) := by
  rw [Metric.mem_closedBall, Real.dist_eq]
  simp [D, Fin.sum_univ_succ]
  exact h

/-! ### W2. From the disc `|μ - 2| ≤ 1` to the interval `[1, 3]`: `constructor`, then R9 → R10 -/
example (μ : ℝ) (h : |μ - 2| ≤ 1) : 1 ≤ μ ∧ μ ≤ 3 := by
  constructor
  all_goals linarith [abs_le.mp h]

end M120Guide
