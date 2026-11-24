/- Guide for M180 (⟪u, v⟫ₘ = 1 forces equal 4-velocities).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal" (or of a hypothesis): the step changes only the part shown
inside `P (…)`. A hypothesis `k` or `h` in an entry is only there to finish the example; it shows what
the goal or hypothesis became.
Part W: worked combinations on objects that are NOT the exercise's (`u + v`, `ℝ³` vectors, `w = v`).
Assumed: Lean basics (E001–E033).
-/
import Physlib.Relativity.Tensors.RealTensor.Velocity.Basic

open Lorentz Vector

namespace M180Guide

/-! # Part R · Reference entries -/

/-! ## Minkowski product → time and space parts (Part 1) -/

/-! ### R1. `minkowskiProduct_self_eq_timeComponent_spatialPart` · context: `⟪p, p⟫ₘ` in `h` → `‖p⁰‖ ^ 2 - ‖p⃗‖ ^ 2`
`⟪p, q⟫ₘ` prints as `(minkowskiProduct p) q`. -/
example {d : ℕ} (p : Lorentz.Vector d) (P : ℝ → Prop) (G : Prop) (h : P ⟪p, p⟫ₘ)
    (k : P (‖p.timeComponent‖ ^ 2 - ‖p.spatialPart‖ ^ 2) → G) : G := by
  rw [minkowskiProduct_self_eq_timeComponent_spatialPart] at h
  exact k h

/-! ### R2. `minkowskiProduct_eq_timeComponent_spatialPart` · context: `⟪p, q⟫ₘ` in `h` → `p⁰ * q⁰ - inner ℝ p⃗ q⃗` -/
example {d : ℕ} (p q : Lorentz.Vector d) (P : ℝ → Prop) (G : Prop) (h : P ⟪p, q⟫ₘ)
    (k : P (p.timeComponent * q.timeComponent - inner ℝ p.spatialPart q.spatialPart) → G) : G := by
  rw [minkowskiProduct_eq_timeComponent_spatialPart] at h
  exact k h

/-! ### R3. `Real.norm_eq_abs`, `sq_abs` · context: `‖a‖ ^ 2` (norm of a real) → `|a| ^ 2` → `a ^ 2` -/
example (a : ℝ) (P : ℝ → Prop) (G : Prop) (h : P (‖a‖ ^ 2)) (k : P (a ^ 2) → G) : G := by
  rw [Real.norm_eq_abs] at h
  rw [sq_abs] at h
  exact k h

/-! ## Cauchy–Schwarz and squaring (Part 1) -/

/-! ### R4. `abs_real_inner_le_norm` · context gains `|inner ℝ x y| ≤ ‖x‖ * ‖y‖` (Cauchy–Schwarz) -/
example {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) (G : Prop) (k : |inner ℝ x y| ≤ ‖x‖ * ‖y‖ → G) :
    G := by
  have hcs := abs_real_inner_le_norm x y
  exact k hcs

/-! ### R5. `by_contra h0` · goal `G` → `False`; context gains `h0 : ¬G` -/
example (a : ℝ) (k : ¬a = 0 → False) : a = 0 := by
  by_contra h0
  exact k h0

/-! ### R6. `positivity` · closes `0 < e` / `0 ≤ e` by the shape of `e`; uses `a ≠ 0` from the context -/
example (a : ℝ) (h0 : ¬a = 0) : 0 < a ^ 2 := by
  positivity

/-! ### R7. `linarith` · closes a linear (in)equality that follows from linear hypotheses -/
example (a b c : ℝ) (h1 : a - b = c) (h2 : c = 0) : a = b := by
  linarith

/-! ### R8. `rw [show a = b by tac]` · goal: `a` → `b`, with the equation proved on the spot -/
example (a b c : ℝ) (h1 : a - b = c) (h2 : c = 0) (P : ℝ → Prop) (k : P b) : P a := by
  rw [show a = b by linarith]
  exact k

/-! ### R9. `abs_le` · `|a| ≤ b ↔ -b ≤ a ∧ a ≤ b`; `.mp` turns a hypothesis into the pair -/
example (a b : ℝ) (h : |a| ≤ b) (G : Prop) (k : -b ≤ a ∧ a ≤ b → G) : G := by
  have h2 := abs_le.mp h
  exact k h2

/-! ### R10. `sq_le_sq'` · `-b ≤ a → a ≤ b → a ^ 2 ≤ b ^ 2`; with `apply`, goal → two goals -/
example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  apply sq_le_sq'
  exact h1
  exact h2

/-! ### R11. `nlinarith` · like `linarith`, but also multiplies pairs of hypotheses first -/
example (a b c : ℝ) (hc : 0 < c) (hab : a < b) : a * c < b * c := by
  nlinarith

/-! ## From `‖w⃗‖ = 0` and `w⁰ = 0` back to `w = 0` (Part 1) -/

/-! ### R12. `simp at h` on `‖x‖ ^ 2 = 0` · context: `h` → `x = 0` (`pow_eq_zero_iff`, `norm_eq_zero`)
`simpa using h` does this and closes the goal with the result. -/
example {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (h : ‖x‖ ^ 2 = 0) : x = 0 := by
  simp at h
  exact h

/-! When `x` is `w.spatialPart`, `simp` also unfolds it to `fun i => w (Sum.inr i)`, in `h` and in the
goal alike, so `exact h` only works after a `simp` on the goal too. `simpa using h` does both. -/
example {d : ℕ} (w : Lorentz.Vector d) (h : ‖w.spatialPart‖ ^ 2 = 0) : w.spatialPart = 0 := by
  simp at h
  simp
  exact h

/-! ### R13. `funext μ` · goal `w = v` (4-vectors are functions) → one component `w μ = v μ` -/
example {d : ℕ} (w : Lorentz.Vector d) (k : ∀ μ, w μ = (0 : Lorentz.Vector d) μ) : w = 0 := by
  funext μ
  exact k μ

/-! ### R14. `match μ with | Sum.inl 0 => … | Sum.inr i => …` · goal list: time component, space components
Written here as `refine match …` so both goals are visible at once; the tactic `match μ with` puts the
same goals inside its two branches. -/
example {d : ℕ} (P : Fin 1 ⊕ Fin d → Prop) (h0 : P (Sum.inl 0)) (h1 : ∀ i, P (Sum.inr i))
    (μ : Fin 1 ⊕ Fin d) : P μ := by
  refine match μ with
    | Sum.inl 0 => ?_
    | Sum.inr i => ?_
  exact h0
  exact h1 i

/-! ### R15. `congrArg (fun v => v i) hs` · context gains the `i`-th coordinate of an equation `hs : x = y`
On `EuclideanSpace` the coordinate prints as `x.ofLp i` (`ofLp` unwraps the `WithLp` wrapper). -/
example {d : ℕ} (w : Lorentz.Vector d) (hs : w.spatialPart = 0) (i : Fin d) (G : Prop)
    (k : w.spatialPart.ofLp i = WithLp.ofLp (0 : EuclideanSpace ℝ (Fin d)) i → G) : G := by
  have h := congrArg (fun v => v i) hs
  exact k h

/-! ### R16. `simp` on coordinates · `w⃗.ofLp i` → `w (Sum.inr i)`, `0 μ` → `0`
`simpa using h` runs `simp` on both `h` and the goal, then closes the goal with `h`. -/
example {d : ℕ} (w : Lorentz.Vector d) (i : Fin d) (h : w.spatialPart.ofLp i = WithLp.ofLp (0 : EuclideanSpace ℝ (Fin d)) i) :
    w (Sum.inr i) = (0 : Lorentz.Vector d) (Sum.inr i) := by
  simp at h
  simp
  exact h

/-! ## The main theorem (Part 2) -/

/-! ### R17. `have hq := L a (by tac)` · context gains a lemma's conclusion; `(by tac)` proves its hypotheses -/
example (Q : ℝ → Prop) (L : ∀ x : ℝ, 0 < x → Q x) : Q 1 := by
  have hq := L 1 (by norm_num)
  exact hq

/-! ### R18. `Velocity.minkowskiProduct_self_eq_one` · goal: `⟪u.1, u.1⟫ₘ` → `1` (a `simp` lemma)
`u : Velocity d` prints as `u : ↑(Velocity d)` and `u.1` as `↑u`. -/
example {d : ℕ} (u : Velocity d) (P : ℝ → Prop) (k : P 1) : P ⟪u.1, u.1⟫ₘ := by
  simp only [Velocity.minkowskiProduct_self_eq_one]
  exact k

/-! ### R19. `map_sub`, `sub_apply` · goal: `⟪p - q, r⟫ₘ` → `⟪p, r⟫ₘ - ⟪q, r⟫ₘ`, and in the right slot -/
example {d : ℕ} (p q r : Lorentz.Vector d) (P : ℝ → Prop) (k : P (⟪p, r⟫ₘ - ⟪q, r⟫ₘ)) :
    P ⟪p - q, r⟫ₘ := by
  rw [map_sub]
  rw [sub_apply]
  exact k

example {d : ℕ} (p q r : Lorentz.Vector d) (P : ℝ → Prop) (k : P (⟪r, p⟫ₘ - ⟪r, q⟫ₘ)) :
    P ⟪r, p - q⟫ₘ := by
  rw [map_sub]
  exact k

/-! ### R20. `minkowskiProduct_symm` · `⟪p, q⟫ₘ = ⟪q, p⟫ₘ` · goal: swap the arguments
Give the arguments (`minkowskiProduct_symm q p`) so `simp` rewrites only that one product. -/
example {d : ℕ} (p q : Lorentz.Vector d) (P : ℝ → Prop) (k : P ⟪q, p⟫ₘ) : P ⟪p, q⟫ₘ := by
  rw [minkowskiProduct_symm]
  exact k

/-! ### R21. `ext1` (lemma `Velocity.ext`) · goal `u = v` on velocities → `↑u = ↑v` on vectors -/
example {d : ℕ} (u v : Velocity d) (k : u.1 = v.1) : u = v := by
  ext1
  exact k

/-! ### R22. `sub_eq_zero` · `a - b = 0 ↔ a = b`; `.mp` uses it left to right, `rw [← sub_eq_zero]` on a goal -/
example {α : Type} [AddGroup α] (a b : α) (k : a - b = 0) : a = b := by
  rw [← sub_eq_zero]
  exact k

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Expanding a product of sums of velocities: R19 (with `map_add`), R20, R18, then `ring` -/
example {d : ℕ} (u v : Velocity d) : ⟪u.1 + v.1, u.1 + v.1⟫ₘ = 2 + 2 * ⟪u.1, v.1⟫ₘ := by
  simp only [map_add, add_apply]
  rw [minkowskiProduct_symm v.1 u.1]
  simp
  ring

/-! ### W2. Squared Cauchy–Schwarz in ℝ³: R4, R9, R10, then `mul_pow : (a * b) ^ n = a ^ n * b ^ n` -/
example (x y : EuclideanSpace ℝ (Fin 3)) : inner ℝ x y ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have hcs := abs_real_inner_le_norm x y
  have h2 := abs_le.mp hcs
  have h3 := sq_le_sq' h2.1 h2.2
  rw [mul_pow] at h3
  exact h3

/-! ### W3. Two 4-vectors with the same parts are equal: R13, the tactic `match` (R14), R15, R16 -/
example {d : ℕ} (w v : Lorentz.Vector d) (ht : w.timeComponent = v.timeComponent)
    (hs : w.spatialPart = v.spatialPart) : w = v := by
  funext μ
  match μ with
    | Sum.inl 0 => exact ht
    | Sum.inr i => simpa using congrArg (fun x => x i) hs

end M180Guide
