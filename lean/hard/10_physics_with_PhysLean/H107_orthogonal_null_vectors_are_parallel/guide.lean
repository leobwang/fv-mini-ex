/- Guide for H107 (Orthogonal null vectors are parallel).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Entries that change a hypothesis or build a fact use `G : Prop` for an arbitrary goal and a
hypothesis `g : … → G` that only closes the example, so you can read off what the context gained.
Part W: worked combinations on objects that are NOT the exercise's (plain vectors of `ℝ³`).
Assumed: Lean basics (E001–E033).
-/
import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct

open Lorentz Vector

namespace H107Guide

/-! # Part R · Reference entries -/

/-! ## Proving `≠`, and 4-vectors by components -/

/-! ### R1. `intro h0` on a goal `a ≠ b` · goal `a ≠ b` → `False`; context gains `h0 : a = b`
`a ≠ b` is notation for `a = b → False`, so `intro` works on it like on any implication. -/
example {α : Type} (a b : α) (g : a = b → False) : a ≠ b := by
  intro h0
  exact g h0

/-! ### R2. `minkowskiProduct_self_eq_timeComponent_spatialPart` · `⟪p, p⟫ₘ = ‖p⁰‖ ^ 2 - ‖p⃗‖ ^ 2`
Used as `rw [...] at h`: it rewrites the hypothesis `h`, not the goal. -/
example {d : ℕ} (p : Lorentz.Vector d) (h : ⟪p, p⟫ₘ = 0) (G : Prop)
    (g : ‖p.timeComponent‖ ^ 2 - ‖p.spatialPart‖ ^ 2 = 0 → G) : G := by
  rw [minkowskiProduct_self_eq_timeComponent_spatialPart] at h
  exact g h

/-! ### R3. `simp at h` on `‖0‖ ^ 2 - ‖p⃗‖ ^ 2 = 0` · context: `h` becomes "the spatial part is zero"
`simp` uses `norm_zero`, `zero_pow`, `zero_sub`, `neg_eq_zero`, `pow_eq_zero_iff`, `norm_eq_zero`, and
`WithLp.toLp_eq_zero`. `p.spatialPart` is by definition `WithLp.toLp 2 (fun i => p (Sum.inr i))`, so the
result is the plain function `fun i => p (Sum.inr i)` equal to `0`. -/
example {d : ℕ} (p : Lorentz.Vector d) (h : ‖(0 : ℝ)‖ ^ 2 - ‖p.spatialPart‖ ^ 2 = 0) (G : Prop)
    (g : (fun i => p (Sum.inr i)) = 0 → G) : G := by
  simp at h
  exact g h

/-! ### R4. `apply hne` with `hne : a ≠ b` · goal `False` → `a = b`
`hne : a = b → False` ends in `False`, so `apply` leaves its premise as the new goal. -/
example {α : Type} (a b : α) (hne : a ≠ b) (h : a = b) : False := by
  apply hne
  exact h

/-! ### R5. `funext μ` · goal `p = q` between 4-vectors → `p μ = q μ`; context gains the index `μ`
`Lorentz.Vector d` is the function type `Fin 1 ⊕ Fin d → ℝ`, so function extensionality applies. -/
example {d : ℕ} (p q : Lorentz.Vector d) (h : ∀ μ, p μ = q μ) : p = q := by
  funext μ
  exact h μ

/-! ### R6. `match μ with | Sum.inl 0 => … | Sum.inr i => …` · goal list: one goal per kind of index
`Fin 1 ⊕ Fin d` has the time index `Sum.inl 0` (the only element of `Fin 1`) and the space indices
`Sum.inr i`, `i : Fin d`. Each arm is a tactic block for one goal. -/
example {d : ℕ} (P : Fin 1 ⊕ Fin d → Prop) (h0 : P (Sum.inl 0)) (h1 : ∀ i, P (Sum.inr i))
    (μ : Fin 1 ⊕ Fin d) : P μ := by
  match μ with
    | Sum.inl 0 => exact h0
    | Sum.inr i => exact h1 i

/-- The same split written `refine match … ?_`, so that both arm goals appear in the infoview. -/
example {d : ℕ} (P : Fin 1 ⊕ Fin d → Prop) (h0 : P (Sum.inl 0)) (h1 : ∀ i, P (Sum.inr i))
    (μ : Fin 1 ⊕ Fin d) : P μ := by
  refine match μ with
    | Sum.inl 0 => ?_
    | Sum.inr i => ?_
  exact h0
  exact h1 i

/-! ### R7. `timeComponent` unfolds by definition · `p (Sum.inl 0)` *is* `p.timeComponent`
So `exact h0` with `h0 : … p.timeComponent …` closes a goal written with `p (Sum.inl 0)`. -/
example {d : ℕ} (p : Lorentz.Vector d) (P : ℝ → Prop) (h0 : P p.timeComponent) :
    P (p (Sum.inl 0)) := by
  exact h0

/-! ### R8. `congrArg (· i) hs` · context gains the `i`-th component of an equation of vectors
`congrArg f : a = b → f a = f b`; `(· i)` is the function `fun x => x i`. For `x : EuclideanSpace ℝ (Fin d)`,
`x i` is printed `x.ofLp i` (`ofLp` turns the vector back into a function `Fin d → ℝ`). -/
example {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) (i : Fin d) (hs : x = y) (G : Prop)
    (g : x.ofLp i = y.ofLp i → G) : G := by
  have h' := congrArg (· i) hs
  exact g h'

/-- `p.spatialPart.ofLp i` *is* `p (Sum.inr i)` by definition, so `exact` accepts one for the other. -/
example {d : ℕ} (p : Lorentz.Vector d) (i : Fin d) (P : ℝ → Prop) (h : P (p.spatialPart.ofLp i)) :
    P (p (Sum.inr i)) := by
  exact h

/-! ## The Minkowski product in components, norms and inner products -/

/-! ### R9. `minkowskiProduct_eq_timeComponent_spatialPart` · `⟪p, q⟫ₘ = p⁰ * q⁰ - inner ℝ p⃗ q⃗` -/
example {d : ℕ} (p q : Lorentz.Vector d) (h : ⟪p, q⟫ₘ = 0) (G : Prop)
    (g : p.timeComponent * q.timeComponent - inner ℝ p.spatialPart q.spatialPart = 0 → G) : G := by
  rw [minkowskiProduct_eq_timeComponent_spatialPart] at h
  exact g h

/-! ### R10. `Real.norm_eq_abs`, `sq_abs` · goal: `‖x‖ ^ 2` → `|x| ^ 2` → `x ^ 2` for a real `x` -/
example (x : ℝ) (P : ℝ → Prop) (h : P (x ^ 2)) : P (‖x‖ ^ 2) := by
  rw [Real.norm_eq_abs]
  rw [sq_abs]
  exact h

/-! ### R11. `norm_sub_sq_real` · `‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2` -/
example {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) (P : ℝ → Prop)
    (h : P (‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2)) : P (‖x - y‖ ^ 2) := by
  rw [norm_sub_sq_real]
  exact h

/-! ### R12. `norm_smul` · `‖r • x‖ = ‖r‖ * ‖x‖` -/
example {d : ℕ} (r : ℝ) (x : EuclideanSpace ℝ (Fin d)) (P : ℝ → Prop) (h : P (‖r‖ * ‖x‖)) :
    P ‖r • x‖ := by
  rw [norm_smul]
  exact h

/-! ### R13. `real_inner_smul_left` · `inner ℝ (r • x) y = r * inner ℝ x y` -/
example {d : ℕ} (r : ℝ) (x y : EuclideanSpace ℝ (Fin d)) (P : ℝ → Prop)
    (h : P (r * inner ℝ x y)) : P (inner ℝ (r • x) y) := by
  rw [real_inner_smul_left]
  exact h

/-! ### R14. `real_inner_smul_right` · `inner ℝ x (r • y) = r * inner ℝ x y` -/
example {d : ℕ} (r : ℝ) (x y : EuclideanSpace ℝ (Fin d)) (P : ℝ → Prop)
    (h : P (r * inner ℝ x y)) : P (inner ℝ x (r • y)) := by
  rw [real_inner_smul_right]
  exact h

/-! ### R15. `mul_pow` · `(a * b) ^ n = a ^ n * b ^ n` -/
example (a b : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (a ^ n * b ^ n)) : P ((a * b) ^ n) := by
  rw [mul_pow]
  exact h

/-! ## Arithmetic over `ℝ` -/

/-! ### R16. `linarith` · closes a goal that follows linearly from the hypotheses
Products such as `y * z` count as one unknown. -/
example (x y z : ℝ) (h : x - y * z = 0) : y * z = x := by
  linarith

/-! ### R17. `nlinarith` · closes a polynomial (in)equality; also multiplies hypotheses in pairs -/
example (a b u v : ℝ) (hu : u = a ^ 2) (hv : v = b ^ 2) :
    a ^ 2 * v + b ^ 2 * u - 2 * u * v = 0 := by
  nlinarith

/-! ## From a zero length to an equation -/

/-! ### R18. `sq_eq_zero_iff` · `a ^ 2 = 0 ↔ a = 0` -/
example (a : ℝ) (h : a ^ 2 = 0) (G : Prop) (g : a = 0 → G) : G := by
  rw [sq_eq_zero_iff] at h
  exact g h

/-! ### R19. `norm_eq_zero` · `‖x‖ = 0 ↔ x = 0` -/
example {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (h : ‖x‖ = 0) (G : Prop) (g : x = 0 → G) : G := by
  rw [norm_eq_zero] at h
  exact g h

/-! ### R20. `sub_eq_zero` · `a - b = 0 ↔ a = b` -/
example {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) (h : x - y = 0) (G : Prop) (g : x = y → G) :
    G := by
  rw [sub_eq_zero] at h
  exact g h

/-! ## Choosing the witness and splitting into time and space -/

/-! ### R21. `refine ⟨r, f _ _ ?_ ?_⟩` · goal `∃ t, …` → the premises of a lemma `f`
The witness `r` is given now; `f`'s explicit arguments `_` are found by unification with the goal,
and each `?_` becomes a new goal. -/
example {α : Type} (A B : α → α → Prop) (f : ∀ u v, A u v → B u v → u = v) (p : α) (s : ℝ → α)
    (r : ℝ) (ha : A p (s r)) (hb : B p (s r)) : ∃ t : ℝ, p = s t := by
  refine ⟨r, f _ _ ?_ ?_⟩
  exact ha
  exact hb

/-! ### R22. `change` · goal replaced by a definitionally equal one
`(r • q).timeComponent` *is* `r * q.timeComponent`, and `(r • q).spatialPart` *is* `r • q.spatialPart`,
by unfolding definitions; `change` writes the goal in the form you want to rewrite. -/
example {d : ℕ} (p q : Lorentz.Vector d) (r : ℝ) (h : p.timeComponent = r * q.timeComponent) :
    p.timeComponent = (r • q).timeComponent := by
  change p.timeComponent = r * q.timeComponent
  exact h

example {d : ℕ} (q : Lorentz.Vector d) (r : ℝ) (P : EuclideanSpace ℝ (Fin d) → Prop)
    (h : P (r • q.spatialPart)) : P (r • q).spatialPart := by
  change P (r • q.spatialPart)
  exact h

/-! ### R23. `field_simp` · clears denominators using the `b ≠ 0` facts in the context; often closes the goal -/
example (a b : ℝ) (hb : b ≠ 0) : a = a / b * b := by
  field_simp

/-! ### R24. `div_eq_inv_mul` · `a / b = b⁻¹ * a` -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (b⁻¹ * a)) : P (a / b) := by
  rw [div_eq_inv_mul]
  exact h

/-! ### R25. `smul_smul` · `a • b • x = (a * b) • x`; right to left: `rw [← smul_smul]` splits a product
Bare `mul_smul` (the same lemma the other way round) is ambiguous after `open Lorentz Vector`. -/
example {d : ℕ} (a b : ℝ) (x : EuclideanSpace ℝ (Fin d)) (P : EuclideanSpace ℝ (Fin d) → Prop)
    (h : P (a • b • x)) : P ((a * b) • x) := by
  rw [← smul_smul]
  exact h

example {d : ℕ} (a b : ℝ) (x : EuclideanSpace ℝ (Fin d)) (P : EuclideanSpace ℝ (Fin d) → Prop)
    (h : P ((a * b) • x)) : P (a • b • x) := by
  rw [smul_smul]
  exact h

/-! ### R26. `inv_mul_cancel₀` · `b ≠ 0 → b⁻¹ * b = 1` -/
example (b : ℝ) (hb : b ≠ 0) (P : ℝ → Prop) (h : P 1) : P (b⁻¹ * b) := by
  rw [inv_mul_cancel₀ hb]
  exact h

/-! ### R27. `one_smul` · `1 • x = x` -/
example {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (P : EuclideanSpace ℝ (Fin d) → Prop) (h : P x) :
    P ((1 : ℝ) • x) := by
  rw [one_smul]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Length of a difference from the three numbers `‖x‖², ‖y‖², ⟪x, y⟫`: R11, then `rw` and `norm_num` -/
example (x y : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ ^ 2 = 1) (hy : ‖y‖ ^ 2 = 1)
    (hxy : inner ℝ x y = 1) : ‖x - y‖ ^ 2 = 0 := by
  rw [norm_sub_sq_real]
  rw [hx, hy, hxy]
  norm_num

/-! ### W2. Dividing an equation of vectors by a nonzero scalar: R25 ←, `rw [← h]`, R25, R26, R27 -/
example (x y : EuclideanSpace ℝ (Fin 3)) (h : (2 : ℝ) • x = (6 : ℝ) • y) : x = (3 : ℝ) • y := by
  rw [show (3 : ℝ) = 2⁻¹ * 6 by norm_num]
  rw [← smul_smul]
  rw [← h]
  rw [smul_smul]
  rw [inv_mul_cancel₀ (by norm_num)]
  rw [one_smul]

end H107Guide
