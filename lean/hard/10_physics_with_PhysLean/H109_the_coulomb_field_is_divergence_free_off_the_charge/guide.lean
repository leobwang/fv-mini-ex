/- Guide for H109 (The Coulomb field is divergence free off the charge).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Entries that build a fact (`norm_pos_iff.mpr hx`, `hf.sqrt hx`, …) use `have h := …`, so the
context gains `h` and you can read off exactly what was produced.
Part W: worked combinations on functions that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Physlib.SpaceAndTime.Space.Derivatives.Div

open Space InnerProductSpace

namespace H109Guide

/-! # Part R · Reference entries -/

/-! ## The fact behind everything: `‖x‖ ≠ 0` -/

/-! ### R1. `norm_pos_iff` · `0 < ‖a‖ ↔ a ≠ 0`; `norm_pos_iff.mpr hx` · context gains `0 < ‖a‖` -/
example {E : Type} [NormedAddCommGroup E] (a : E) (hx : a ≠ 0) : 0 < ‖a‖ := by
  have h := norm_pos_iff.mpr hx
  exact h

/-! ### R2. `positivity` · closes a goal `0 < e`, `0 ≤ e` or `e ≠ 0` built from positive pieces
It reads hypotheses `0 < a` from the context. Typical use: a side argument `(by positivity)`. -/
example (r : ℝ) (hr : 0 < r) : r ^ 3 ≠ 0 := by
  positivity

/-! ## Derivatives as facts: `HasFDerivAt`, and turning them into rewrites -/

/-! ### R3. `hasStrictFDerivAt_norm_sq` + `.hasFDerivAt` · context gains the derivative of `‖y‖ ^ 2`
`HasFDerivAt f f' x`: the linear map `f'` is the derivative of `f` at `x`. `innerSL ℝ a` is the
linear map `v ↦ ⟪a, v⟫_ℝ`; `2 • L` is `L` added to itself (a natural-number scalar). So this says
`d(‖y‖²) = 2⟪x, ·⟫`. -/
example {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (a : F) :
    HasFDerivAt (fun y : F => ‖y‖ ^ 2) ((2 : ℕ) • (innerSL ℝ) a) a := by
  have h := (hasStrictFDerivAt_norm_sq a).hasFDerivAt
  exact h

/-! ### R4. `HasFDerivAt.sqrt` · context gains the derivative of `fun y => √(f y)`
`hf.sqrt hx : HasFDerivAt (fun y => √(f y)) ((1 / (2 * √(f a))) • f') a`, given `hx : f a ≠ 0`.
`√` is `Real.sqrt`. -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (f' : E →L[ℝ] ℝ) (a : E)
    (hf : HasFDerivAt f f' a) (hx : f a ≠ 0) :
    HasFDerivAt (fun y => √(f y)) ((1 / (2 * √(f a))) • f') a := by
  have h := hf.sqrt hx
  exact h

/-! ### R5. `funext y` · goal `f = g` (two functions) → context gains `y`, goal `f y = g y` -/
example {α β : Type} (f g : α → β) (h : ∀ y, f y = g y) : f = g := by
  funext y
  exact h y

/-! ### R6. `norm_nonneg` · `norm_nonneg y : 0 ≤ ‖y‖`, for any `y` -/
example {E : Type} [NormedAddCommGroup E] (y : E) : 0 ≤ ‖y‖ := by
  have h := norm_nonneg y
  exact h

/-! ### R7. `Real.sqrt_sq` · `0 ≤ a → √(a ^ 2) = a` · goal: `√(a ^ 2)` → `a`
Its argument is the proof of `0 ≤ a`: `norm_nonneg y` (R6), or `hn.le` to weaken `hn : 0 < a`. -/
example (a : ℝ) (ha : 0 ≤ a) (P : ℝ → Prop) (h : P a) : P (√(a ^ 2)) := by
  rw [Real.sqrt_sq ha]
  exact h

/-! ### R8. `rw [e] at h` · rewrites the hypothesis `h` instead of the goal · context changes -/
example {α β : Type} (f g : α → β) (e : f = g) (Q : (α → β) → Prop) (h : Q f) : Q g := by
  rw [e] at h
  exact h

/-! ### R9. `Space.deriv_eq` · goal: `∂[i] f x` → `fderiv ℝ f x (basis i)`
`∂[i] f x` (printed `Space.deriv i f x`) is the partial derivative along the unit vector `basis i`.
`fderiv ℝ f x` is the derivative of `f` at `x` as a linear map; applying it to a vector `v` gives the
directional derivative along `v`. `rw [← Space.deriv_eq]` folds it back into `∂[i]`. -/
example (f : Space → ℝ) (i : Fin 3) (x : Space) (P : ℝ → Prop)
    (h : P (fderiv ℝ f x (basis i))) : P (∂[i] f x) := by
  rw [Space.deriv_eq]
  exact h

/-! ### R10. `HasFDerivAt.fderiv` · goal: `fderiv ℝ f x` → `f'`, given `hf : HasFDerivAt f f' x`
`rw [hf.fderiv]` needs the function in `hf` to be the function in the goal, literally. -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (f' : E →L[ℝ] ℝ) (x v : E)
    (hf : HasFDerivAt f f' x) (P : ℝ → Prop) (h : P (f' v)) : P (fderiv ℝ f x v) := by
  rw [hf.fderiv]
  exact h

/-! ## Evaluating a linear map at `basis i` (`simp` applies R11–R14 by itself) -/

/-! ### R11. `_root_.smul_apply` · goal: `(c • L) v` → `c • L v`
The `_root_.` is needed because `open Space` makes `smul_apply` mean `Space.smul_apply`. -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : E →L[ℝ] ℝ) (c : ℝ) (v : E)
    (P : ℝ → Prop) (h : P (c • L v)) : P ((c • L) v) := by
  rw [_root_.smul_apply]
  exact h

/-! ### R12. `smul_eq_mul`, `nsmul_eq_mul` · goal: `a • b` → `a * b`; `n • b` → `↑n * b` (`n : ℕ`) -/
example (a b : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (a * b + ↑n * b)) : P (a • b + n • b) := by
  rw [smul_eq_mul]
  rw [nsmul_eq_mul]
  exact h

/-! ### R13. `coe_innerSL_apply` · goal: `(innerSL ℝ a) v` → `⟪a, v⟫_ℝ` -/
example {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (a v : F) (P : ℝ → Prop)
    (h : P ⟪a, v⟫_ℝ) : P ((innerSL ℝ) a v) := by
  simp only [coe_innerSL_apply]
  exact h

/-! ### R14. `Space.inner_basis` · goal: `⟪p, basis i⟫_ℝ` → `p i`, the `i`-th coordinate
`p i` is printed `p.val 3 i` (`3` is the dimension of `Space`). -/
example (p : Space) (i : Fin 3) (P : ℝ → Prop) (h : P (p i)) : P ⟪p, basis i⟫_ℝ := by
  rw [Space.inner_basis]
  exact h

/-! ### R15. `field_simp` · goal: clears every denominator it knows to be nonzero
It looks for `0 < r` or `r ≠ 0` in the context; `a / r = b` becomes `a = b * r`-style. The result is
a polynomial goal; it may close it, or leave it for `ring` / `nlinarith`. -/
example (r a b : ℝ) (hr : 0 < r) (h : r ^ 2 - a = r ^ 5 * b) : (r ^ 3)⁻¹ - a / r ^ 5 = b := by
  field_simp
  exact h

/-! ## The chain rule `ℝ → ℝ` after `E → ℝ` -/

/-! ### R16. `DifferentiableAt.norm` · context gains `DifferentiableAt ℝ (fun y => ‖y‖) x`, for `x ≠ 0`
`DifferentiableAt.norm ℝ differentiableAt_id hx`: the norm of the identity map is differentiable
wherever it is nonzero. The `ℝ` is explicit; state the type with `have h : … := …` so Lean prints
`fun y => ‖y‖` rather than `fun y => ‖id y‖`. -/
example {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (x : F) (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun y : F => ‖y‖) x := by
  have h : DifferentiableAt ℝ (fun y : F => ‖y‖) x := DifferentiableAt.norm ℝ differentiableAt_id hx
  exact h

/-! ### R17. `hasDerivAt_pow` · context gains `HasDerivAt (fun x => x ^ n) (↑n * a ^ (n - 1)) a`
`HasDerivAt g g' a` is the one-variable version: `g : ℝ → ℝ` has derivative the number `g'` at `a`. -/
example (a : ℝ) : HasDerivAt (fun x : ℝ => x ^ 3) (↑3 * a ^ (3 - 1)) a := by
  have h := hasDerivAt_pow 3 a
  exact h

/-! ### R18. `HasDerivAt.fun_inv` · context gains the derivative of `fun r => (c r)⁻¹`
`hc.fun_inv hx : HasDerivAt (fun r => (c r)⁻¹) (-c' / c a ^ 2) a`, given `hx : c a ≠ 0`. -/
example (c : ℝ → ℝ) (c' a : ℝ) (hc : HasDerivAt c c' a) (hx : c a ≠ 0) :
    HasDerivAt (fun r => (c r)⁻¹) (-c' / c a ^ 2) a := by
  have h := hc.fun_inv hx
  exact h

/-! ### R19. `DifferentiableAt.hasFDerivAt` · `hd.hasFDerivAt : HasFDerivAt f (fderiv ℝ f x) x` -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (x : E)
    (hd : DifferentiableAt ℝ f x) : HasFDerivAt f (fderiv ℝ f x) x := by
  have h := hd.hasFDerivAt
  exact h

/-! ### R20. `HasDerivAt.comp_hasFDerivAt` · chain rule: `g ∘ f` has derivative `g' • f'`
`hg.comp_hasFDerivAt x hf : HasFDerivAt (g ∘ f) (g' • f') x` for `hg : HasDerivAt g g' (f x)`,
`hf : HasFDerivAt f f' x`. Written as `have h : HasFDerivAt (fun y => g (f y)) … := …`, the
context gets the lambda form, which `rw [h.fderiv]` (R10) can match in a goal. -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (g : ℝ → ℝ) (f' : E →L[ℝ] ℝ)
    (g' : ℝ) (x : E) (hg : HasDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun y => g (f y)) (g' • f') x := by
  have h : HasFDerivAt (fun y => g (f y)) (g' • f') x := hg.comp_hasFDerivAt x hf
  exact h

/-! ## The product rule on `Space` -/

/-! ### R21. `pow_pos`, `.ne'` · `pow_pos hr n : 0 < r ^ n`; `(pow_pos hr n).ne' : r ^ n ≠ 0` -/
example (r : ℝ) (hr : 0 < r) : r ^ 3 ≠ 0 := by
  have h := (pow_pos hr 3).ne'
  exact h

/-! ### R22. `DifferentiableAt.pow`, `DifferentiableAt.inv` · context gains differentiability of `f ^ n`, `(f ^ n)⁻¹`
`hd.pow n : DifferentiableAt ℝ (f ^ n) x`; `(hd.pow n).inv hne : DifferentiableAt ℝ (f ^ n)⁻¹ x`
given `hne : f x ^ n ≠ 0` (R21). `f ^ n` and `(f ^ n)⁻¹` are pointwise operations on functions; a
`have` with the type `fun y => (f y ^ n)⁻¹` accepts them (definitionally equal). -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (x : E)
    (hd : DifferentiableAt ℝ f x) (hne : f x ^ 3 ≠ 0) :
    DifferentiableAt ℝ (fun y => (f y ^ 3)⁻¹) x := by
  have h : DifferentiableAt ℝ (fun y => (f y ^ 3)⁻¹) x := (hd.pow 3).inv hne
  exact h

/-! ### R23. `fun_prop` · closes a `DifferentiableAt` goal built from known pieces (coordinates, `+`, `*`, …) -/
example (x : Space) (i j : Fin 3) : DifferentiableAt ℝ (fun y : Space => 2 * y i + y j) x := by
  fun_prop

/-! ### R24. `change` · goal: replaced by a definitionally equal one; here `fun y => c y * f y` → `c • f`
`c • f` for two functions is the pointwise product; it is the shape `Space.deriv_smul` (R25) needs. -/
example (c f : Space → ℝ) (P : (Space → ℝ) → Prop) (h : P (c • f)) : P (fun y => c y * f y) := by
  change P (c • f)
  exact h

/-! ### R25. `Space.deriv_smul` · goal: `∂[u] (c • f) x` → `c x • ∂[u] f x + ∂[u] c x • f x` (product rule)
Its arguments are `hc : DifferentiableAt ℝ c x` and `hf : DifferentiableAt ℝ f x`. -/
example (c f : Space → ℝ) (u : Fin 3) (x : Space) (hc : DifferentiableAt ℝ c x)
    (hf : DifferentiableAt ℝ f x) (P : ℝ → Prop)
    (h : P (c x • ∂[u] f x + ∂[u] c x • f x)) : P (∂[u] (c • f) x) := by
  rw [Space.deriv_smul hc hf]
  exact h

/-! ### R26. `Space.deriv_component_same` · goal: `∂[i] (fun y => y i) x` → `1` -/
example (i : Fin 3) (x : Space) (P : ℝ → Prop) (h : P 1) : P (∂[i] (fun y : Space => y i) x) := by
  rw [Space.deriv_component_same]
  exact h

/-! ### R27. `ring` · closes an identity of commutative rings (here: after `field_simp`) -/
example (r a : ℝ) : r ^ 2 + -(3 * a ^ 2) = r ^ 2 - 3 * a ^ 2 := by
  ring

/-! ## The divergence -/

/-! ### R28. `unfold Space.div` · goal: `(∇ ⬝ F) x` → `∑ i, ∂[i] (fun y => (F y).ofLp i) x`
`∇ ⬝ F` is printed `div F`. `F y : EuclideanSpace ℝ (Fin 3)` is a vector, and `v.ofLp i` is its
`i`-th component (you may write `v i` in source; Lean prints `v.ofLp i`). -/
example (F : Space → EuclideanSpace ℝ (Fin 3)) (x : Space) (P : ℝ → Prop)
    (h : P (∑ i, ∂[i] (fun y => (F y).ofLp i) x)) : P ((∇ ⬝ F) x) := by
  unfold Space.div
  exact h

/-! ### R29. `PiLp.smul_apply` · goal: `(c • v).ofLp i` → `c • v.ofLp i` -/
example (c : ℝ) (v : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) (P : ℝ → Prop)
    (h : P (c • v.ofLp i)) : P ((c • v).ofLp i) := by
  rw [PiLp.smul_apply]
  exact h

/-! ### R30. `Space.basis_repr_apply` · goal: `(basis.repr p).ofLp i` → `p i`
`basis.repr p : EuclideanSpace ℝ (Fin 3)` is the point `p` written as a coordinate vector. -/
example (p : Space) (i : Fin 3) (P : ℝ → Prop) (h : P (p i)) : P ((basis.repr p).ofLp i) := by
  rw [Space.basis_repr_apply]
  exact h

/-! ### R31. `simp only [e]` · goal: rewrites under binders (`fun`, `∑ i, …`), where `rw` fails
With `e : ∀ i, f i = g i`, `simp only [e]` rewrites every `f i` inside `∑ i, …`. It also
beta-reduces `(fun y => …) x`. -/
example (f g : Fin 3 → ℝ) (e : ∀ i, f i = g i) (P : ℝ → Prop) (h : P (∑ i, g i)) :
    P (∑ i, f i) := by
  simp only [e]
  exact h

/-! ### R32. `Fin.sum_univ_three` · goal: `∑ i : Fin 3, f i` → `f 0 + f 1 + f 2` -/
example {β : Type} [AddCommMonoid β] (f : Fin 3 → β) (P : β → Prop) (h : P (f 0 + f 1 + f 2)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_three]
  exact h

/-! ### R33. `Space.norm_sq_eq` · `‖p‖ ^ 2 = ∑ i, p i ^ 2` · goal: `‖p‖ ^ 2` → the sum of squares
`have h := Space.norm_sq_eq p` puts the same equation in the context instead. -/
example (p : Space) (P : ℝ → Prop) (h : P (∑ i, p i ^ 2)) : P (‖p‖ ^ 2) := by
  rw [Space.norm_sq_eq]
  exact h

/-! ### R34. `nlinarith [h]` · closes a polynomial (in)equality that follows from `h` by arithmetic
It multiplies and adds the hypotheses it is given; `linarith` is the linear version. -/
example (r a b : ℝ) (h : r ^ 2 = a ^ 2 + b ^ 2) : r ^ 2 - a ^ 2 + (r ^ 2 - b ^ 2) = r ^ 2 := by
  nlinarith [h]

/-! # Part W · Worked combinations (not the exercise's functions) -/

/-! ### W1. `∂ᵢ ‖y‖² = 2 xᵢ`: R3, R9, R10, then `simp` evaluates (R11–R14) -/
example (i : Fin 3) (x : Space) : ∂[i] (fun y : Space => ‖y‖ ^ 2) x = 2 * x i := by
  have hd := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  rw [Space.deriv_eq, hd.fderiv]
  simp

/-! ### W2. Chain rule through `r ↦ r ^ 2` after `‖·‖`: R16, R17, R19, R20, R9, R10, R11, R12 -/
example (i : Fin 3) (x : Space) (h0 : x ≠ 0) :
    ∂[i] (fun y : Space => ‖y‖ ^ 2) x = 2 * ‖x‖ * ∂[i] (fun y : Space => ‖y‖) x := by
  have hd : DifferentiableAt ℝ (fun y : Space => ‖y‖) x := DifferentiableAt.norm ℝ differentiableAt_id h0
  have hg := hasDerivAt_pow 2 ‖x‖
  have hc : HasFDerivAt (fun y : Space => ‖y‖ ^ 2)
      ((↑2 * ‖x‖ ^ (2 - 1)) • fderiv ℝ (fun y : Space => ‖y‖) x) x :=
    hg.comp_hasFDerivAt x hd.hasFDerivAt
  rw [Space.deriv_eq, hc.fderiv, _root_.smul_apply, smul_eq_mul, ← Space.deriv_eq]
  norm_num

/-! ### W3. Product rule for `y ↦ yᵢ · yᵢ`: R24, R25, R26, R12, `ring` -/
example (i : Fin 3) (x : Space) : ∂[i] (fun y : Space => y i * y i) x = 2 * x i := by
  have hf : DifferentiableAt ℝ (fun y : Space => y i) x := by fun_prop
  change ∂[i] ((fun y : Space => y i) • fun y : Space => y i) x = _
  rw [Space.deriv_smul hf hf, Space.deriv_component_same]
  simp only [smul_eq_mul]
  ring

end H109Guide
