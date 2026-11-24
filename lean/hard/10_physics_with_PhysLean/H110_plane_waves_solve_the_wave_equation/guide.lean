/- Guide for H110 (Plane waves solve the wave equation).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Entries that build a fact from a hypothesis (`hg y`, `hf.differentiable …`) use `have h := …`, so
the context gains `h` and you can read off exactly what was produced.
Part W: worked combinations on functions that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Physlib.ClassicalMechanics.WaveEquation.Basic

open Space Time ClassicalMechanics InnerProductSpace

namespace H110Guide

/-! # Part R · Reference entries -/

/-! ## Derivatives as linear maps: `∂ₜ`, `fderiv`, the chain rule -/

/-! ### R1. `Time.deriv_eq` · goal: `∂ₜ f t` → `fderiv ℝ f t 1` (the derivative map applied to `1`) -/
example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Time → F) (t : Time)
    (P : F → Prop) (h : P (fderiv ℝ f t 1)) : P (∂ₜ f t) := by
  rw [Time.deriv_eq]
  exact h

/-! ### R2. `change` · goal: replaced by a definitionally equal one; here `fun x => g (f x)` → `g ∘ f` -/
example {E F G : Type} (f : E → F) (g : F → G) (P : (E → G) → Prop) (h : P (g ∘ f)) :
    P (fun x => g (f x)) := by
  change P (g ∘ f)
  exact h

/-! ### R3. `hg y` · context gains `DifferentiableAt ℝ g y` from `hg : Differentiable ℝ g`
`Differentiable ℝ g` is by definition `∀ y, DifferentiableAt ℝ g y`, so apply it to a point. -/
example {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (g : F → G) (hg : Differentiable ℝ g) (y : F) : DifferentiableAt ℝ g y := by
  have h := hg y
  exact h

/-! ### R4. `fun_prop` · closes a `Differentiable` / `DifferentiableAt` goal built from known pieces
It combines `+`, `*`, `•`, `∘`, `⟪·,·⟫_ℝ`, `Time.val`, constants and the hypotheses in the context. -/
example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F) (hf : Differentiable ℝ f)
    (a b : ℝ) (t : Time) : DifferentiableAt ℝ (fun τ : Time => a • f (b * τ.val)) t := by
  fun_prop

/-! ### R5. `fderiv_comp` · goal: `fderiv ℝ (g ∘ f) x` → `(fderiv ℝ g (f x)).comp (fderiv ℝ f x)`
`rw [fderiv_comp x hg hf]` with `hg : DifferentiableAt ℝ g (f x)`, `hf : DifferentiableAt ℝ f x`.
Write `rw [fderiv_comp _ hg hf]` or `rw [fderiv_comp _ (hg' _) (by fun_prop)]` to let Lean find `x`. -/
example {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (f : E → F) (g : F → G) (x : E)
    (hg : DifferentiableAt ℝ g (f x)) (hf : DifferentiableAt ℝ f x)
    (P : (E →L[ℝ] G) → Prop) (h : P ((fderiv ℝ g (f x)).comp (fderiv ℝ f x))) :
    P (fderiv ℝ (g ∘ f) x) := by
  rw [fderiv_comp x hg hf]
  exact h

/-! ### R6. `ContinuousLinearMap.comp_apply` · goal: `(L.comp M) v` → `L (M v)` -/
example {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G) (M : E →L[ℝ] F)
    (v : E) (P : G → Prop) (h : P (L (M v))) : P ((L.comp M) v) := by
  rw [ContinuousLinearMap.comp_apply]
  exact h

/-! ### R7. `fderiv_eq_smul_deriv` · goal: `fderiv ℝ f x y` → `y • deriv f x`, for `f : ℝ → F`
`deriv f x : F` is the ordinary derivative; Lean prints it `_root_.deriv` because `Space.deriv`
and `Time.deriv` are open too. -/
example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F) (x y : ℝ) (P : F → Prop)
    (h : P (y • _root_.deriv f x)) : P (fderiv ℝ f x y) := by
  rw [fderiv_eq_smul_deriv]
  exact h

/-! ### R8. `fderiv_const_sub` · goal: `fderiv ℝ (fun y => c - f y) x` → `-fderiv ℝ f x` -/
example {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : E → F) (c : F) (x : E) (P : (E →L[ℝ] F) → Prop)
    (h : P (-fderiv ℝ f x)) : P (fderiv ℝ (fun y => c - f y) x) := by
  rw [fderiv_const_sub]
  exact h

/-! ### R9. `fderiv_const_mul` · goal: `fderiv ℝ (fun y => b * a y) x` → `b • fderiv ℝ a x`
Takes `ha : DifferentiableAt ℝ a x` first: `rw [fderiv_const_mul ha]` or `(by fun_prop)`. -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : E → ℝ) (b : ℝ) (x : E)
    (ha : DifferentiableAt ℝ a x) (P : (E →L[ℝ] ℝ) → Prop) (h : P (b • fderiv ℝ a x)) :
    P (fderiv ℝ (fun y => b * a y) x) := by
  rw [fderiv_const_mul ha]
  exact h

/-! ### R10. `Time.fderiv_val` · goal: `fderiv ℝ Time.val t 1` → `1` (`simp` applies it by itself) -/
example (t : Time) (P : ℝ → Prop) (h : P 1) : P (fderiv ℝ Time.val t 1) := by
  rw [Time.fderiv_val]
  exact h

/-! ### R11. `_root_.neg_apply`, `_root_.smul_apply` · goal: `(-L) v` → `-L v`; `(c • L) v` → `c • L v`
Evaluating a negated or scaled linear map. `simp` applies both by itself; `rw` needs `_root_.`
because `open Space` makes `smul_apply`, `neg_apply` mean `Space.smul_apply`, `Space.neg_apply`
(coordinates of `c • p`, `-p` for a point `p : Space d`). -/
example {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E →L[ℝ] F) (c : ℝ) (v : E) (P : F → Prop) (h : P (-(c • L v))) :
    P ((-(c • L)) v) := by
  rw [_root_.neg_apply]
  rw [_root_.smul_apply]
  exact h

/-! ## Space derivatives and the inner product -/

/-! ### R12. `Space.deriv_eq` · goal: `∂[i] f x` → `fderiv ℝ f x (Space.basis i)`
`∂[i] f x` is printed `Space.deriv i f x`; `Space.basis i` is the `i`-th unit vector. -/
example {d : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Space d → F) (i : Fin d)
    (x : Space d) (P : F → Prop) (h : P (fderiv ℝ f x (Space.basis i))) : P (∂[i] f x) := by
  rw [Space.deriv_eq]
  exact h

/-! ### R13. `fderiv_sub_const` · goal: `fderiv ℝ (fun y => f y - c) x` → `fderiv ℝ f x` -/
example {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : E → F) (c : F) (x : E) (P : (E →L[ℝ] F) → Prop)
    (h : P (fderiv ℝ f x)) : P (fderiv ℝ (fun y => f y - c) x) := by
  rw [fderiv_sub_const]
  exact h

/-! ### R14. `fderiv_inner_apply ℝ hf hg` · goal: derivative of `⟪f y, g y⟫_ℝ` → product rule
`fderiv ℝ (fun y => ⟪f y, g y⟫_ℝ) x v = ⟪f x, fderiv ℝ g x v⟫_ℝ + ⟪fderiv ℝ f x v, g x⟫_ℝ`.
The field `ℝ` is an explicit argument; both hypotheses are usually `(by fun_prop)`. -/
example {E G : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (f g : G → E) (x v : G) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (P : ℝ → Prop)
    (h : P (⟪f x, fderiv ℝ g x v⟫_ℝ + ⟪fderiv ℝ f x v, g x⟫_ℝ)) :
    P (fderiv ℝ (fun y => ⟪f y, g y⟫_ℝ) x v) := by
  rw [fderiv_inner_apply ℝ hf hg]
  exact h

/-! ### R15. `fderiv_fun_const` · goal: derivative of a constant function → `0` (`simp` uses it) -/
example {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (u : F) (P : (E → E →L[ℝ] F) → Prop) (h : P 0) :
    P (fderiv ℝ (fun _ : E => u)) := by
  rw [fderiv_fun_const]
  exact h

/-! ### R16. `fderiv_fun_id` · goal: derivative of `fun y => y` → the identity map (`simp` uses it) -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) (P : (E →L[ℝ] E) → Prop)
    (h : P (ContinuousLinearMap.id ℝ E)) : P (fderiv ℝ (fun y : E => y) x) := by
  rw [fderiv_fun_id]
  exact h

/-! ### R17. `Space.basis_inner` · goal: `⟪Space.basis i, p⟫_ℝ` → `p.val i`, the `i`-th coordinate -/
example {d : ℕ} (p : Space d) (i : Fin d) (P : ℝ → Prop) (h : P (p.val i)) :
    P ⟪Space.basis i, p⟫_ℝ := by
  rw [Space.basis_inner]
  exact h

/-! ## Smoothness facts from `ContDiff ℝ 2 f` -/

/-! ### R18. `ContDiff.differentiable` · context gains `Differentiable ℝ f` from `ContDiff ℝ n f`
Its argument is `n ≠ 0`; for `n = 2` write `hf.differentiable (by simp)`. -/
example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F) (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ f := by
  have h := hf.differentiable (by simp)
  exact h

/-! ### R19. `ContDiff.differentiable_iteratedDeriv` · context gains `Differentiable ℝ (iteratedDeriv m f)`
Its argument is `↑m < n`; for `m = 1`, `n = 2` write `(by norm_num)`. -/
example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F) (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (iteratedDeriv 1 f) := by
  have h := hf.differentiable_iteratedDeriv 1 (by norm_num)
  exact h

/-! ### R20. `iteratedDeriv_one` · goal: `iteratedDeriv 1 f` → `deriv f` -/
example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F) (P : (ℝ → F) → Prop)
    (h : P (_root_.deriv f)) : P (iteratedDeriv 1 f) := by
  rw [iteratedDeriv_one]
  exact h

/-! ### R21. `iteratedDeriv_succ` · goal: `iteratedDeriv (n + 1) f` → `deriv (iteratedDeriv n f)`
`2` matches `n + 1` with `n = 1`, so `rw [iteratedDeriv_succ, iteratedDeriv_one]` turns
`iteratedDeriv 2 f` into `deriv (deriv f)`. -/
example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F) (P : (ℝ → F) → Prop)
    (h : P (_root_.deriv (iteratedDeriv 1 f))) : P (iteratedDeriv 2 f) := by
  rw [iteratedDeriv_succ]
  exact h

/-! ### R22. `simpa [l] using e` · closes the goal: simplifies both `e` and the goal with `l`, then matches -/
example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F)
    (e : Differentiable ℝ (iteratedDeriv 1 f)) : Differentiable ℝ (_root_.deriv f) := by
  simpa [iteratedDeriv_one] using e

/-! ## Time derivatives of plane waves -/

/-! ### R23. `planeWave_eq` · goal: `planeWave f₀ c s t x` → `f₀ (⟪x, s.unit⟫_ℝ - c * t.val)` -/
example {d : ℕ} (f₀ : ℝ → EuclideanSpace ℝ (Fin d)) (c : ℝ) (s : Direction d) (t : Time)
    (x : Space d) (P : EuclideanSpace ℝ (Fin d) → Prop) (h : P (f₀ (⟪x, s.unit⟫_ℝ - c * t.val))) :
    P (planeWave f₀ c s t x) := by
  simp only [planeWave_eq]
  exact h

/-! ### R24. `simp only [h]` · goal: rewrites under `fun` binders, where `rw [h]` fails
`rw` cannot rewrite `f y` when `y` is bound by a `fun` (it reports "motive is not type correct"
or finds no instance); `simp only` can. Use it to apply a `∀`-lemma inside `fun τ => …`. -/
example (f g : ℝ → ℝ) (hfg : ∀ y, f y = g y) (P : (ℝ → ℝ) → Prop) (h : P (fun y => g y * 2)) :
    P (fun y => f y * 2) := by
  simp only [hfg]
  exact h

/-! ### R25. `Time.deriv_smul` · goal: `∂ₜ (fun τ => k • f τ) t` → `k • ∂ₜ (fun τ => f τ) t`
Only for `f : Time → EuclideanSpace ℝ (Fin d)`; needs `Differentiable ℝ f` (often `(by fun_prop)`). -/
example {d : ℕ} (f : Time → EuclideanSpace ℝ (Fin d)) (k : ℝ) (t : Time) (hf : Differentiable ℝ f)
    (P : EuclideanSpace ℝ (Fin d) → Prop) (h : P (k • ∂ₜ f t)) :
    P (∂ₜ (fun τ => k • f τ) t) := by
  rw [Time.deriv_smul _ _ hf]
  exact h

/-! ### R26. `smul_smul` · goal: `a • b • v` → `(a * b) • v` -/
example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (a b : ℝ) (v : F) (P : F → Prop)
    (h : P ((a * b) • v)) : P (a • b • v) := by
  rw [smul_smul]
  exact h

/-! ### R27. `ring_nf` · closes `(-a * -a) • v = a ^ 2 • v`: normalises the scalar on each side -/
example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (a : ℝ) (v : F) :
    (-a * -a) • v = a ^ 2 • v := by
  ring_nf

/-! ## Second space derivatives -/

/-! ### R28. `fderiv_fun_const_smul` · goal: `fderiv ℝ (fun y => c • f y) x` → `c • fderiv ℝ f x`
Takes `hf : DifferentiableAt ℝ f x` first (often `(by fun_prop)`). -/
example {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : E → F) (c : ℝ) (x : E) (hf : DifferentiableAt ℝ f x)
    (P : (E →L[ℝ] F) → Prop) (h : P (c • fderiv ℝ f x)) :
    P (fderiv ℝ (fun y => c • f y) x) := by
  rw [fderiv_fun_const_smul hf]
  exact h

/-! ### R29. `pow_two` · goal: `a ^ 2` → `a * a` -/
example (a : ℝ) (P : ℝ → Prop) (h : P (a * a)) : P (a ^ 2) := by
  rw [pow_two]
  exact h

/-! ### R30. `unfold planeWave` · goal: the name `planeWave f₀ c s t` → its `fun x => …` body -/
example {d : ℕ} (f₀ : ℝ → EuclideanSpace ℝ (Fin d)) (c : ℝ) (s : Direction d) (t : Time)
    (P : (Space d → EuclideanSpace ℝ (Fin d)) → Prop)
    (h : P (fun x => f₀ (⟪x, s.unit⟫_ℝ - c * t.val))) : P (planeWave f₀ c s t) := by
  unfold planeWave
  exact h

/-! ## The unit vector: `∑ i, sᵢ² = 1` -/

/-! ### R31. `Space.norm_sq_eq` · `‖p‖ ^ 2 = ∑ i, p.val i ^ 2`; `rw [← …]` folds the sum into a norm -/
example {d : ℕ} (p : Space d) (P : ℝ → Prop) (h : P (‖p‖ ^ 2)) : P (∑ i, p.val i ^ 2) := by
  rw [← Space.norm_sq_eq]
  exact h

/-! ### R32. `s.norm` (`Direction.norm`) · goal: `‖s.unit‖` → `1` -/
example {d : ℕ} (s : Direction d) (P : ℝ → Prop) (h : P 1) : P ‖s.unit‖ := by
  rw [s.norm]
  exact h

/-! ### R33. `one_pow` · goal: `1 ^ n` → `1` -/
example (n : ℕ) (P : ℝ → Prop) (h : P 1) : P (1 ^ n) := by
  rw [one_pow]
  exact h

/-! ## The vector Laplacian, component by component -/

/-! ### R34. `ext j` on `EuclideanSpace ℝ (Fin d)` · goal `v = w` → context gains `j`, goal `v.ofLp j = w.ofLp j`
`v.ofLp j` is the `j`-th component of `v`. -/
example {d : ℕ} (v w : EuclideanSpace ℝ (Fin d)) (h : ∀ j, v.ofLp j = w.ofLp j) : v = w := by
  ext j
  exact h j

/-! ### R35. `laplacianVec` · goal: `Δᵥ F x` → the vector of the scalar Laplacians of its components -/
example {d : ℕ} (F : Space d → EuclideanSpace ℝ (Fin d)) (x : Space d)
    (P : EuclideanSpace ℝ (Fin d) → Prop)
    (h : P (WithLp.toLp 2 fun i => Δ (fun y => (F y).ofLp i) x)) : P (Δᵥ F x) := by
  simp only [laplacianVec]
  exact h

/-! ### R36. `PiLp.toLp_apply` · goal: `(WithLp.toLp p u).ofLp i` → `u i` -/
example {d : ℕ} (u : Fin d → ℝ) (i : Fin d) (P : ℝ → Prop) (h : P (u i)) :
    P ((WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d)).ofLp i) := by
  rw [PiLp.toLp_apply]
  exact h

/-! ### R37. `laplacian_eq_sum_snd_deriv` · goal: `Δ f` → `fun x => ∑ i, ∂[i] (∂[i] f) x` -/
example {d : ℕ} (f : Space d → ℝ) (P : (Space d → ℝ) → Prop)
    (h : P (fun x => ∑ i, ∂[i] (∂[i] f) x)) : P (Δ f) := by
  rw [laplacian_eq_sum_snd_deriv]
  exact h

/-! ### R38. `Space.deriv_euclid hF` · goal: derivative of a component → component of the derivative
`∂[i] (fun y => (F y).ofLp j) x = (∂[i] F x).ofLp j`, given `hF : Differentiable ℝ F`. -/
example {d : ℕ} (F : Space d → EuclideanSpace ℝ (Fin d)) (hF : Differentiable ℝ F) (i j : Fin d)
    (x : Space d) (P : ℝ → Prop) (h : P ((∂[i] F x).ofLp j)) :
    P (∂[i] (fun y => (F y).ofLp j) x) := by
  rw [Space.deriv_euclid hF]
  exact h

/-! ### R39. `PiLp.smul_apply` · goal: `(c • v).ofLp j` → `c • v.ofLp j` -/
example {d : ℕ} (c : ℝ) (v : EuclideanSpace ℝ (Fin d)) (j : Fin d) (P : ℝ → Prop)
    (h : P (c • v.ofLp j)) : P ((c • v).ofLp j) := by
  rw [PiLp.smul_apply]
  exact h

/-! ### R40. `smul_eq_mul` · goal: `a • b` → `a * b` when both are numbers -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (a * b)) : P (a • b) := by
  rw [smul_eq_mul]
  exact h

/-! ### R41. `Finset.sum_mul` · `(∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a`; `← …` pulls a common factor out -/
example {d : ℕ} (f : Fin d → ℝ) (a : ℝ) (P : ℝ → Prop) (h : P ((∑ i, f i) * a)) :
    P (∑ i, f i * a) := by
  rw [← Finset.sum_mul]
  exact h

/-! ### R42. `one_mul` · goal: `1 * a` → `a` -/
example (a : ℝ) (P : ℝ → Prop) (h : P a) : P (1 * a) := by
  rw [one_mul]
  exact h

/-! ## The wave equation -/

/-! ### R43. `rw [WaveEquation]` · goal: `WaveEquation f t x c` → its defining equation -/
example {d : ℕ} (f : Time → Space d → EuclideanSpace ℝ (Fin d)) (t : Time) (x : Space d) (c : ℝ)
    (h : c ^ 2 • Δᵥ (f t) x - ∂ₜ (fun τ => ∂ₜ (fun σ => f σ x) τ) t = 0) :
    WaveEquation f t x c := by
  rw [WaveEquation]
  exact h

/-! ### R44. `sub_self` · goal: `a - a` → `0` -/
example {F : Type} [NormedAddCommGroup F] (a : F) (P : F → Prop) (h : P 0) : P (a - a) := by
  rw [sub_self]
  exact h

/-! # Part W · Worked combinations (not the exercise's functions) -/

/-! ### W1. A time chain rule without the constant: `d/dt g(c t) = c g'(c t)`; R1, R2, R5, R6, R7, R9 -/
example {d : ℕ} (g : ℝ → EuclideanSpace ℝ (Fin d)) (hg : Differentiable ℝ g) (c : ℝ) (t : Time) :
    ∂ₜ (fun τ : Time => g (c * τ.val)) t = c • _root_.deriv g (c * t.val) := by
  rw [Time.deriv_eq]
  change fderiv ℝ (g ∘ fun τ : Time => c * τ.val) t 1 = _
  rw [fderiv_comp _ (hg _) (by fun_prop)]
  rw [ContinuousLinearMap.comp_apply]
  rw [fderiv_eq_smul_deriv]
  rw [fderiv_const_mul (by fun_prop)]
  simp

/-! ### W2. A scalar space chain rule: `∂ᵢ g(⟪y, u⟫) = uᵢ g'(⟪x, u⟫)` for `g : ℝ → ℝ`; R12, R2, R5, R6, R7, R14 -/
example {d : ℕ} (g : ℝ → ℝ) (hg : Differentiable ℝ g) (u : Space d) (i : Fin d) (x : Space d) :
    ∂[i] (fun y : Space d => g ⟪y, u⟫_ℝ) x = u.val i * _root_.deriv g ⟪x, u⟫_ℝ := by
  rw [Space.deriv_eq]
  change fderiv ℝ (g ∘ fun y : Space d => ⟪y, u⟫_ℝ) x (Space.basis i) = _
  rw [fderiv_comp _ (hg _) (by fun_prop)]
  rw [ContinuousLinearMap.comp_apply]
  rw [fderiv_eq_smul_deriv]
  rw [fderiv_inner_apply ℝ (by fun_prop) (by fun_prop)]
  simp

/-! ### W3. A vector of length 2: `∑ i, uᵢ² = 4`; R31, then the norm hypothesis, then `norm_num` -/
example {d : ℕ} (u : Space d) (hu : ‖u‖ = 2) : ∑ i, u.val i ^ 2 = 4 := by
  rw [← Space.norm_sq_eq]
  rw [hu]
  norm_num

end H110Guide
