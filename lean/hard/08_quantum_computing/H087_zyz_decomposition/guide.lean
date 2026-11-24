/- Guide for H087 (ZYZ decomposition of a qubit gate).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's.
Assumed: Lean basics (E001–E033). Matrix notation, `ext`, `fin_cases` and casts `ℝ → ℂ` are
explained in cheatsheet.md (Reading the goals) and lean/TACTIC_STATES.md.
-/
import Mathlib

open Matrix Complex

namespace H087Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 tools: unitarity → equations between entries -/

/-! ### R1. `(Matrix.mem_unitaryGroup_iff).mp` · context gains the equation `M * star M = 1` -/
example (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M ∈ Matrix.unitaryGroup (Fin 2) ℂ) (G : Prop)
    (g : M * star M = 1 → G) : G := by
  have h := (Matrix.mem_unitaryGroup_iff).mp hM
  exact g h

/-! ### R2. `congrFun (congrFun h i) j` · context gains entry `(i, j)` of a matrix equation -/
example (M N : Matrix (Fin 2) (Fin 2) ℂ) (h : M = N) (G : Prop) (g : M 1 0 = N 1 0 → G) : G := by
  have e := congrFun (congrFun h 1) 0
  exact g e

/-! ### R3. `simp [Matrix.mul_apply, Fin.sum_univ_two] at e` · context: hypothesis `e` evaluated
`simp` also uses `Matrix.star_apply` (`star M i j = conj (M j i)`) and `Matrix.one_apply_ne`. -/
example (M N : Matrix (Fin 2) (Fin 2) ℂ) (e : (M * star N) 1 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
    (G : Prop) (g : M 1 0 * (starRingEnd ℂ) (N 0 0) + M 1 1 * (starRingEnd ℂ) (N 0 1) = 0 → G) :
    G := by
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e
  exact g e

/-! ### R4. `Matrix.det_fin_two` · goal: `M.det` → `M 0 0 * M 1 1 - M 0 1 * M 1 0` -/
example (M : Matrix (Fin 2) (Fin 2) ℂ) (P : ℂ → Prop) (h : P (M 0 0 * M 1 1 - M 0 1 * M 1 0)) :
    P M.det := by
  rw [Matrix.det_fin_two]
  exact h

/-! ### R5. `refine ⟨by tac, by tac, ?_, ?_⟩` · goal list: close two conjuncts inline, keep two -/
example (A B C D : Prop) (ha : A) (hb : B) (hc : C) (hd : D) : A ∧ B ∧ C ∧ D := by
  refine ⟨by exact ha, by exact hb, ?_, ?_⟩
  exacts [hc, hd]

/-! ### R6. `linear_combination c₁ * e₁ + c₂ * e₂` · closes `lhs = rhs` when
`lhs - rhs = c₁ * (lhs₁ - rhs₁) + c₂ * (lhs₂ - rhs₂)` holds by `ring` (coefficients may be terms)
Here `b = -b * (a * u - 1) + a * (b * u - 0)`. -/
example (a b u : ℂ) (e₁ : a * u = 1) (e₂ : b * u = 0) : b = 0 := by
  linear_combination (-b) * e₁ + a * e₂

/-! ### R7. `Complex.mul_conj` · `z * conj z = ↑(normSq z)` · goal or hypothesis -/
example (z : ℂ) (P : ℂ → Prop) (h : P ↑(Complex.normSq z)) : P (z * (starRingEnd ℂ) z) := by
  rw [Complex.mul_conj]
  exact h

/-! ### R8. `Complex.normSq_eq_norm_sq` · `normSq z = ‖z‖ ^ 2` -/
example (z : ℂ) (P : ℝ → Prop) (h : P (‖z‖ ^ 2)) : P (Complex.normSq z) := by
  rw [Complex.normSq_eq_norm_sq]
  exact h

/-! ### R9. `exact_mod_cast e` · closes a goal that equals `e` up to casts `ℝ → ℂ` -/
example (x y : ℝ) (e : (↑x : ℂ) + ↑y = 1) : x + y = 1 := by
  exact_mod_cast e

/-! ### R10. `Matrix.det_of_mem_unitary` · `M ∈ unitaryGroup → M.det ∈ unitary ℂ` -/
example (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M ∈ Matrix.unitaryGroup (Fin 2) ℂ) (G : Prop)
    (g : M.det ∈ unitary ℂ → G) : G := by
  have h := Matrix.det_of_mem_unitary hM
  exact g h

/-! ### R11. `CStarRing.norm_of_mem_unitary` · `u ∈ unitary ℂ → ‖u‖ = 1` · closes the goal -/
example (u : ℂ) (hu : u ∈ unitary ℂ) : ‖u‖ = 1 := by
  exact CStarRing.norm_of_mem_unitary hu

/-! ## Part 2 tools: multiplying out the rotation product -/

/-! ### R12. `Matrix.mul_fin_two` · goal: product of two `!![…]` literals → one literal -/
example {α : Type} [CommRing α] (a b c d e f g k : α) (P : Matrix (Fin 2) (Fin 2) α → Prop)
    (h : P !![a * e + b * g, a * f + b * k; c * e + d * g, c * f + d * k]) :
    P (!![a, b; c, d] * !![e, f; g, k]) := by
  rw [Matrix.mul_fin_two]
  exact h

/-! ### R13. `Matrix.smul_of` · goal: `s • !![…]` → `of (s • ![…])`; entries then give `s * aᵢⱼ` -/
example {α : Type} [CommRing α] (s a b c d : α) (P : Matrix (Fin 2) (Fin 2) α → Prop)
    (h : P (Matrix.of (s • ![![a, b], ![c, d]]))) : P (s • !![a, b; c, d]) := by
  rw [Matrix.smul_of]
  exact h

/-! ### R14. `simp only [mul_zero, zero_mul, add_zero, zero_add]` · goal: drop the `0` terms -/
example {α : Type} [CommRing α] (a b c : α) (P : α → Prop) (h : P (a * b)) :
    P (0 * c + (a * b + c * 0)) := by
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  exact h

/-! ### R15. `Complex.exp_add` · `cexp (x + y) = cexp x * cexp y`; right to left merges a product
`have e : ∀ x y : ℂ, cexp x * cexp y = cexp (x + y) := fun x y => (Complex.exp_add x y).symm`
gives the merging direction a name. -/
example (x y : ℂ) (P : ℂ → Prop) (h : P (Complex.exp (x + y))) :
    P (Complex.exp x * Complex.exp y) := by
  rw [← Complex.exp_add]
  exact h

/-! ### R16. `rw [show ∀ a b c : α, … from fun a b c => by ring]` · goal: reorder a product
`rw` cannot see through `*` reassociation; state the reordering you need and prove it by `ring`. -/
example {α : Type} [CommRing α] (x y z : α) (P : α → Prop) (h : P (x * z * y)) :
    P (x * (y * z)) := by
  rw [show ∀ a b c : α, a * (b * c) = a * c * b from fun a b c => by ring]
  exact h

/-! ### R17. `congr 2` · goal `cexp a * c = cexp b * c` → `a = b` (strips `* c`, then `cexp`)
`congr` closes a leftover goal that is literally a hypothesis, so `h` here is stated backwards. -/
example (a b : ℂ) (c : ℝ) (h : b = a) :
    Complex.exp a * ↑c = Complex.exp b * ↑c := by
  congr 2
  exact h.symm

/-! ## Part 3 tools: half angles and `arccos` -/

/-! ### R18. `mul_div_cancel_left₀ _ two_ne_zero` · goal: `2 * x / 2` → `x` -/
example (x : ℝ) (P : ℝ → Prop) (h : P x) : P (2 * x / 2) := by
  rw [mul_div_cancel_left₀ _ two_ne_zero]
  exact h

/-! ### R19. `Real.cos_arccos` · `-1 ≤ x → x ≤ 1 → cos (arccos x) = x` -/
example (x : ℝ) (h0 : -1 ≤ x) (h1 : x ≤ 1) : Real.cos (Real.arccos x) = x := by
  exact Real.cos_arccos h0 h1

/-! ### R20. `Real.sin_arccos` · `sin (arccos x) = √(1 - x ^ 2)` (no side condition) -/
example (x : ℝ) (P : ℝ → Prop) (h : P (Real.sqrt (1 - x ^ 2))) : P (Real.sin (Real.arccos x)) := by
  rw [Real.sin_arccos]
  exact h

/-! ### R21. `linarith` · closes a linear (in)equality that follows from the hypotheses -/
example (x : ℝ) (h0 : 0 ≤ x) : -1 ≤ x := by
  linarith

/-! ## Part 4 tools: polar form -/

/-! ### R22. `Complex.norm_mul_exp_arg_mul_I` · `↑‖z‖ * cexp (↑(arg z) * I) = z`
Right to left, `rw [← …  z]` replaces `z` by its polar form (true for `z = 0` too). -/
example (z : ℂ) (P : ℂ → Prop) (h : P (↑‖z‖ * Complex.exp (↑z.arg * I))) : P z := by
  rw [← Complex.norm_mul_exp_arg_mul_I z]
  exact h

/-! ### R23. `conv_lhs => rw [h]` · goal: rewrite inside the left side of `=` only
Plain `rw [← Complex.norm_mul_exp_arg_mul_I z]` would also hit the `z` inside `z.arg` on the right. -/
example (z w : ℂ) (h : z = w) (h' : w = z.re) : z = z.re := by
  conv_lhs => rw [h]
  exact h'

/-! ### R24. `map_mul` · `f (x * y) = f x * f y` for a ring map such as `starRingEnd ℂ` (= `conj`) -/
example (x y : ℂ) (P : ℂ → Prop) (h : P ((starRingEnd ℂ) x * (starRingEnd ℂ) y)) :
    P ((starRingEnd ℂ) (x * y)) := by
  rw [map_mul]
  exact h

/-! ### R25. `Complex.conj_ofReal` · `conj ↑r = ↑r` for `r : ℝ` -/
example (r : ℝ) (P : ℂ → Prop) (h : P ↑r) : P ((starRingEnd ℂ) ↑r) := by
  rw [Complex.conj_ofReal]
  exact h

/-! ### R26. `Complex.exp_conj` · `cexp (conj x) = conj (cexp x)`; right to left pulls `conj` inside -/
example (x : ℂ) (P : ℂ → Prop) (h : P (Complex.exp ((starRingEnd ℂ) x))) :
    P ((starRingEnd ℂ) (Complex.exp x)) := by
  rw [← Complex.exp_conj]
  exact h

/-! ### R27. `push_cast` · goal: casts moved inward, `↑(x - y)` → `↑x - ↑y` -/
example (x y : ℝ) (P : ℂ → Prop) (h : P (↑x - ↑y)) : P (↑(x - y)) := by
  push_cast
  exact h

/-! ## Part 5 tools: assembling the decomposition -/

/-! ### R28. `obtain ⟨h₁, h₂, h₃⟩ := e` · context: a conjunction split into its parts -/
example (A B C G : Prop) (e : A ∧ B ∧ C) (g : A → B → C → G) : G := by
  obtain ⟨h₁, h₂, h₃⟩ := e
  exact g h₁ h₂ h₃

/-! ### R29. `Matrix.eta_fin_two M` · goal: `M` → `!![M 0 0, M 0 1; M 1 0, M 1 1]` -/
example (M : Matrix (Fin 2) (Fin 2) ℂ) (P : Matrix (Fin 2) (Fin 2) ℂ → Prop)
    (h : P !![M 0 0, M 0 1; M 1 0, M 1 1]) : P M := by
  rw [Matrix.eta_fin_two M]
  exact h

/-! ### R30. `set x := e` · context gains `x := e`; every `e` in goal and context becomes `x` -/
example (M : Matrix (Fin 2) (Fin 2) ℂ) (P : ℂ → Prop) (h : P (M 0 0)) : P (M 0 0) := by
  set x := M 0 0
  exact h

/-! ### R31. `nlinarith [t₁, t₂]` · closes a nonlinear (in)equality; `tᵢ` are extra facts to use
`norm_nonneg z : 0 ≤ ‖z‖` is the usual extra fact. -/
example (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) (hx : 0 ≤ x) : x ≤ 1 := by
  nlinarith [sq_nonneg y]

/-! ### R32. `Real.sqrt_sq` · `0 ≤ a → √(a ^ 2) = a` · closes the goal -/
example (a : ℝ) (ha : 0 ≤ a) : Real.sqrt (a ^ 2) = a := by
  exact Real.sqrt_sq ha

/-! ### R33. `Complex.exp_pi_mul_I` · `cexp (↑π * I) = -1` -/
example (P : ℂ → Prop) (h : P (-1)) : P (Complex.exp (↑Real.pi * I)) := by
  rw [Complex.exp_pi_mul_I]
  exact h

/-! ### R34. `add_mul` · `(a + b) * c = a * c + b * c` -/
example {α : Type} [CommRing α] (a b c : α) (P : α → Prop) (h : P (a * c + b * c)) :
    P ((a + b) * c) := by
  rw [add_mul]
  exact h

/-! ### R35. `sub_add_cancel` · `a - b + b = a` · here in a hypothesis: `rw [sub_add_cancel] at h` -/
example {α : Type} [CommRing α] (a b : α) (P : α → Prop) (h : P (a - b + b)) (G : Prop)
    (g : P a → G) : G := by
  rw [sub_add_cancel] at h
  exact g h

/-! ### R36. `neg_mul`, `neg_neg` · `-a * b = -(a * b)`, `- -a = a` -/
example {α : Type} [CommRing α] (a b : α) (P : α → Prop) (h : P (a * b)) : P (-(-a * b)) := by
  rw [neg_mul]
  rw [neg_neg]
  exact h

/-! ### R37. `mul_comm` · `a * b = b * a` (rewrites the first product it finds) -/
example {α : Type} [CommRing α] (a b : α) (P : α → Prop) (h : P (b * a)) : P (a * b) := by
  rw [mul_comm]
  exact h

/-! ### R38. `refine ⟨x₁, x₂, ?_⟩` · goal: an `∃` with the witnesses chosen now -/
example (P : ℝ → ℝ → Prop) (h : P 1 2) : ∃ a b : ℝ, P a b := by
  refine ⟨1, 2, ?_⟩
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. One entry of `M * N = 1` as an equation of numbers: R2, R3 -/
example (M N : Matrix (Fin 2) (Fin 2) ℂ) (h : M * N = 1) : M 0 0 * N 0 1 + M 0 1 * N 1 1 = 0 := by
  have e := congrFun (congrFun h 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e
  exact e

/-! ### W2. Two phase gates multiply by adding angles: R12, R14, then merge with R15 -/
example (x y : ℂ) :
    !![Complex.exp x, 0; 0, 1] * !![Complex.exp y, 0; 0, 1] = !![Complex.exp (x + y), 0; 0, 1] := by
  rw [Matrix.mul_fin_two]
  simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one]
  rw [← Complex.exp_add]

/-! ### W3. Polar form of `z²`: R23, R22, R27, then R34 and R15 -/
example (z : ℂ) : z * z = ↑(‖z‖ ^ 2) * Complex.exp (↑(2 * z.arg) * I) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
  push_cast
  rw [two_mul, add_mul, Complex.exp_add]
  ring

/-! ### W4. A phase shifted by `2π` is unchanged: R27, R34, R15, then `Complex.exp_two_pi_mul_I` -/
example (x : ℝ) : Complex.exp (↑(x + 2 * Real.pi) * I) = Complex.exp (↑x * I) := by
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I]
  ring

end H087Guide
