/- Guide for H074 (Least squares and the normal equations).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`G : Prop` is an arbitrary goal, finished with `hG`; it exists only so a new hypothesis can be shown.
Vectors are functions `ι → R` on a finite index type `ι` (`[Fintype ι]`); the exercise uses `Fin n`
and `Fin m`. `R` is any commutative ring (`[CommRing R]`: ℤ, ℚ, ℝ, ℂ); entries about order use `ℝ`.
Part W: worked combinations on objects that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Matrix

namespace H074Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · Moving a matrix across a dot product -/

/-! ### R1. `dotProduct_comm` · `v ⬝ᵥ w = w ⬝ᵥ v` · goal
Bare `rw [dotProduct_comm]` swaps the FIRST dot product it finds (and every identical copy);
`rw [dotProduct_comm v w]` swaps only `v ⬝ᵥ w`. -/
example {ι R : Type} [Fintype ι] [CommRing R] (v w : ι → R) (P : R → Prop) (h : P (w ⬝ᵥ v)) :
    P (v ⬝ᵥ w) := by
  rw [dotProduct_comm]
  exact h

/-! ### R2. `Matrix.dotProduct_mulVec` · `v ⬝ᵥ (A *ᵥ w) = (v ᵥ* A) ⬝ᵥ w` · goal
Lean prints `v ⬝ᵥ (A *ᵥ w)` as `v ⬝ᵥ A *ᵥ w`: `*ᵥ` binds tighter than `⬝ᵥ`. -/
example {ι κ R : Type} [Fintype ι] [Fintype κ] [CommRing R] (v : κ → R) (A : Matrix κ ι R)
    (w : ι → R) (P : R → Prop) (h : P (v ᵥ* A ⬝ᵥ w)) : P (v ⬝ᵥ A *ᵥ w) := by
  rw [dotProduct_mulVec]
  exact h

/-! ### R3. `Matrix.mulVec_transpose` · `Aᵀ *ᵥ x = x ᵥ* A` · goal -/
example {ι κ R : Type} [Fintype ι] [Fintype κ] [CommRing R] (A : Matrix κ ι R) (x : κ → R)
    (P : (ι → R) → Prop) (h : P (x ᵥ* A)) : P (Aᵀ *ᵥ x) := by
  rw [mulVec_transpose]
  exact h

/-! ## Part 2 · Squared norms are nonnegative -/

/-! ### R4. `dotProduct_self_star_nonneg` · `0 ≤ v ⬝ᵥ star v` · context gains the fact -/
example {ι : Type} [Fintype ι] (v : ι → ℝ) (G : Prop) (hG : 0 ≤ v ⬝ᵥ star v → G) : G := by
  have h := dotProduct_self_star_nonneg v
  exact hG h

/-! ### R5. `star_trivial` (what `simpa using e` does with `star` on ℝ) · context: `star v` → `v`
`simpa using e` = simplify `e` and the goal, then `exact e`. -/
example {ι : Type} [Fintype ι] (v : ι → ℝ) (P : (ι → ℝ) → Prop) (G : Prop) (h : P (star v))
    (hG : P v → G) : G := by
  simp only [star_trivial] at h
  exact hG h

/-! ## Part 3 · Expanding a squared residual -/

/-! ### R6. `Matrix.mulVec_add` · `A *ᵥ (x + y) = A *ᵥ x + A *ᵥ y` · goal -/
example {ι κ R : Type} [Fintype ι] [CommRing R] (A : Matrix κ ι R) (x y : ι → R)
    (P : (κ → R) → Prop) (h : P (A *ᵥ x + A *ᵥ y)) : P (A *ᵥ (x + y)) := by
  rw [mulVec_add]
  exact h

/-! ### R7. `rw [show a + c - b = a - b + c by abel]` · goal: regroup a sum of vectors
`abel` closes identities in an additive commutative group (`+`, `-`, `0` only; vectors qualify).
`show T by tac` is a proof of `T` written inline, so `rw` can use it once. -/
example {V : Type} [AddCommGroup V] (a b c : V) (P : V → Prop) (h : P (a - b + c)) :
    P (a + c - b) := by
  rw [show a + c - b = a - b + c by abel]
  exact h

/-! ### R8. `add_dotProduct` · `(u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w` · goal -/
example {ι R : Type} [Fintype ι] [CommRing R] (u v w : ι → R) (P : R → Prop)
    (h : P (u ⬝ᵥ w + v ⬝ᵥ w)) : P ((u + v) ⬝ᵥ w) := by
  rw [add_dotProduct]
  exact h

/-! ### R9. `dotProduct_add` · `u ⬝ᵥ (v + w) = u ⬝ᵥ v + u ⬝ᵥ w` · goal -/
example {ι R : Type} [Fintype ι] [CommRing R] (u v w : ι → R) (P : R → Prop)
    (h : P (u ⬝ᵥ v + u ⬝ᵥ w)) : P (u ⬝ᵥ (v + w)) := by
  rw [dotProduct_add]
  exact h

/-! ### R10. `ring` · closes a commutative-ring identity; each dot product is one unknown
`u ⬝ᵥ w` and `w ⬝ᵥ u` are DIFFERENT unknowns to `ring`: make them equal with R1 first. -/
example (p q r : ℝ) : p + q + (q + r) = p + 2 * q + r := by ring

/-! ## Part 4 · Normal equations ⇔ minimiser -/

/-! ### R11. `constructor` on `↔` · goal list: `A ↔ B` → `A → B` and `B → A` -/
example (A B : Prop) (hab : A → B) (hba : B → A) : A ↔ B := by
  constructor
  exact hab
  exact hba

/-! ### R12. `add_sub_cancel` · `a + (b - a) = b` · context, with `rw … at h` -/
example {V : Type} [AddCommGroup V] (a b : V) (P : V → Prop) (G : Prop) (h : P (a + (b - a)))
    (hG : P b → G) : G := by
  rw [add_sub_cancel] at h
  exact hG h

/-! ### R13. `zero_dotProduct` · `0 ⬝ᵥ v = 0` · goal (here: `at h`) -/
example {ι R : Type} [Fintype ι] [CommRing R] (v : ι → R) (P : R → Prop) (G : Prop)
    (h : P (0 ⬝ᵥ v)) (hG : P 0 → G) : G := by
  rw [zero_dotProduct] at h
  exact hG h

/-! ### R14. `linarith [e]` · closes a linear (in)equality from the hypotheses plus the extra fact `e`
Products and dot products count as single unknowns; `2 * 0` is evaluated. -/
example (a : ℝ) (f : ℝ → ℝ) (hf : ∀ y, 0 ≤ f y) (c : ℝ) (h : c = a + 2 * 0 + f 1) : a ≤ c := by
  linarith [hf 1]

/-! ### R15. `set y := e` · context gains `y : T := e`; every `e` in goal and context becomes `y`
Facts created LATER are not folded back into `y` (see R24). -/
example (f : ℝ → ℝ) (x : ℝ) (P : ℝ → Prop) (h : P (f x)) : P (f x) := by
  set y := f x
  exact h

/-! ### R16. `by_contra hc` · goal `Q` → `False`, context gains `hc : ¬Q` -/
example (Q : Prop) (hQ : ¬¬Q) : Q := by
  by_contra hc
  exact hQ hc

/-! ### R17. `dotProduct_self_eq_zero` · `v ⬝ᵥ v = 0 ↔ v = 0` (over ℝ) · context, with `.mp` -/
example {ι : Type} [Fintype ι] (v : ι → ℝ) (h : v ⬝ᵥ v = 0) (G : Prop) (hG : v = 0 → G) : G := by
  have hv := dotProduct_self_eq_zero.mp h
  exact hG hv

/-! ### R18. `lt_of_le_of_ne` · `a ≤ b → a ≠ b → a < b` · goal list: `a < b` → two goals
`a ≠ b` unfolds to `a = b → False`, so it can be proved by `fun h => …`. -/
example (a b : ℝ) (h1 : a ≤ b) (h2 : a ≠ b) : a < b := by
  refine lt_of_le_of_ne ?_ ?_
  exact h1
  exact h2

/-! ### R19. `positivity` · closes `0 < e` / `0 ≤ e` built from `+ * / ^` and atoms with
sign hypotheses `0 < a`, `0 ≤ b` in the context -/
example (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) : 0 < a / (b + 1) := by positivity

/-! ### R20. `Matrix.mulVec_smul` · `A *ᵥ (c • v) = c • (A *ᵥ v)` · goal -/
example {ι κ R : Type} [Fintype ι] [CommRing R] (A : Matrix κ ι R) (c : R) (v : ι → R)
    (P : (κ → R) → Prop) (h : P (c • A *ᵥ v)) : P (A *ᵥ c • v) := by
  rw [mulVec_smul]
  exact h

/-! ### R21. `smul_dotProduct` · `(c • v) ⬝ᵥ w = c • (v ⬝ᵥ w)` · goal -/
example {ι R : Type} [Fintype ι] [CommRing R] (c : R) (v w : ι → R) (P : R → Prop)
    (h : P (c • (v ⬝ᵥ w))) : P (c • v ⬝ᵥ w) := by
  rw [smul_dotProduct]
  exact h

/-! ### R22. `dotProduct_smul` · `v ⬝ᵥ (c • w) = c • (v ⬝ᵥ w)` · goal -/
example {ι R : Type} [Fintype ι] [CommRing R] (c : R) (v w : ι → R) (P : R → Prop)
    (h : P (c • (v ⬝ᵥ w))) : P (v ⬝ᵥ c • w) := by
  rw [dotProduct_smul]
  exact h

/-! ### R23. `smul_eq_mul` · `a • b = a * b` for two scalars · goal -/
example {R : Type} [CommRing R] (a b : R) (P : R → Prop) (h : P (a * b)) : P (a • b) := by
  rw [smul_eq_mul]
  exact h

/-! ### R24. `change T at h` · context: restate `h` as a definitionally equal `T`
`_` in `T` is copied from `h`. Use it to fold an expression back into a `set` name. -/
example (f : ℝ → ℝ) (x : ℝ) (G : Prop) (hG : ∀ z : ℝ, 0 ≤ z → G) : G := by
  set y := f x
  have h : 0 ≤ f x ^ 2 := sq_nonneg _
  change 0 ≤ y ^ 2 at h
  exact hG _ h

/-! ### R25. `nlinarith` · closes a goal that needs products of hypotheses (nonlinear `linarith`) -/
example (t a b : ℝ) (ht : 0 < t) (h : t * a ≤ t * b) : a ≤ b := by nlinarith

/-! ### R26. `div_mul_eq_mul_div` · `a / b * c = a * c / b` · goal -/
example (a b c : ℝ) (P : ℝ → Prop) (h : P (a * c / b)) : P (a / b * c) := by
  rw [div_mul_eq_mul_div]
  exact h

/-! ### R27. `div_lt_iff₀` · `0 < c → (b / c < a ↔ b < a * c)` · goal: clear a denominator -/
example (a b c : ℝ) (hc : 0 < c) (h : b < a * c) : b / c < a := by
  rw [div_lt_iff₀ hc]
  exact h

/-! ## Part 5 · Uniqueness from injectivity -/

/-! ### R28. `Matrix.mulVec_sub` · `A *ᵥ (x - y) = A *ᵥ x - A *ᵥ y` · goal (here: `at h`) -/
example {ι κ R : Type} [Fintype ι] [CommRing R] (A : Matrix κ ι R) (x y : ι → R)
    (P : (κ → R) → Prop) (G : Prop) (h : P (A *ᵥ (x - y))) (hG : P (A *ᵥ x - A *ᵥ y) → G) : G := by
  rw [mulVec_sub] at h
  exact hG h

/-! ### R29. `sub_eq_zero` · `a - b = 0 ↔ a = b` · context, with `rw … at h` (rewriting by an `↔`) -/
example {V : Type} [AddCommGroup V] (a b : V) (h : a - b = 0) (G : Prop) (hG : a = b → G) : G := by
  rw [sub_eq_zero] at h
  exact hG h

/-! ### R30. `Function.Injective f` applied: `hf h` · context: `f a = f b` gives `a = b`
`Function.Injective f` is `∀ ⦃a b⦄, f a = f b → a = b`; `A.mulVec` is the function `v ↦ A *ᵥ v`. -/
example {α β : Type} (f : α → β) (hf : Function.Injective f) (a b : α) (h : f a = f b) (G : Prop)
    (hG : a = b → G) : G := by
  have e := hf h
  exact hG e

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. ‖u + w‖² for plain vectors: R8, R9, R1 with explicit arguments, R10 -/
example {ι : Type} [Fintype ι] (u w : ι → ℝ) :
    (u + w) ⬝ᵥ (u + w) = u ⬝ᵥ u + 2 * (u ⬝ᵥ w) + w ⬝ᵥ w := by
  simp only [add_dotProduct, dotProduct_add]
  rw [dotProduct_comm w u]
  ring

/-! ### W2. Pulling scalars out of a dot product: R21, R22, R23 together -/
example {ι : Type} [Fintype ι] (c : ℝ) (v : ι → ℝ) :
    (c • v) ⬝ᵥ (c • v) = c * (c * (v ⬝ᵥ v)) := by
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]

/-! ### W3. Injective `B`, equal images: R28, R29, R30 -/
example {ι κ : Type} [Fintype ι] (B : Matrix κ ι ℝ) (hB : Function.Injective B.mulVec)
    (u w : ι → ℝ) (h : B *ᵥ (u - w) = 0) : u = w := by
  rw [mulVec_sub, sub_eq_zero] at h
  exact hB h

end H074Guide
