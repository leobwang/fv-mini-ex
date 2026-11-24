/- Guide for H080 (The swap test).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other circuits, other sums).
Assumed: Lean basics (E001–E033).
-/
import QuantumInfo.States.Pure.Braket

open Braket

namespace H080Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · one output amplitude of a circuit -/

/-! ### R1. `simp only [f]` for `f := fun p => …` applied to a pair · goal: name → body, `(a, b).2` → `b`
After unfolding, `simp only` also β-reduces `(fun p => …) (a, b)` and evaluates the projections. -/
def swapArg {α β : Type} (v : α × β → ℂ) : β × α → ℂ := fun p => v (p.2, p.1)

example {α β : Type} (v : α × β → ℂ) (a : α) (b : β) (P : ℂ → Prop) (h : P (v (a, b))) :
    P (swapArg v (b, a)) := by
  simp only [swapArg]
  exact h

/-! ### R2. `simp` on `if`s over `Fin 2` · goal: `if True then x else y` → `x`, `if (1 : Fin 2) = 0 …` → the
else branch (simp decides `1 = 0` is false in `Fin 2`), then `-1 * x` → `-x` -/
example (a b : ℂ) (P : ℂ → Prop) (h : P (a + -b)) :
    P ((if True then a else b) + (if (1 : Fin 2) = 0 then 1 else -1) * b) := by
  simp
  exact h

/-! ### R3. `mul_inv` · `(a * b)⁻¹ = a⁻¹ * b⁻¹`; used right to left: `rw [← mul_inv]` -/
example {α : Type} [DivisionCommMonoid α] (a b : α) (P : α → Prop) (h : P (a * b)⁻¹) :
    P (a⁻¹ * b⁻¹) := by
  rw [← mul_inv]
  exact h

/-! ### R4. `Complex.ofReal_mul` · `↑(x * y) = ↑x * ↑y`; right to left moves `*` inside the cast -/
example (x y : ℝ) (P : ℂ → Prop) (h : P ↑(x * y)) : P (↑x * ↑y) := by
  rw [← Complex.ofReal_mul]
  exact h

/-! ### R5. `Real.mul_self_sqrt` · `0 ≤ x → √x * √x = x` · goal rewritten, plus side goal `0 ≤ x`
Write `rw [Real.mul_self_sqrt (by norm_num)]` to close the side goal on the spot. -/
example (x : ℝ) (P : ℝ → Prop) (h : P x) (hx : 0 ≤ x) : P (√x * √x) := by
  rw [Real.mul_self_sqrt]
  exact h
  exact hx

/-! ### R6. `norm_num` · closes (or simplifies) a goal made of numerals, `⁻¹`, `/` and casts of numerals -/
example : ((5 : ℝ) : ℂ)⁻¹ = 1 / 5 := by norm_num

/-! ### R7. `linear_combination c * h` · closes `L = R` when `L - R - c * (lhs h - rhs h)` is 0 by `ring` -/
example (s t a : ℂ) (h : s * s = t) : s * (s * a) = t * a := by
  linear_combination a * h

/-! ## Part 2 · a norm sum over `d × d` factorises -/

/-! ### R8. `Complex.normSq_mul` · `normSq (z * w) = normSq z * normSq w` -/
example (z w : ℂ) (P : ℝ → Prop) (h : P (Complex.normSq z * Complex.normSq w)) :
    P (Complex.normSq (z * w)) := by
  rw [Complex.normSq_mul]
  exact h

/-! ### R9. `Fintype.sum_prod_type` · goal: a sum over pairs → a double sum -/
example {α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (f : α → β → M) (P : M → Prop)
    (h : P (∑ a, ∑ b, f a b)) : P (∑ q : α × β, f q.1 q.2) := by
  simp only [Fintype.sum_prod_type]
  exact h

/-! ### R10. `Finset.sum_mul_sum`, right to left · goal: `∑ a, ∑ b, f a * g b` → `(∑ f) * (∑ g)` -/
example {α β R : Type} [Fintype α] [Fintype β] [NonUnitalNonAssocSemiring R] (f : α → R) (g : β → R)
    (P : R → Prop) (h : P ((∑ a, f a) * ∑ b, g b)) : P (∑ a, ∑ b, f a * g b) := by
  simp only [← Finset.sum_mul_sum]
  exact h

/-! ### R11. `Ket.normalized` · `∑ x, normSq (ψ x) = 1` for a ket `ψ : Ket d` -/
example {d : Type} [Fintype d] (ψ : Ket d) (P : ℝ → Prop) (h : P 1) :
    P (∑ x, Complex.normSq (ψ x)) := by
  rw [Ket.normalized]
  exact h

/-! ### R12. `mul_one` · `a * 1 = a` -/
example {α : Type} [MulOneClass α] (a : α) (P : α → Prop) (h : P a) : P (a * 1) := by
  rw [mul_one]
  exact h

/-! ## Part 3 · the cross sum is `|⟨ψ|φ⟩|²` -/

/-! ### R13. `Braket.dot` · goal: `〈ψ‖φ〉` (printed `dot (↑ψ) φ`) → `∑ x, ↑ψ x * φ x` -/
example {d : Type} [Fintype d] (ψ φ : Ket d) (P : ℂ → Prop) (h : P (∑ x, (Ket.to_bra ψ).vec x * φ x)) :
    P 〈ψ‖φ〉 := by
  simp only [Braket.dot]
  exact h

/-! ### R14. `map_sum` · `conj (∑ i, f i) = ∑ i, conj (f i)` (any additive map, here `starRingEnd ℂ`) -/
example {ι : Type} [Fintype ι] (f : ι → ℂ) (P : ℂ → Prop) (h : P (∑ i, starRingEnd ℂ (f i))) :
    P (starRingEnd ℂ (∑ i, f i)) := by
  simp only [map_sum]
  exact h

/-! ### R15. `Finset.sum_mul_sum`, left to right · goal: `(∑ f) * (∑ g)` → `∑ a, ∑ b, f a * g b` -/
example {α β R : Type} [Fintype α] [Fintype β] [NonUnitalNonAssocSemiring R] (f : α → R) (g : β → R)
    (P : R → Prop) (h : P (∑ a, ∑ b, f a * g b)) : P ((∑ a, f a) * ∑ b, g b) := by
  simp only [Finset.sum_mul_sum]
  exact h

/-! ### R16. `refine Finset.sum_congr rfl fun i _ => ?_` · goal `∑ f = ∑ g` → context gains `i`, goal `f i = g i` -/
example {ι M : Type} [Fintype ι] [AddCommMonoid M] (f g : ι → M) (h : ∀ i, f i = g i) :
    ∑ i, f i = ∑ i, g i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  exact h i

/-! ### R17. `simp [Ket.to_bra, Bra.apply]` · goal: an amplitude `↑ψ x` of the bra `↑ψ` → `conj (ψ x)`
You never type `↑ψ x` yourself: it appears when R13 unfolds `〈ψ‖φ〉`. Typed by hand, `(ψ : Bra d) x`
makes Lean read `x` as a ket (a bra can also be applied to a ket, giving `〈ψ‖x〉`), so this example has
to name the "bra as a function on `d`" coercion explicitly. -/
example {d : Type} [Fintype d] (ψ : Ket d) (x : d) (P : ℂ → Prop) (h : P (starRingEnd ℂ (ψ x))) :
    P (@DFunLike.coe (Bra d) d (fun _ => ℂ) Braket.instFunLikeBra (ψ : Bra d) x) := by
  simp [Ket.to_bra, Bra.apply]
  exact h

/-! ### R18. `Ket.apply` · `ψ x = ψ.vec x`: the amplitude, written through the underlying vector -/
example {d : Type} [Fintype d] (ψ : Ket d) (x : d) (P : ℂ → Prop) (h : P (ψ.vec x)) : P (ψ x) := by
  rw [Ket.apply]
  exact h

/-! ### R19. `map_mul` · `conj (a * b) = conj a * conj b` (`simp` applies it by itself) -/
example (a b : ℂ) (P : ℂ → Prop) (h : P (starRingEnd ℂ a * starRingEnd ℂ b)) :
    P (starRingEnd ℂ (a * b)) := by
  rw [map_mul]
  exact h

/-! ### R20. `Complex.re_sum` · `(∑ i, f i).re = ∑ i, (f i).re`; right to left pulls `.re` out of the sum -/
example {ι : Type} [Fintype ι] (f : ι → ℂ) (P : ℝ → Prop) (h : P (∑ i, f i).re) :
    P (∑ i, (f i).re) := by
  rw [← Complex.re_sum]
  exact h

/-! ### R21. `Complex.normSq_eq_conj_mul_self` · `↑(normSq z) = conj z * z`; right to left -/
example (z : ℂ) (P : ℂ → Prop) (h : P ↑(Complex.normSq z)) : P (starRingEnd ℂ z * z) := by
  rw [← Complex.normSq_eq_conj_mul_self]
  exact h

/-! ### R22. `Complex.ofReal_re` · `(↑r).re = r`: the real part of a real number cast into `ℂ` -/
example (r : ℝ) (P : ℝ → Prop) (h : P r) : P (r : ℂ).re := by
  rw [Complex.ofReal_re]
  exact h

/-! ### R23. `Complex.sq_norm` · `‖z‖ ^ 2 = normSq z` -/
example (z : ℂ) (P : ℝ → Prop) (h : P (Complex.normSq z)) : P (‖z‖ ^ 2) := by
  rw [Complex.sq_norm]
  exact h

/-! ## Part 4 · assembling the probability -/

/-! ### R24. `Complex.normSq_add` · `normSq (z + w) = normSq z + normSq w + 2 * (z * conj w).re` -/
example (z w : ℂ) (P : ℝ → Prop)
    (h : P (Complex.normSq z + Complex.normSq w + 2 * (z * starRingEnd ℂ w).re)) :
    P (Complex.normSq (z + w)) := by
  rw [Complex.normSq_add]
  exact h

/-! ### R25. `norm_num` on `normSq` of a numeral · goal: `normSq (1 / 2)` → `1 / 4`
On a larger goal `norm_num` also splits every other `normSq (a * b)` into `normSq a * normSq b` and
expands `.re` of a product into real and imaginary parts; `ring` then finishes. -/
example (P : ℝ → Prop) (h : P (1 / 4)) : P (Complex.normSq (1 / 2)) := by
  norm_num
  exact h

/-! ### R26. `Fintype.sum_equiv (Equiv.prodComm α β) _ _ fun _ => rfl` · closes `∑ over α × β = ∑ over β × α`
`Equiv.prodComm α β : α × β ≃ β × α` is the bijection `(a, b) ↦ (b, a)`. `Fintype.sum_equiv e f g hfg`
proves `∑ x, f x = ∑ y, g y` from `hfg : ∀ x, f x = g (e x)`; here `hfg` holds by `rfl`. -/
example {α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (f : α → β → M) :
    ∑ q : α × β, f q.1 q.2 = ∑ q : β × α, f q.2 q.1 := by
  exact Fintype.sum_equiv (Equiv.prodComm α β) _ _ fun _ => rfl

/-! ### R27. `simp only [e]` with `e : ∀ q, f q = g q` · goal: rewrites inside a `∑` (under the binder),
where `rw [e]` fails -/
example {ι : Type} [Fintype ι] (f g : ι → ℝ) (e : ∀ q, f q = g q) (P : ℝ → Prop)
    (h : P (∑ q, g q)) : P (∑ q, f q) := by
  simp only [e]
  exact h

/-! ### R28. `Finset.sum_div` · `(∑ i, f i) / a = ∑ i, f i / a`; right to left pulls `/ a` out -/
example {ι : Type} [Fintype ι] (f : ι → ℝ) (a : ℝ) (P : ℝ → Prop) (h : P ((∑ i, f i) / a)) :
    P (∑ i, f i / a) := by
  simp only [← Finset.sum_div]
  exact h

/-! ### R29. `Finset.sum_add_distrib` · `∑ i, (f i + g i) = ∑ i, f i + ∑ i, g i` -/
example {ι M : Type} [Fintype ι] [AddCommMonoid M] (f g : ι → M) (P : M → Prop)
    (h : P (∑ i, f i + ∑ i, g i)) : P (∑ i, (f i + g i)) := by
  simp only [Finset.sum_add_distrib]
  exact h

/-! ### R30. `Finset.mul_sum` · `a * ∑ i, f i = ∑ i, a * f i`; right to left pulls `a *` out -/
example {ι : Type} [Fintype ι] (f : ι → ℝ) (a : ℝ) (P : ℝ → Prop) (h : P (a * ∑ i, f i)) :
    P (∑ i, a * f i) := by
  simp only [← Finset.mul_sum]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A two-qubit circuit amplitude: unfold (R1), clean the `if`s (R2), finish with a √3 fact (R7)
A state is a function `Fin 2 × Fin 2 → ℂ`. `mixA` is a √3-scaled butterfly on the first qubit and `start`
puts amplitude `a` on first qubit 0 and `b` on first qubit 1. -/
noncomputable def mixA (v : Fin 2 × Fin 2 → ℂ) : Fin 2 × Fin 2 → ℂ :=
  fun p => (Real.sqrt 3 : ℂ)⁻¹ * (v (0, p.2) + (if p.1 = 0 then 1 else -1) * v (1, p.2))

def start (a b : ℂ) : Fin 2 × Fin 2 → ℂ := fun p => if p.1 = 0 then a else b

example (a b : ℂ) (j : Fin 2) : mixA (mixA (start a b)) (0, j) = 2 / 3 * a := by
  have h3 : (Real.sqrt 3 : ℂ)⁻¹ * (Real.sqrt 3 : ℂ)⁻¹ = 1 / 3 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  simp only [mixA, start]
  simp
  linear_combination (2 * a) * h3

/-! ### W2. A factorised norm sum (R8, R9, R10, R11, R12) on a ket over `d` and one over `e` -/
example {d e : Type} [Fintype d] [Fintype e] (ψ : Ket d) (χ : Ket e) :
    ∑ q : d × e, Complex.normSq (ψ q.1) * Complex.normSq (χ q.2) = 1 := by
  simp only [Fintype.sum_prod_type]
  simp only [← Finset.sum_mul_sum]
  simp only [Ket.normalized]
  simp only [mul_one]

/-! ### W3. A double sum against a product of sums, term by term (R15, R16 twice, `ring`) -/
example {ι : Type} [Fintype ι] (a b : ι → ℂ) :
    ∑ i, ∑ j, b j * a i = (∑ i, a i) * ∑ j, b j := by
  simp only [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ### W4. `.re` of `conj z * z` is `‖z‖ ^ 2` (R21, R22, R23) -/
example (z : ℂ) : (starRingEnd ℂ z * z).re = ‖z‖ ^ 2 := by
  rw [← Complex.normSq_eq_conj_mul_self]
  rw [Complex.ofReal_re]
  rw [Complex.sq_norm]

/-! ### W5. Rewrite under `∑`, then pull `/` and `*` out of the sums (R27, R28, R29, R30) -/
example {ι : Type} [Fintype ι] (f g : ι → ℝ) (u : ι → ℝ) (e : ∀ i, u i = (f i + 2 * g i) / 4) :
    ∑ i, u i = (∑ i, f i + 2 * ∑ i, g i) / 4 := by
  simp only [e]
  simp only [← Finset.sum_div]
  simp only [Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]

end H080Guide
