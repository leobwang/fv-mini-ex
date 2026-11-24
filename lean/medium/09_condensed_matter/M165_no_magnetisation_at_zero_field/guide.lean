/- Guide for M165 (No magnetisation at zero field).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (negation on `ℤ`-valued vectors,
an odd function on a type with `-`).
Assumed: Lean basics.
-/
import Mathlib

namespace M165Guide

/-! # Part R · Reference entries -/

/-! ## Building a bijection (`Equiv`) -/

/-! ### R1. `let e : α ≃ α := ⟨f, g, l, r⟩` · context gains `e`, a named bijection; goal unchanged
`α ≃ β` is a structure: `toFun : α → β`, `invFun : β → α`, `left_inv : ∀ x, g (f x) = x`,
`right_inv : ∀ y, f (g y) = y`. Here both laws are `neg_neg : - -x = x`. -/
example {α : Type} [InvolutiveNeg α] (G : Prop) (hG : G) : G := by
  let e : α ≃ α := ⟨fun x => -x, fun x => -x, neg_neg, neg_neg⟩
  exact hG

/-! ### R2. `funext i` · goal: equation of functions `F = G` → context gains `i`, goal `F i = G i`
This is the shape of a law of an `Equiv` between function types: `invFun (toFun v) = v`. -/
example {ι : Type} (v : ι → ℤ) : (fun v i => -v i) ((fun v i => -v i) v) = v := by
  funext i
  simp

/-! ### R3. `Bool.not_not` · `(!!b) = b` · goal: double negation of a `Bool` removed (`simp` uses it) -/
example (b : Bool) (P : Bool → Prop) (h : P b) : P (!!b) := by
  rw [Bool.not_not]
  exact h

/-! ## Facts about a `Bool`-valued `if` -/

/-! ### R4. `cases b` (`b : Bool`) · context loses `b`; goal list: one goal for `false`, one for `true` -/
example (x y : ℝ) (P : ℝ → Prop) (hx : P x) (hy : P y) (b : Bool) : P (if b then x else y) := by
  cases b
  exacts [hy, hx]

/-! ### R5. `simp` on `if false = true then x else y` · goal: the `if` with a literal condition → a branch
After `cases b`, `if b then …` shows as `if false = true then …`; `simp` picks the branch. -/
example (x y : ℝ) (P : ℝ → Prop) (h : P y) : P (if false = true then x else y) := by
  simp
  exact h

/-! ## Evaluating a hand-built `Equiv` -/

/-! ### R6. `simp only [e]`, then `Equiv.coe_fn_mk` · goal: `e x` → the body of its `toFun` at `x`
`simp only [e]` unfolds the `let`; `Equiv.coe_fn_mk : ⇑⟨f, g, l, r⟩ = f` then applies the function. -/
example {α : Type} [InvolutiveNeg α] (P : α → Prop) (x : α) (h : P (-x)) : P (-x) := by
  let e : α ≃ α := ⟨fun x => -x, fun x => -x, neg_neg, neg_neg⟩
  show P (e x)
  simp only [e]
  simp only [Equiv.coe_fn_mk]
  exact h

/-! ### R7. `simp only [hf]` under a `∑` · goal: rewrite inside the summand (`rw [hf]` fails here)
The summand mentions the bound variable `i`; `rw` cannot rewrite such a subterm, `simp` can. -/
example {ι α : Type} [Fintype ι] (f : α → ℝ) (g : α → α) (u : ι → α)
    (hf : ∀ a, f (g a) = -f a) (P : ℝ → Prop) (h : P (∑ i, -f (u i))) :
    P (∑ i, f (g (u i))) := by
  simp only [hf]
  exact h

/-! ## Signs -/

/-! ### R8. `neg_mul_neg` · `-a * -b = a * b` · goal: two signs cancel -/
example {α : Type} [Mul α] [HasDistribNeg α] (a b : α) (P : α → Prop) (h : P (a * b)) :
    P (-a * -b) := by
  rw [neg_mul_neg]
  exact h

/-! ### R9. `neg_mul` · `-a * b = -(a * b)` · goal: a sign pulled out of a product -/
example {α : Type} [Mul α] [HasDistribNeg α] (a b : α) (P : α → Prop) (h : P (-(a * b))) :
    P (-a * b) := by
  rw [neg_mul]
  exact h

/-! ## Reindexing a sum -/

/-! ### R10. `have h := Equiv.sum_comp e g` · context gains `h : ∑ i, g (e i) = ∑ i, g i`
A bijection `e` only permutes the summands, so the sum is unchanged. -/
example {ι M : Type} [Fintype ι] [AddCommMonoid M] (e : ι ≃ ι) (g : ι → M) (G : Prop)
    (hG : G) : G := by
  have h := Equiv.sum_comp e g
  exact hG

/-! ### R11. `simp only [hg] at h` · context: `h` rewritten (inside its sums too); goal unchanged -/
example {ι : Type} [Fintype ι] (e : ι ≃ ι) (g : ι → ℝ) (hg : ∀ i, g (e i) = -g i)
    (h : ∑ i, g (e i) = ∑ i, g i) : ∑ i, -g i = ∑ i, g i := by
  simp only [hg] at h
  exact h

/-! ### R12. `Finset.sum_neg_distrib` · `∑ i ∈ s, -f i = -∑ i ∈ s, f i` · a minus sign leaves the sum -/
example {ι M : Type} [Fintype ι] [AddCommGroup M] (f : ι → M) (P : M → Prop) (h : P (-∑ i, f i)) :
    P (∑ i, -f i) := by
  rw [Finset.sum_neg_distrib]
  exact h

/-! ### R13. `linarith` · closes a linear (in)equality over `ℝ` from hypotheses: here `S = 0` from `-S = S` -/
example (S : ℝ) (h : -S = S) : S = 0 := by
  linarith

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A bijection of function types, laws by `funext` (R1, R2): pointwise negation of vectors -/
example {ι : Type} : (ι → ℤ) ≃ (ι → ℤ) :=
  ⟨fun v i => -v i, fun v i => -v i, fun v => by funext i; simp, fun v => by funext i; simp⟩

/-! ### W2. An odd function sums to zero (R1, R6, R10, R11, R12, R13) -/
example {α : Type} [Fintype α] [InvolutiveNeg α] (f : α → ℝ) (hf : ∀ x, f (-x) = -f x) :
    ∑ x, f x = 0 := by
  let e : α ≃ α := ⟨fun x => -x, fun x => -x, neg_neg, neg_neg⟩
  have hg : ∀ x, f (e x) = -f x := by
    intro x
    simp only [e, Equiv.coe_fn_mk]
    exact hf x
  have h := Equiv.sum_comp e f
  simp only [hg] at h
  simp only [Finset.sum_neg_distrib] at h
  linarith

/-! ### W3. An invariant under a sign flip: each product picks up two signs (R7, R8) -/
example {ι : Type} [Fintype ι] (a b : ι → ℝ) :
    ∑ i, -a i * -b i = ∑ i, a i * b i := by
  simp only [neg_mul_neg]

end M165Guide
