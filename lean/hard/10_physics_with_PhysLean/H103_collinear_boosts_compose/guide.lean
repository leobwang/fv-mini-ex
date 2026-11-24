/- Guide for H103 (Collinear boosts compose).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other speeds, other functions).
Assumed: Lean basics.
-/
import Physlib.Relativity.LorentzGroup.Boosts.Apply

open Lorentz Vector LorentzGroup Matrix

namespace H103Guide

/-! # Part R · Reference entries -/

/-! ## Inequalities with `|·|` and `/` -/

/-! ### R1. `rw [abs_lt] at *` · `|a| < b ↔ -b < a ∧ a < b` · goal and context
`at *` rewrites the goal and every hypothesis it can; `at h` rewrites only `h`. -/
example (a b c : ℝ) (h : |a| < b) (k : -b < a ∧ a < b → -1 < c ∧ c < 1) : |c| < 1 := by
  rw [abs_lt] at *
  exact k h

/-! ### R2. `nlinarith` · closes a (non)linear inequality over `ℝ`
It multiplies pairs of hypotheses (and splits `∧` hypotheses) before running linear arithmetic. -/
example (a b : ℝ) (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) : a * b < 1 := by
  nlinarith

/-! ### R3. `lt_div_iff₀` · `0 < c → (a < b / c ↔ a * c < b)` · goal: clear a denominator on the right -/
example (a b c : ℝ) (hc : 0 < c) (h : a * c < b) : a < b / c := by
  rw [lt_div_iff₀ hc]
  exact h

/-! ### R4. `div_lt_iff₀` · `0 < c → (b / c < a ↔ b < a * c)` · goal: clear a denominator on the left -/
example (a b c : ℝ) (hc : 0 < c) (h : b < a * c) : b / c < a := by
  rw [div_lt_iff₀ hc]
  exact h

/-! ## The Lorentz factor and square roots -/

/-! ### R5. `unfold γ` · goal: `γ β` → its definition `1 / √(1 - β ^ 2)` -/
example (β : ℝ) (P : ℝ → Prop) (h : P (1 / √(1 - β ^ 2))) : P (γ β) := by
  unfold γ
  exact h

/-! ### R6. `field_simp` · goal: multiply out every denominator it can prove nonzero
It looks for `c ≠ 0` or `0 < c` in the context. Usually followed by `ring`. -/
example (a b c : ℝ) (hc : 0 < c) : a / c + b = (a + b * c) / c := by
  field_simp

example (a b c : ℝ) (hc : c ≠ 0) (h : a = c * b) : a / c = b := by
  field_simp
  exact h

/-! ### R7. `Real.sqrt_div'` · `0 ≤ y → √(x / y) = √x / √y` · goal -/
example (x y : ℝ) (hy : 0 ≤ y) (P : ℝ → Prop) (h : P (√x / √y)) : P √(x / y) := by
  rw [Real.sqrt_div' x hy]
  exact h

/-! ### R8. `positivity` · closes `0 ≤ e` or `0 < e` when `e` is visibly nonnegative (squares, sums, …) -/
example (a b : ℝ) : 0 ≤ (a - b) ^ 2 := by
  positivity

/-! ### R9. `Real.sqrt_sq` · `0 ≤ x → √(x ^ 2) = x` · goal -/
example (x : ℝ) (hx : 0 ≤ x) (P : ℝ → Prop) (h : P x) : P √(x ^ 2) := by
  rw [Real.sqrt_sq hx]
  exact h

/-! ### R10. `Real.sqrt_mul` · `0 ≤ x → √(x * y) = √x * √y` · goal -/
example (x y : ℝ) (hx : 0 ≤ x) (P : ℝ → Prop) (h : P (√x * √y)) : P √(x * y) := by
  rw [Real.sqrt_mul hx]
  exact h

/-! ### R11. `h.le`, `h.ne'` · from `h : 0 < c` get `0 ≤ c` and `c ≠ 0` · context gains facts -/
example (c : ℝ) (h : 0 < c) (P : Prop) (k : 0 ≤ c → c ≠ 0 → P) : P := by
  have h1 : 0 ≤ c := h.le
  have h2 : c ≠ 0 := h.ne'
  exact k h1 h2

/-! ## Group actions -/

/-! ### R12. `SemigroupAction.mul_smul` · `(x * y) • b = x • y • b` · goal: act by a product in two steps
`LorentzGroup d` acts on `Lorentz.Vector d` this way. Write the full name: plain `mul_smul` is
ambiguous under `open Lorentz Vector`. -/
example {α β : Type} [Monoid α] [MulAction α β] (x y : α) (b : β) (P : β → Prop) (h : P (x • y • b)) :
    P ((x * y) • b) := by
  rw [SemigroupAction.mul_smul]
  exact h

/-! ## Equality of Lorentz transformations -/

/-! ### R13. `refine ⟨hp, ?_⟩` on `∃ h : p, Q h` · goal: supply the proof `hp`, keep `Q hp`
The witness is a proof, so the infoview prints it as `⋯`. -/
example (p : Prop) (Q : p → Prop) (hp : p) (k : ∀ h, Q h) : ∃ h : p, Q h := by
  refine ⟨hp, ?_⟩
  exact k hp

/-! ### R14. `apply LorentzGroup.eq_of_mulVec_eq` · goal: `Λ = Λ'` → they agree on every vector
`↑Λ` is the matrix of `Λ`, and `M *ᵥ x` is matrix times column vector. Give `x` its type: under
`open Lorentz` the notation `*ᵥ` also means other products, and a bare `Λ.1 *ᵥ x` is ambiguous. -/
example {d : ℕ} (Λ Λ' : LorentzGroup d) (h : ∀ x : Fin 1 ⊕ Fin d → ℝ, Λ.1 *ᵥ x = Λ'.1 *ᵥ x) :
    Λ = Λ' := by
  apply eq_of_mulVec_eq
  exact h

/-! ### R15. `div_mul_cancel₀` · `b ≠ 0 → a / b * b = a` · context gains the cancellation fact -/
example (a b : ℝ) (hb : 0 < b) (P : Prop) (k : a / b * b = a → P) : P := by
  have h3 : a / b * b = a := div_mul_cancel₀ a hb.ne'
  exact k h3

/-! ### R16. `Lorentz.Vector.smul_eq_mulVec` · `Λ • p = ↑Λ *ᵥ p`; right to left: `rw [← …]` · goal -/
example {d : ℕ} (Λ : LorentzGroup d) (p : Lorentz.Vector d) (P : Lorentz.Vector d → Prop)
    (h : P (Λ • p)) : P (Λ.1 *ᵥ p) := by
  rw [← Lorentz.Vector.smul_eq_mulVec]
  exact h

/-! ### R17. `Lorentz.Vector.boost_toCoord_eq` · goal: `boost i β hβ • p` → its coordinates
Time row `Sum.inl 0`, the boosted axis `Sum.inr i`, and every other axis unchanged. -/
example {d : ℕ} (i : Fin d) (β : ℝ) (hβ : |β| < 1) (p : Lorentz.Vector d)
    (P : Lorentz.Vector d → Prop) (h : ∀ q, P q) : P (boost i β hβ • p) := by
  rw [Lorentz.Vector.boost_toCoord_eq]
  exact h _

/-! ## Comparing vectors coordinate by coordinate -/

/-! ### R18. `funext j` · goal `f = g` (functions) → `f j = g j`, context gains `j` -/
example {d : ℕ} (f g : Fin 1 ⊕ Fin d → ℝ) (h : ∀ j, f j = g j) : f = g := by
  funext j
  exact h j

/-! ### R19. `match j with | Sum.inl 0 => … | Sum.inr k => …` · goal list: one goal per constructor
`Fin 1 ⊕ Fin d` is "time or one of `d` space axes": `Sum.inl 0` is time, `Sum.inr k` is axis `k`. -/
example {d : ℕ} (P : Fin 1 ⊕ Fin d → Prop) (h0 : P (Sum.inl 0)) (hk : ∀ k, P (Sum.inr k))
    (j : Fin 1 ⊕ Fin d) : P j := by
  match j with
    | Sum.inl 0 => exact h0
    | Sum.inr k => exact hk k

/-! The same split as a term with holes, so the infoview shows the goal each branch starts from:
`j` is replaced by the constructor. -/
example {d : ℕ} (P : Fin 1 ⊕ Fin d → Prop) (h0 : P (Sum.inl 0)) (hk : ∀ k, P (Sum.inr k))
    (j : Fin 1 ⊕ Fin d) : P j := by
  refine match j with | Sum.inl 0 => ?_ | Sum.inr k => ?_
  exacts [h0, hk k]

/-! ### R20. `simp only [if_true]` · goal: evaluates `match` on a constructor, applies `fun`s, and
turns `if a = a then x else y` into `x` -/
example {d : ℕ} (k : Fin d) (x y : ℝ) (P : ℝ → Prop) (h : P x) :
    P ((fun j : Fin 1 ⊕ Fin d =>
      match j with
      | Sum.inl 0 => if k = k then x else y
      | Sum.inr _ => y) (Sum.inl 0)) := by
  simp only [if_true]
  exact h

/-! ### R21. `linear_combination e * h` · closes `L = R` when `L - R = e * (h.lhs - h.rhs)` as a ring identity
`ring` does not know `s / t * t = s`; feed it that fact as `h`, scaled by the factor `e` it needs. -/
example (s t u : ℝ) (h : s / t * t = s) : u * (s / t * t) + u = u * s + u := by
  linear_combination u * h

/-! ### R22. `by_cases hj : j = i` · goal list: two goals, with `hj : j = i` and `hj : ¬j = i` -/
example {d : ℕ} (i j : Fin d) (P : Prop) (k1 : j = i → P) (k2 : ¬j = i → P) : P := by
  by_cases hj : j = i
  · exact k1 hj
  · exact k2 hj

/-! ### R23. `subst hj` · context: `hj : j = i` is used up, `i` is replaced by `j` everywhere -/
example {d : ℕ} (i j : Fin d) (P : Fin d → Fin d → Prop) (h : ∀ k, P k k) (hj : j = i) : P j i := by
  subst hj
  exact h j

/-! ### R24. `simp [hj]` with `hj : ¬j = i` · goal: picks the `else` branch of `if j = i then … else …` -/
example {d : ℕ} (i j : Fin d) (hj : ¬j = i) (x y : ℝ) (P : ℝ → Prop) (h : P y) :
    P (if j = i then x else y) := by
  simp [hj]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Clear denominators, then `ring` (R6): a rational identity in `a` -/
example (a : ℝ) : 1 - (2 * a / (1 + a ^ 2)) ^ 2 = ((1 - a ^ 2) / (1 + a ^ 2)) ^ 2 := by
  have h : 0 < 1 + a ^ 2 := by positivity
  field_simp
  ring

/-! ### W2. Square root of a quotient of a product (R7, R8, R9, R10) -/
example (x y t : ℝ) (hx : 0 ≤ x) (ht : 0 < t) : √(x * y / t ^ 2) = √x * √y / t := by
  rw [Real.sqrt_div' _ (by positivity)]
  rw [Real.sqrt_sq ht.le]
  rw [Real.sqrt_mul hx]

/-! ### W3. A coordinatewise identity on `Fin 1 ⊕ Fin d` (R18, R19, R20, R22–R24) -/
def F {d : ℕ} (i : Fin d) (v : Fin 1 ⊕ Fin d → ℝ) : Fin 1 ⊕ Fin d → ℝ := fun j =>
  match j with
  | Sum.inl 0 => 2 * v (Sum.inl 0) + v (Sum.inr i)
  | Sum.inr j => if j = i then 3 * v (Sum.inr i) else v (Sum.inr j)

example {d : ℕ} (i : Fin d) (v : Fin 1 ⊕ Fin d → ℝ) :
    F i (F i v) = fun j =>
      match j with
      | Sum.inl 0 => 4 * v (Sum.inl 0) + 5 * v (Sum.inr i)
      | Sum.inr j => if j = i then 9 * v (Sum.inr i) else v (Sum.inr j) := by
  unfold F
  funext j
  match j with
    | Sum.inl 0 =>
      simp only [if_true]
      ring
    | Sum.inr j =>
      by_cases hj : j = i
      · subst hj
        simp only [if_true]
        ring
      · simp [hj]

/-! ### W4. `linear_combination` against a cancellation fact (R15, R21) -/
example (s t u w : ℝ) (ht : 0 < t) : w * (u - s / t * (t * u)) = w * u * (1 - s) := by
  have h3 : s / t * t = s := div_mul_cancel₀ s ht.ne'
  linear_combination (-(w * u)) * h3

end H103Guide
