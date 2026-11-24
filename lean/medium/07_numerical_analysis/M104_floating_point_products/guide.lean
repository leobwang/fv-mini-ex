/- Guide for M104 (Floating-point products).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (another recursive list function,
additive instead of relative errors).
Assumed: Lean basics.
-/
import Mathlib

namespace M104Guide

/-! # Part R · Reference entries -/

/-! ## Induction on a list and the empty-list case -/

/-! ### R1. `induction xs with | nil => … | cons x xs ih => …` · goal list: one goal per constructor
`?_` leaves a case open, so here both cases show up as goals; in a proof you write the case's tactics
after `=>`. In `cons`, the context gains the head `x`, the tail `xs`, and `ih`: the goal for the tail. -/
example (P : List ℝ → Prop) (h0 : P []) (hs : ∀ x xs, P xs → P (x :: xs)) (xs : List ℝ) : P xs := by
  induction xs with
    | nil => ?_
    | cons x xs ih => ?_
  · exact h0
  · exact hs x xs ih

/-! ### R2. `refine ⟨w, ?_, ?_⟩` · goal `∃ θ, A θ ∧ B θ` → two goals `A w`, `B w`
The witness `w` is chosen now. `exact ⟨w, p, q⟩` is the same with both proofs given on the spot. -/
example (A B : ℝ → Prop) (w : ℝ) (ha : A w) (hb : B w) : ∃ θ, A θ ∧ B θ := by
  refine ⟨w, ?_, ?_⟩
  exacts [ha, hb]

/-! ### R3. `List.length_nil`, `pow_zero`, `sub_self`, `abs_zero` · goal (`simp` applies all four)
`[].length = 0`, `a ^ 0 = 1`, `a - a = 0`, `|0| = 0`. The last `rw` leaves `0 ≤ 0`, which `rw`
closes by itself (it tries `rfl`, and `≤` is reflexive). -/
example (a : ℝ) : |(0 : ℝ)| ≤ a ^ ([] : List ℝ).length - 1 := by
  rw [List.length_nil]
  rw [pow_zero]
  rw [sub_self]
  rw [abs_zero]

/-! ### R4. Unfold a recursive definition: `rw [f]` or `simp [f]` · goal: `f (pattern)` → that clause
`rw [f]` uses the clause whose pattern (`[]` or `x :: xs`) matches the argument in the goal. -/
def f : List ℝ → ℝ
  | [] => 1
  | x :: xs => 2 * x * f xs

example (x : ℝ) (xs : List ℝ) (P : ℝ → Prop) (h : P (2 * x * f xs)) : P (f (x :: xs)) := by
  rw [f]
  exact h

example (P : ℝ → Prop) (h : P 1) : P (f []) := by
  rw [f]
  exact h

/-! ### R5. `List.prod_nil`, `add_zero`, `mul_one` · goal (`simp` applies all three)
`[].prod = 1` (the empty product), `a + 0 = a`, `a * 1 = a`. -/
example (P : ℝ → Prop) (h : P 1) : P (([] : List ℝ).prod * (1 + 0)) := by
  rw [List.prod_nil]
  rw [add_zero]
  rw [mul_one]
  exact h

/-! ## Taking hypotheses apart -/

/-! ### R6. `obtain ⟨θ, hA, hB⟩ := h` · context: `h : ∃ θ, A θ ∧ B θ` → `θ`, `hA : A θ`, `hB : B θ`
The pattern follows the nesting `∃ θ, (A θ ∧ B θ)`. `h` itself leaves the context. -/
example (A B : ℝ → Prop) (G : Prop) (h : ∃ θ, A θ ∧ B θ) (k : ∀ θ, A θ → B θ → G) : G := by
  obtain ⟨θ, hA, hB⟩ := h
  exact k θ hA hB

/-! ### R7. Apply a `∀` hypothesis to a term: `hg t` · context gains the instance for `t`
`hg : Lip c g` is a defined name, but its body starts with `∀ x`, so `hg t` works without unfolding.
`obtain ⟨…⟩ := hg t` (R6) takes the instance apart in the same step. The same works for a theorem
proved earlier in the file: `obtain ⟨…⟩ := my_theorem args`. -/
def Lip (c : ℝ) (g : ℝ → ℝ) : Prop := ∀ x, |g x| ≤ c * |x|

example (c t : ℝ) (g : ℝ → ℝ) (hg : Lip c g) (G : Prop) (k : |g t| ≤ c * |t| → G) : G := by
  have ht := hg t
  exact k ht

/-! ## Inequalities with absolute values -/

/-! ### R8. `calc a ≤ b := p` / `_ ≤ c := q` · goal `a ≤ c` → one goal per step
Each step `_ ≤ c` continues from the previous right side (`_`). The steps are proved by `p`, `q`;
`?_` leaves them as goals, as here. Mixing `=` and `≤` steps is fine. -/
example (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  calc a ≤ b := ?_
    _ ≤ c := ?_
  exacts [hab, hbc]

/-! ### R9. `abs_add_le a b : |a + b| ≤ |a| + |b|` · closes the goal (triangle inequality) -/
example (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  exact abs_add_le a b

/-! ### R10. `abs_mul : |a * b| = |a| * |b|` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (|a| * |b|)) : P |a * b| := by
  rw [abs_mul]
  exact h

/-! ### R11. `gcongr` on a sum · goal `a + c ≤ b + c` → `a ≤ b`
`gcongr` ("generalized congruence") matches the two sides, keeps the common parts, and leaves the
parts that differ as goals. -/
example (a b c : ℝ) : |a + b| + c ≤ |a| + |b| + c := by
  gcongr
  exact abs_add_le a b

/-! ### R12. `gcongr` on a product · goal `a * b ≤ c * d` → side goal `0 ≤ c`
For products it needs `a ≤ c`, `b ≤ d`, `0 ≤ b`, `0 ≤ c`. It closes a goal by a hypothesis in the
context (`hac`, `hbd`) or by `positivity` (`0 ≤ |b|`); whatever is left becomes your goal. -/
example (a b c d : ℝ) (hac : |a| ≤ c) (hbd : |b| ≤ d) : |a| * |b| ≤ c * d := by
  gcongr
  exact le_trans (abs_nonneg a) hac

/-! ### R13. `abs_nonneg a : 0 ≤ |a|` · closes the goal -/
example (a : ℝ) : 0 ≤ |a| := by
  exact abs_nonneg a

/-! ### R14. `le_trans : a ≤ b → b ≤ c → a ≤ c` · goal `a ≤ c` → goals `a ≤ b`, `b ≤ c`
Usually given both proofs at once: `exact le_trans h₁ h₂`. With `apply`, `b` is chosen by
the first proof you give; here it is fixed by `(b := b)`. -/
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  apply le_trans (b := b)
  exacts [h₁, h₂]

/-! ## The power `(1 + u) ^ n` after one more element -/

/-! ### R15. `List.length_cons : (a :: l).length = l.length + 1` · goal -/
example (x : ℝ) (xs : List ℝ) (P : ℕ → Prop) (h : P (xs.length + 1)) : P (x :: xs).length := by
  rw [List.length_cons]
  exact h

/-! ### R16. `pow_succ : a ^ (n + 1) = a ^ n * a` · goal -/
example (a : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (a ^ n * a)) : P (a ^ (n + 1)) := by
  rw [pow_succ]
  exact h

/-! ### R17. `nlinarith` · closes `≤`, `<`, `=` goals that follow from hypotheses by adding them up
It first multiplies everything out, so `A * (1 + v)` becomes `A + A * v`, and treats a product of
unknowns such as `A * v` as one more unknown. `linarith` does the same; `nlinarith` also multiplies
pairs of hypotheses together, which `linarith` never does. -/
example (s p q r A v : ℝ) (h1 : s ≤ p + q + r) (hp : p ≤ A - 1) (hq : q ≤ v)
    (hr : r ≤ (A - 1) * v) : s ≤ A * (1 + v) - 1 := by
  nlinarith

/-! ## Products of lists, and rewriting with an equation proved on the spot -/

/-! ### R18. `List.prod_cons : (a :: l).prod = a * l.prod` · goal -/
example (x : ℝ) (xs : List ℝ) (P : ℝ → Prop) (h : P (x * xs.prod)) : P (x :: xs).prod := by
  rw [List.prod_cons]
  exact h

/-! ### R19. `rw [show a = b by tac]` · goal: rewrite with an equation you prove on the spot
`show a = b by ring` is a term proving `a = b`; `a` must appear literally in the goal. -/
example (a b s : ℝ) (P : ℝ → Prop) (h : P (a * s)) : P (a * (b + s) - a * b) := by
  rw [show a * (b + s) - a * b = a * s by ring]
  exact h

/-! ### R20. `mul_comm : a * b = b * a` · goal: `rw [mul_comm]` swaps the FIRST product it finds
With no arguments it picks the first `_ * _` in the goal (left side first) and swaps every copy of
that product. `rw [mul_comm a b]` names the one you mean. -/
example (a b c : ℝ) (P : ℝ → ℝ → Prop) (h : P (b * a) (c * a)) : P (a * b) (c * a) := by
  rw [mul_comm]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. List induction with a recursive definition: R1, R4, R15, R16, then `ring` -/
def dbl : List ℝ → ℝ
  | [] => 1
  | _ :: xs => 2 * dbl xs

example (xs : List ℝ) : dbl xs = 2 ^ xs.length := by
  induction xs with
    | nil => simp [dbl]
    | cons x xs ih =>
      rw [dbl, ih, List.length_cons, pow_succ]
      ring

/-! ### W2. Composing two ADDITIVE errors: R6 twice, R2, then R8 with R9 and R11-style `gcongr` -/
example (x y z u v : ℝ) (h1 : ∃ δ, |δ| ≤ u ∧ y = x + δ) (h2 : ∃ ε, |ε| ≤ v ∧ z = y + ε) :
    ∃ θ, |θ| ≤ u + v ∧ z = x + θ := by
  obtain ⟨δ, hδ, hy⟩ := h1
  obtain ⟨ε, hε, hz⟩ := h2
  refine ⟨δ + ε, ?_, ?_⟩
  · calc |δ + ε| ≤ |δ| + |ε| := abs_add_le δ ε
      _ ≤ u + v := by gcongr
  · rw [hz, hy]
    ring

/-! ### W3. Pulling an absolute value apart: R19, R10, R20 -/
example (x θ : ℝ) : |x * (2 + θ) - 2 * x| = |θ| * |x| := by
  rw [show x * (2 + θ) - 2 * x = x * θ by ring]
  rw [abs_mul]
  rw [mul_comm]

end M104Guide
