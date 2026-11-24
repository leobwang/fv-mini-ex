/- Guide for M176 (Causal character is scale invariant).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` or `k` in an entry is only there to finish the example; it shows what the goal became.
`G : Prop` is a goal the entry does not touch.
Part W: worked combinations on objects that are NOT the exercise's (`2 • p`, `3 • q`, a sign function
`sign3` on ℝ).
Assumed: Lean basics (E001–E033).
-/
import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.Basic

open Lorentz Vector

namespace M176Guide

/-! # Part R · Reference entries -/

/-! ## Pulling a scalar out of the Minkowski product -/

/-! ### R1. `map_smul` · `f (c • x) = c • f x` · goal: `⟪c • p, q⟫ₘ` or `⟪p, c • q⟫ₘ` → `c` pulled out
`⟪p, q⟫ₘ` prints as `(minkowskiProduct p) q`. In the first slot the scalar lands on the linear map
`minkowskiProduct p` (then R2); in the second slot it lands on the number directly. -/
example {d : ℕ} (c : ℝ) (p q : Lorentz.Vector d) (P : ℝ → Prop)
    (h : P ((c • minkowskiProduct p) q)) : P ⟪c • p, q⟫ₘ := by
  rw [map_smul]
  exact h

example {d : ℕ} (c : ℝ) (p q : Lorentz.Vector d) (P : ℝ → Prop)
    (h : P (c • (minkowskiProduct p) q)) : P ⟪p, c • q⟫ₘ := by
  rw [map_smul]
  exact h

/-! ### R2. `smul_apply` · `(c • f) x = c • f x` · goal: a scaled linear map applied → scale the value
(`ContinuousLinearMap.smul_apply` is the deprecated old name.) -/
example {d : ℕ} (c : ℝ) (p q : Lorentz.Vector d) (P : ℝ → Prop)
    (h : P (c • (minkowskiProduct p) q)) : P ((c • minkowskiProduct p) q) := by
  rw [smul_apply]
  exact h

/-! ### R3. `smul_eq_mul` · `a • b = a * b` · goal: `•` between two numbers → `*` -/
example {α : Type} [Mul α] (a b : α) (P : α → Prop) (h : P (a * b)) : P (a • b) := by
  rw [smul_eq_mul]
  exact h

/-! ### R4. `ring` after `simp [map_smul]` · closes `c * (c * x) = c ^ 2 * x`
`simp` applies R1–R3 by itself and leaves nested products, never a power. -/
example (c x : ℝ) : c * (c * x) = c ^ 2 * x := by
  ring

/-! ### R5. `positivity` · closes `0 < e` / `0 ≤ e` from the shape of `e`; uses `c ≠ 0` from the context -/
example (c : ℝ) (hc : c ≠ 0) : 0 < c ^ 2 := by
  positivity

/-! ## Opening `causalCharacter` -/

/-! ### R6. `unfold causalCharacter` · goal: `causalCharacter p` → its body, a nested `if`
The body starts with `have v0 := ⟪p, p⟫ₘ;`, a local name for the product (not a hypothesis: `intro`
cannot take it; `simp` substitutes it away). -/
example {d : ℕ} (p : Lorentz.Vector d) (P : CausalCharacter → Prop)
    (h : P (if ⟪p, p⟫ₘ = 0 then .lightLike else if 0 < ⟪p, p⟫ₘ then .timeLike else .spaceLike)) :
    P (causalCharacter p) := by
  unfold causalCharacter
  exact h

/-! ### R7. `rw [hab]` inside `have v := a; if …` · goal: `a` → `b` in the bound value
The bound value is an ordinary subterm, so `rw` reaches it; the `if` below it is untouched. -/
example {α : Type} (a b : ℝ) (x y : α) (P : α → Prop) (hab : a = b)
    (h : P (have v := b; if v = 0 then x else y)) : P (have v := a; if v = 0 then x else y) := by
  rw [hab]
  exact h

/-! ## Deciding the `if`s -/

/-! ### R8. `by_cases h0 : Q` · goal list: one goal → a goal with `h0 : Q` and one with `h0 : ¬Q` -/
example (a : ℝ) (G : Prop) (k0 : a = 0 → G) (k1 : ¬a = 0 → G) : G := by
  by_cases h0 : a = 0
  exact k0 h0
  exact k1 h0

/-! ### R9. `simp [h0]` on `if Q then x else y` · goal: picks the branch `h0` decides (`if_pos`, `if_neg`)
Give `simp` the condition exactly as it appears in the `if`, or its negation. -/
example {α : Type} (a : ℝ) (x y : α) (P : α → Prop) (h0 : a = 0) (h : P x) :
    P (if a = 0 then x else y) := by
  simp [h0]
  exact h

example {α : Type} (a : ℝ) (x y : α) (P : α → Prop) (h0 : ¬a = 0) (h : P y) :
    P (if a = 0 then x else y) := by
  simp [h0]
  exact h

/-! ## Facts about signs of products -/

/-! ### R10. `LT.lt.ne'` · `b < a → a ≠ b` · context gains `a ≠ 0` from `h : 0 < a`
Dot notation: `h.ne'` means `LT.lt.ne' h` because `h : 0 < a` has type `LT.lt 0 a`. -/
example (a : ℝ) (h : 0 < a) (G : Prop) (k : a ≠ 0 → G) : G := by
  have ha := h.ne'
  exact k ha

/-! ### R11. `mul_ne_zero` · `a ≠ 0 → b ≠ 0 → a * b ≠ 0` · context gains `a * b ≠ 0` -/
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (G : Prop) (k : a * b ≠ 0 → G) : G := by
  have hab := mul_ne_zero ha hb
  exact k hab

/-! ### R12. `mul_pos` · `0 < a → 0 < b → 0 < a * b` · context gains `0 < a * b` -/
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (G : Prop) (k : 0 < a * b → G) : G := by
  have hab := mul_pos ha hb
  exact k hab

/-! ### R13. `LT.lt.le` · `a < b → a ≤ b` · context gains `0 ≤ a` from `h : 0 < a` (write `h.le`) -/
example (a : ℝ) (h : 0 < a) (G : Prop) (k : 0 ≤ a → G) : G := by
  have ha := h.le
  exact k ha

/-! ### R14. `pos_of_mul_pos_right` · `0 < a * b → 0 ≤ a → 0 < b` · context gains `0 < b` -/
example (a b : ℝ) (hab : 0 < a * b) (ha : 0 ≤ a) (G : Prop) (k : 0 < b → G) : G := by
  have hb := pos_of_mul_pos_right hab ha
  exact k hb

/-! ### R15. Proving `¬Q`: `¬Q` is `Q → False`, so `fun h' => …` (term) or `intro h'` (tactic)
· goal `¬Q` → context gains `h' : Q`, goal `False` -/
example (Q R : Prop) (hr : ¬R) (f : Q → R) : ¬Q := by
  intro h'
  exact hr (f h')

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `simp [map_smul]` (R1–R3) leaves nested products; `ring` (R4) finishes -/
example {d : ℕ} (p q : Lorentz.Vector d) : ⟪(2 : ℝ) • p, (3 : ℝ) • q⟫ₘ = 6 * ⟪p, q⟫ₘ := by
  simp [map_smul]
  ring

/-- A sign function with the same `if` shape as `causalCharacter`. -/
noncomputable def sign3 (x : ℝ) : ℤ := if x = 0 then 0 else if 0 < x then 1 else -1

/-! ### W2. Unfold (R6), prove the two conditions' truth values first (R5), then one `simp` (R9) -/
example (x : ℝ) : sign3 (x ^ 2 + 1) = 1 := by
  unfold sign3
  have h1 : x ^ 2 + 1 ≠ 0 := by positivity
  have h2 : 0 < x ^ 2 + 1 := by positivity
  simp [h1, h2]

/-! ### W3. Nested `by_cases` (R8) on both conditions, `simp` (R9) in each of the three cases -/
example (x : ℝ) : sign3 x ≠ 2 := by
  unfold sign3
  by_cases h0 : x = 0
  · simp [h0]
  · by_cases hp : 0 < x
    · simp [h0, hp]
    · simp [h0, hp]

/-! ### W4. A negative fact from R15 and R14: if `x` is not positive, neither is `3 * x` -/
example (x : ℝ) (hp : ¬0 < x) : ¬0 < 3 * x :=
  fun h' => hp (pos_of_mul_pos_right h' (by norm_num))

end M176Guide
