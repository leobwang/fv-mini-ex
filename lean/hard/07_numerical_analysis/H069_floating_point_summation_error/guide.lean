/- Guide for H069 (Floating-point summation error).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a tree of naturals, one rounding).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace H069Guide

/-- A binary tree of naturals: the guide's stand-in for an inductive type of your own. -/
inductive Bin where
  | tip (n : ℕ)
  | fork (a b : Bin)

/-- number of tips -/
def Bin.size : Bin → ℕ
  | tip _ => 1
  | fork a b => a.size + b.size

/-! # Part R · Reference entries -/

/-! ## Induction on your own type, unfolding at a constructor -/

/-! ### R1. `induction t with | tip n => _ | fork a b iha ihb => _` · goal list: one goal per constructor
The `fork` goal gets one induction hypothesis per recursive argument. The second example shows the
two goals the infoview prints (`rename_i` only names the variables, as `with` would). -/
example (P : Bin → Prop) (h0 : ∀ n, P (Bin.tip n)) (h1 : ∀ a b, P a → P b → P (a.fork b))
    (t : Bin) : P t := by
  induction t with
    | tip n => exact h0 n
    | fork a b iha ihb => exact h1 a b iha ihb

example (P : Bin → Prop) (h0 : ∀ n, P (Bin.tip n)) (h1 : ∀ a b, P a → P b → P (a.fork b))
    (t : Bin) : P t := by
  induction t
  rename_i n
  exact h0 n
  rename_i a b iha ihb
  exact h1 a b iha ihb

/-! ### R2. `simp only [Bin.size]` · goal: a definition applied to a constructor → that clause's body -/
example (P : ℕ → Prop) (a b : Bin) (h : P (a.size + b.size)) : P (Bin.fork a b).size := by
  simp only [Bin.size]
  exact h

/-! ## Chaining inequalities -/

/-! ### R3. `h₁.trans h₂` (`le_trans`) · `a ≤ b → b ≤ c → a ≤ c`; `refine h₁.trans ?_` leaves `b ≤ c` -/
example {α : Type} [Preorder α] (a b c : α) (hab : a ≤ b) (h : b ≤ c) : a ≤ c := by
  refine hab.trans ?_
  exact h

/-! ### R4. `abs_add_le` · `|a + b| ≤ |a| + |b|` (triangle inequality) -/
example (a b c : ℝ) (h : |a| + |b| ≤ c) : |a + b| ≤ c := by
  refine (abs_add_le a b).trans ?_
  exact h

/-! ### R5. `add_le_add` · `a ≤ b → c ≤ d → a + c ≤ b + d` · goal list: one goal → two -/
example (a b c d : ℝ) (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  refine add_le_add ?_ ?_
  exact h₁
  exact h₂

/-! ## Lists -/

/-! ### R6. `induction xs with | nil => _ | cons x xs ih => _` · goal list: `[]` and `x :: xs` -/
example {α : Type} (P : List α → Prop) (h0 : P []) (h1 : ∀ x xs, P xs → P (x :: xs))
    (xs : List α) : P xs := by
  induction xs with
    | nil => exact h0
    | cons x xs ih => exact h1 x xs ih

example {α : Type} (P : List α → Prop) (h0 : P []) (h1 : ∀ x xs, P xs → P (x :: xs))
    (xs : List α) : P xs := by
  induction xs
  exact h0
  rename_i x xs ih
  exact h1 x xs ih

/-! ### R7. `List.sum_cons`, `List.map_cons`, `List.length_cons` · goal: a list function at `x :: xs` -/
example {α : Type} [AddMonoid α] (x : α) (xs : List α) (P : α → Prop) (h : P (x + xs.sum)) :
    P (x :: xs).sum := by
  rw [List.sum_cons]
  exact h

example {α β : Type} (f : α → β) (x : α) (xs : List α) (P : List β → Prop)
    (h : P (f x :: xs.map f)) : P ((x :: xs).map f) := by
  rw [List.map_cons]
  exact h

example {α : Type} (x : α) (xs : List α) (P : ℕ → Prop) (h : P (xs.length + 1)) :
    P (x :: xs).length := by
  rw [List.length_cons]
  exact h

/-! ## Closing linear goals; absolute value as two inequalities -/

/-! ### R8. `linarith` · closes a linear (in)equality that follows from the hypotheses
`linarith [t₁, t₂]` also uses the facts `t₁, t₂` (proof terms), as if they were hypotheses. -/
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b + 1 ≤ c) : a + 1 ≤ c := by linarith

example (a b : ℝ) (h : |a| ≤ b) : 0 ≤ b + 1 := by linarith [abs_nonneg a]

/-! ### R9. `rw [abs_le] at h ⊢` · `|a| ≤ b ↔ -b ≤ a ∧ a ≤ b`; in a hypothesis and the goal at once -/
example (a b c : ℝ) (k : -b ≤ a ∧ a ≤ b → -c ≤ a ∧ a ≤ c) (h : |a| ≤ b) : |a| ≤ c := by
  rw [abs_le] at h ⊢
  exact k h

/-! ## The base case -/

/-! ### R10. `simp` on a leaf: `sub_self`, `abs_zero`, `pow_zero`, `zero_mul` · closes the goal -/
example (x a : ℝ) (P : ℝ → Prop) (h : P 0) : P (|x - x| + (a ^ 0 - 1) * |x|) := by
  simp
  exact h

/-! ## Unpacking a hypothesis, naming a term -/

/-! ### R11. `obtain ⟨d, hA, hB⟩ := h` · context: `h : ∃ d, A d ∧ B d` → `d`, `hA`, `hB`
It sees through a definition whose body is `∃`; apply a `∀`-hypothesis to a point first: `hfl s`. -/
example {α : Type} (A B : α → Prop) (G : Prop) (h : ∃ d, A d ∧ B d) (k : ∀ d, A d → B d → G) :
    G := by
  obtain ⟨d, hA, hB⟩ := h
  exact k d hA hB

/-! ### R12. `set d := e` · context gains `d := e`; every `e` in the goal is replaced by `d` -/
example (m n : ℕ) (P : ℕ → Prop) (h : ∀ k, P (k + 1)) : P (max m n + 1) := by
  set d := max m n
  exact h d

/-! ### R13. `abs_nonneg` · `0 ≤ |a|`; with R3 it turns `|e| ≤ A` into `0 ≤ A` -/
example (e A : ℝ) (h : |e| ≤ A) : 0 ≤ A := by
  have h0 : 0 ≤ |e| := abs_nonneg e
  exact h0.trans h

/-! ## Monotonicity: `gcongr` -/

/-! ### R14. `gcongr` · goal `a * c ≤ b * c` → `a ≤ b`; the side goal `0 ≤ c` is found in the context -/
example (a b c x : ℝ) (hc : 0 ≤ c) (hax : a ≤ x) (hxb : x ≤ b) : a * c ≤ b * c := by
  gcongr
  exact hax.trans hxb

/-! ### R15. `gcongr` on a power (lemma `pow_le_pow_right₀ : 1 ≤ a → m ≤ n → a ^ m ≤ a ^ n`)
goal list: `(a ^ m - 1) * A ≤ (a ^ n - 1) * A` → `1 ≤ a` and `m ≤ n`. `exacts [p, q]` closes them in order. -/
example (u A : ℝ) (m n : ℕ) (hu : 0 ≤ u) (hA : 0 ≤ A) :
    ((1 + u) ^ m - 1) * A ≤ ((1 + u) ^ max m n - 1) * A := by
  gcongr
  exacts [by linarith, le_max_left m n]

/-! ### R16. `le_max_left`, `le_max_right` · `a ≤ max a b`, `b ≤ max a b` -/
example (m n : ℕ) : m ≤ max m n ∧ n ≤ max m n := ⟨le_max_left m n, le_max_right m n⟩

/-! ## Rewriting with an identity, chaining with `calc` -/

/-! ### R17. `rw [show A = B by ring]` · goal: `A` → `B`, for an identity you prove on the spot -/
example (a b c : ℝ) (P : ℝ → Prop) (h : P (a * c + b * c)) : P ((a + b) * c) := by
  rw [show (a + b) * c = a * c + b * c by ring]
  exact h

/-! ### R18. `calc` · prove `a ≤ d` as a chain `a ≤ b`, `b ≤ c`, `c = d`, one proof per link
`_` at the start of a line is the right side of the line above (in the first line: the goal's left side). -/
example (a b c d : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : c = d) : a ≤ d := by
  calc _ ≤ b := h₁
    _ ≤ c := h₂
    _ = d := h₃

/-! ### R19. `abs_mul` · `|a * b| = |a| * |b|` -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (|a| * |b|)) : P |a * b| := by
  rw [abs_mul]
  exact h

/-! ### R20. `one_le_pow₀` · `1 ≤ a → 1 ≤ a ^ n` -/
example (a : ℝ) (n : ℕ) (ha : 1 ≤ a) : 0 ≤ a ^ n - 1 := by
  have h : 1 ≤ a ^ n := one_le_pow₀ ha
  linarith

/-! ### R21. `gcongr` on a sum of products · goal list: one goal per factor that differs
A main goal equal to a hypothesis (`|δ| ≤ u`) is closed for you. Side goals `0 ≤ …` go to `positivity`,
which reads hypotheses such as `hw : 1 ≤ w` and `hA : 0 ≤ A`. The second example has only a bound
`positivity` cannot use, so the side goal `0 ≤ (w - 1) * A` comes first in the goal list. -/
example (e s δ u w A C : ℝ) (hw : 1 ≤ w) (hA : 0 ≤ A) (hC : 0 ≤ C) (hδ : |δ| ≤ u)
    (k : |e| ≤ (w - 1) * A ∧ |1 + δ| ≤ 1 + u ∧ |s| ≤ C) :
    |e| * |1 + δ| + |s| * |δ| ≤ (w - 1) * A * (1 + u) + C * u := by
  gcongr
  exacts [k.1, k.2.1, k.2.2]

example (e s δ u w A C : ℝ) (hw : 2 ≤ w + 1) (hA : 0 ≤ A) (hC : 0 ≤ C) (hδ : |δ| ≤ u)
    (k : |e| ≤ (w - 1) * A ∧ |1 + δ| ≤ 1 + u ∧ |s| ≤ C) :
    |e| * |1 + δ| + |s| * |δ| ≤ (w - 1) * A * (1 + u) + C * u := by
  gcongr
  exact mul_nonneg (by linarith) hA
  exacts [k.1, k.2.1, k.2.2]

/-! ### R22. `ring` with symbolic exponents · closes identities in which `a ^ (n + 1)` meets `a ^ n * a` -/
example (a x : ℝ) (n : ℕ) : (a ^ n - 1) * x * a + (a - 1) * x = (a ^ (n + 1) - 1) * x := by ring

/-! ## Nonnegativity and the last nonlinear step -/

/-! ### R23. `List.sum_nonneg` · `(∀ x ∈ l, 0 ≤ x) → 0 ≤ l.sum` · goal: a sum → a statement about each element -/
example (l : List ℝ) (h : ∀ x ∈ l, 0 ≤ x) : 0 ≤ l.sum := by
  refine List.sum_nonneg ?_
  exact h

/-! ### R24. `pow_succ` · `a ^ (n + 1) = a ^ n * a` -/
example {α : Type} [Monoid α] (a : α) (n : ℕ) (P : α → Prop) (h : P (a ^ n * a)) : P (a ^ (n + 1)) := by
  rw [pow_succ]
  exact h

/-! ### R25. `mul_nonneg` · `0 ≤ a → 0 ≤ b → 0 ≤ a * b` -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := mul_nonneg ha hb

/-! ### R26. `sub_nonneg` · `0 ≤ a - b ↔ b ≤ a`; `sub_nonneg.mpr h` turns `h : b ≤ a` into `0 ≤ a - b` -/
example (a b : ℝ) (h : b ≤ a) : 0 ≤ a - b := sub_nonneg.mpr h

/-! ### R27. `nlinarith [t]` · closes a goal that is linear once the product fact `t` is added -/
example (a b c : ℝ) (ha : 0 ≤ a) (hb : 1 ≤ b) (hc : 0 ≤ c) : a * c ≤ a * b * c := by
  nlinarith [mul_nonneg (mul_nonneg ha hc) (sub_nonneg.mpr hb)]

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Induction on a tree with unfolding and `linarith` (R1, R2, R8) -/
example (t : Bin) : 1 ≤ t.size := by
  induction t with
    | tip n => simp [Bin.size]
    | fork a b iha ihb =>
      simp only [Bin.size]
      linarith

/-! ### W2. One rounding of an exact sum: `|(a + b)(1 + δ) - (a + b)| ≤ (|a| + |b|) u` (R17, R19, R14, R4) -/
example (a b δ u : ℝ) (hδ : |δ| ≤ u) : |(a + b) * (1 + δ) - (a + b)| ≤ (|a| + |b|) * u := by
  rw [show (a + b) * (1 + δ) - (a + b) = (a + b) * δ by ring]
  rw [abs_mul]
  gcongr
  exact abs_add_le a b

/-! ### W3. List induction: a sum of squares is nonnegative (R6, R7, R8) -/
example (xs : List ℝ) : 0 ≤ (xs.map (fun x => x ^ 2)).sum := by
  induction xs with
    | nil => simp
    | cons x xs ih =>
      rw [List.map_cons, List.sum_cons]
      nlinarith [sq_nonneg x]

end H069Guide
