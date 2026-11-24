/- Guide for M075 (Monotone convergence).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a function on `ℤ`, other bounds).
Assumed: Lean basics.
-/
import Mathlib

namespace M075Guide

/-! # Part R · Reference entries -/

/-! ## Opening the ε-N statement -/

/-! ### R1. `intro ε hε` · goal: a definition whose body is `∀ ε > 0, …` → context gains `ε`, `hε`
`intro` unfolds a definition by itself when its body starts with `∀`. `∀ ε > 0, Q ε` is
`∀ ε, ε > 0 → Q ε`, so it takes two names. -/
def AllPos (Q : ℝ → Prop) : Prop := ∀ ε > 0, Q ε

example (Q : ℝ → Prop) (h : ∀ ε, ε > 0 → Q ε) : AllPos Q := by
  intro ε hε
  exact h ε hε

/-! ## Finding a term above `sSup s - ε` -/

/-! ### R2. `sub_lt_self` · `0 < b → a - b < a` · context gains the fact
`sub_lt_self a hb`: the first argument `a` is explicit, `b` is read off `hb`. Pass `_` for `a` and
Lean finds it from the expected type. -/
example {α : Type} [AddGroup α] [LT α] [AddLeftStrictMono α] (a b : α) (hb : 0 < b) (P : Prop)
    (h : a - b < a → P) : P := by
  have hlt : a - b < a := sub_lt_self a hb
  exact h hlt

/-! ### R3. `Set.range_nonempty` · `(Set.range f).Nonempty` when the domain is nonempty · context gains it
`Set.range f = {x | ∃ y, f y = x}`, the set of values of `f`. `ℕ` is nonempty (it contains `0`), so
no hypothesis is needed. -/
example {α : Type} (f : ℕ → α) (P : Prop) (h : (Set.range f).Nonempty → P) : P := by
  have hne : (Set.range f).Nonempty := Set.range_nonempty f
  exact h hne

/-! ### R4. `exists_lt_of_lt_csSup` · `s.Nonempty → b < sSup s → ∃ x ∈ s, b < x` · context gains it
Anything below the supremum is beaten by some element of the set. `cs` = "conditionally complete":
`ℝ` has `sSup` of every nonempty bounded-above set, so the lemma asks for `s.Nonempty`. -/
example {α : Type} [ConditionallyCompleteLinearOrder α] (s : Set α) (b : α) (hs : s.Nonempty)
    (hb : b < sSup s) (P : Prop) (h : (∃ x ∈ s, b < x) → P) : P := by
  have hex : ∃ x ∈ s, b < x := exists_lt_of_lt_csSup hs hb
  exact h hex

/-! ### R5. `obtain ⟨_, ⟨N, rfl⟩, hN⟩ := hex` · context: `∃ x ∈ Set.range f, b < x` → `N`, `hN : b < f N`
`x ∈ Set.range f` is `∃ y, f y = x`; the inner pattern `⟨N, rfl⟩` names `y` as `N` and the `rfl`
replaces `x` by `f N` everywhere, so `x` itself (the `_`) disappears. -/
example {α : Type} [LT α] (f : ℕ → α) (b : α) (hex : ∃ x ∈ Set.range f, b < x) (P : Prop)
    (h : ∀ N, b < f N → P) : P := by
  obtain ⟨_, ⟨N, rfl⟩, hN⟩ := hex
  exact h N hN

/-! ## Choosing `N` -/

/-! ### R6. `refine ⟨N, fun n hn => ?_⟩` · goal `∃ N, ∀ n ≥ N, Q n` → context gains `n`, `hn : n ≥ N`
`∀ n ≥ N, Q n` is `∀ n, n ≥ N → Q n`, so the function takes two arguments. -/
example (Q : ℕ → Prop) (N : ℕ) (h : ∀ n, n ≥ N → Q n) : ∃ M : ℕ, ∀ n ≥ M, Q n := by
  refine ⟨N, fun n hn => ?_⟩
  exact h n hn

/-! ## Facts about one term `f n` -/

/-! ### R7. `⟨n, rfl⟩ : f n ∈ Set.range f` · a membership proof (also `Set.mem_range_self n`)
The anonymous constructor gives the witness `n` and the proof `f n = f n` of `∃ y, f y = f n`. -/
example {α : Type} (f : ℕ → α) (n : ℕ) (P : Prop) (h : f n ∈ Set.range f → P) : P := by
  have hmem : f n ∈ Set.range f := ⟨n, rfl⟩
  exact h hmem

/-! ### R8. `le_csSup` · `BddAbove s → x ∈ s → x ≤ sSup s` · context gains it
Every element of a bounded-above set is at most its supremum. -/
example {α : Type} [ConditionallyCompleteLattice α] (s : Set α) (x : α) (hbdd : BddAbove s)
    (hx : x ∈ s) (P : Prop) (h : x ≤ sSup s → P) : P := by
  have hle : x ≤ sSup s := le_csSup hbdd hx
  exact h hle

/-! ### R9. `hm hab` with `hm : Monotone f` · `a ≤ b → f a ≤ f b` · context gains it
`Monotone f` is the statement `∀ ⦃a b⦄, a ≤ b → f a ≤ f b`, so `hm` is applied like a function to a
proof of `a ≤ b`; `a`, `b` are read off that proof. -/
example {α β : Type} [Preorder α] [Preorder β] (f : α → β) (hm : Monotone f) (a b : α)
    (hab : a ≤ b) (P : Prop) (h : f a ≤ f b → P) : P := by
  have hfab : f a ≤ f b := hm hab
  exact h hfab

/-! ## Closing `|x - L| < ε` -/

/-! ### R10. `abs_sub_lt_iff` · `|a - b| < c ↔ a - b < c ∧ b - a < c` · goal: one `|·|` → two inequalities
On `ℝ`; the brackets say: an additive group with a compatible total order (`ℝ`, `ℤ`, `ℚ` qualify). -/
example {G : Type} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] (a b c : G)
    (h : a - b < c ∧ b - a < c) : |a - b| < c := by
  rw [abs_sub_lt_iff]
  exact h

/-! ### R11. `linarith` · closes a linear (in)equality that follows from hypotheses
`linarith` adds up hypotheses `t < s`, `t ≤ s`, `t = s` with nonnegative coefficients. Atoms such as
`sSup s` or `f n` are unknowns to it. -/
example (u v w e : ℝ) (h1 : u - e < v) (h2 : v ≤ w) : u - w < e := by
  linarith

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A value of `g : ℤ → ℝ` strictly between `b` and the supremum: R3, R4, R5, R7, R8 -/
example (g : ℤ → ℝ) (hg : BddAbove (Set.range g)) (b : ℝ) (hb : b < sSup (Set.range g)) :
    ∃ k, b < g k ∧ g k ≤ sSup (Set.range g) := by
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := exists_lt_of_lt_csSup (Set.range_nonempty g) hb
  exact ⟨k, hk, le_csSup hg ⟨k, rfl⟩⟩

/-! ### W2. Two one-sided bounds → one absolute value: R10, `constructor`, R11 -/
example (x y L e : ℝ) (h1 : L - e < x) (h2 : x ≤ y) (h3 : y ≤ L) : |L - y| < e := by
  rw [abs_sub_lt_iff]
  constructor
  · linarith
  · linarith

/-! ### W3. `n ≥ N` is `N ≤ n`, so a monotone hypothesis applies to it directly: R9 -/
example (f : ℕ → ℝ) (hm : Monotone f) (N n : ℕ) (hn : n ≥ N) : f N ≤ f n := hm hn

end M075Guide
