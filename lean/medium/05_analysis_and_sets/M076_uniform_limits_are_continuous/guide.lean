/- Guide for M076 (Uniform limits are continuous).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` or `k` in an entry is only there to finish the example; it shows what the goal became.
`G : Prop` is an arbitrary goal; `k : … → G` consumes a fact that the step added to the context.
`Q`, `R` are arbitrary predicates standing for "some property".
Part W: worked combinations on objects that are NOT the exercise's (three real numbers, no functions).
Assumed: Lean basics (E001–E033). New: Mathlib's real numbers `ℝ`, absolute value `|x|`, and the
tactics `obtain`, `calc`, `positivity`, `ring_nf`, `gcongr`.
-/
import Mathlib

namespace M076Guide

/-! # Part R · Reference entries -/

/-! ## ε–δ statements: taking them apart and building them -/

/-- A toy definition whose body is an `∀ ε > 0, …`, like the exercise's two definitions. -/
def ForallPos (Q : ℝ → Prop) : Prop := ∀ ε > 0, Q ε

/-! ### R1. `intro ε hε` · goal `∀ ε > 0, Q ε` (even behind a `def`) → context gains `ε`, `hε` -/
example (Q : ℝ → Prop) (h : ∀ e : ℝ, 0 < e → Q e) : ForallPos Q := by
  intro ε hε
  exact h ε hε

/-- A toy definition with the shape "for every `ε > 0` there is an index `N`". -/
def SomeIndex (Q : ℝ → ℕ → Prop) : Prop := ∀ ε > 0, ∃ N : ℕ, Q ε N

/-! ### R2. `obtain ⟨N, hN⟩ := h (e / 3) (by positivity)` · apply `h` at `e / 3` (a `def` unfolds
when applied), split the `∃` · context gains `N`, `hN` -/
example (Q : ℝ → ℕ → Prop) (h : SomeIndex Q) (e : ℝ) (he : e > 0) (G : Prop)
    (k : ∀ N, Q (e / 3) N → G) : G := by
  obtain ⟨N, hN⟩ := h (e / 3) (by positivity)
  exact k N hN

/-! ### R3. `positivity` · closes `0 < t` (or `t > 0`) for `t` built from positive pieces -/
example (e : ℝ) (he : e > 0) : e / 3 > 0 := by
  positivity

/-! ### R4. `obtain ⟨δ, hδ, hc⟩ := h` · `h : ∃ δ > 0, Q δ` → context gains `δ`, `hδ : δ > 0`, `hc` -/
example (Q : ℝ → Prop) (h : ∃ δ > 0, Q δ) (G : Prop) (k : ∀ d : ℝ, d > 0 → Q d → G) : G := by
  obtain ⟨δ, hδ, hc⟩ := h
  exact k δ hδ hc

/-! ### R5. `refine ⟨δ, hδ, fun y hy => ?_⟩` · goal `∃ d > 0, ∀ y, R y d → P y` → witness `δ` and
its proof `hδ` given, context gains `y hy`, goal is the body -/
example (R : ℝ → ℝ → Prop) (P : ℝ → Prop) (δ : ℝ) (hδ : δ > 0) (h : ∀ y, R y δ → P y) :
    ∃ d > 0, ∀ y, R y d → P y := by
  refine ⟨δ, hδ, fun y hy => ?_⟩
  exact h y hy

/-! ### R6. `have h2 := hc y hy` · instantiate a `∀ y, A y → B y` hypothesis · context gains `h2` -/
example (A B : ℝ → Prop) (hc : ∀ y, A y → B y) (y : ℝ) (hy : A y) : B y := by
  have h2 := hc y hy
  exact h2

/-! ### R7. `le_rfl` · `a ≤ a`; it proves `N ≥ N` when you instantiate `∀ n ≥ N, …` at `n := N`
· context gains the instance -/
example (Q : ℕ → ℝ → Prop) (N : ℕ) (hN : ∀ n ≥ N, ∀ x, Q n x) (z : ℝ) (G : Prop)
    (k : Q N z → G) : G := by
  have h1 := hN N le_rfl z
  exact k h1

/-! ## Chains of (in)equalities and the triangle inequality -/

/-! ### R8. `calc` · goal `a < e` closed by a chain `a = b`, `b ≤ c`, `c < d`, `d = e` -/
example (a b c d e : ℝ) (h1 : a = b) (h2 : b ≤ c) (h3 : c < d) (h4 : d = e) : a < e := by
  calc a = b := h1
    _ ≤ c := h2
    _ < d := h3
    _ = e := h4

/-! ### R9. `ring_nf` · closes `g (a - d) = g ((a - b) + (b - c) + (c - d))`: it normalises ring
expressions even inside a function such as `|·|` -/
example (g : ℝ → ℝ) (a b c d : ℝ) : g (a - d) = g ((a - b) + (b - c) + (c - d)) := by
  ring_nf

/-! ### R10. `abs_add_three` · `|a + b + c| ≤ |a| + |b| + |c|` (triangle inequality, three terms)
· context gains it -/
example (a b c : ℝ) (G : Prop) (k : |a + b + c| ≤ |a| + |b| + |c| → G) : G := by
  have h := abs_add_three a b c
  exact k h

/-! ### R11. `abs_sub_comm` · `|a - b| = |b - a|`; `rw [abs_sub_comm a]` flips only `|a - _|` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P |b - a|) : P |a - b| := by
  rw [abs_sub_comm a]
  exact h

/-! ### R12. `gcongr` · goal `a + b + c < d + e + f` → one goal per summand pair `a < d`, `b < e`,
`c < f`; each is closed at once by a hypothesis that states it exactly; any other is handed back
(W2) · goal list -/
example (a b c d e f : ℝ) (h1 : a < d) (h2 : b < e) (h3 : c < f) : a + b + c < d + e + f := by
  gcongr

/-! ### R13. `ring` · closes an identity of commutative rings; division by a numeral is allowed -/
example (e : ℝ) : e / 4 + e / 4 + e / 2 = e := by
  ring

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The ε/3 split on three real numbers: R8 with R9, R10, R11, R12, R13 -/
example (u v w z e : ℝ) (h1 : |u - v| < e / 3) (h2 : |w - v| < e / 3) (h3 : |w - z| < e / 3) :
    |u - z| < e := by
  calc |u - z| = |(u - v) + (v - w) + (w - z)| := by ring_nf
    _ ≤ |u - v| + |v - w| + |w - z| := abs_add_three _ _ _
    _ < e / 3 + e / 3 + e / 3 := by rw [abs_sub_comm v]; gcongr
    _ = e := by ring

/-! ### W2. Without the flip, `gcongr` cannot close the middle goal and hands it back (R12, R11) -/
example (u v w z e : ℝ) (h1 : |u - v| < e / 3) (h2 : |w - v| < e / 3) (h3 : |w - z| < e / 3) :
    |u - v| + |v - w| + |w - z| < e / 3 + e / 3 + e / 3 := by
  gcongr
  rw [abs_sub_comm v]
  exact h2

end M076Guide
