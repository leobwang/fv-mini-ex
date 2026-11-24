/- Guide for M068 (Limit of a sum).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (two "eventually" properties
`S`, `T`; a three-point triangle inequality with thirds of `e`).
Assumed: Lean basics.
-/
import Mathlib

namespace M068Guide

/-! # Part R · Reference entries -/

/-! ## Opening the ε-N statement -/

/-! ### R1. `intro ε hε` · goal: a definition whose body is `∀ ε > 0, …` → context gains `ε`, `hε`
`intro` unfolds a definition by itself when its body starts with `∀`. `∀ ε > 0, Q ε` is
`∀ ε, ε > 0 → Q ε`, so it takes two names. -/
def AllPos (Q : ℝ → Prop) : Prop := ∀ ε > 0, Q ε

example (Q : ℝ → Prop) (h : ∀ ε, ε > 0 → Q ε) : AllPos Q := by
  intro ε hε
  exact h ε hε

/-! ## Asking a hypothesis for precision `e / 2` -/

/-! ### R2. `positivity` · closes `0 < e / 2` when the context has `he : e > 0`
It proves `0 < t`, `0 ≤ t`, `t ≠ 0` for `t` built from positive pieces (numerals, `+`, `*`, `/`), and
for a variable it looks for a hypothesis such as `he : e > 0` in the context. -/
example (e : ℝ) (he : e > 0) : 0 < e / 2 := by
  positivity

/-! ### R3. `obtain ⟨K, hK⟩ := h (e / 2) (by positivity)` · context gains `K` and `hK`
`h : ∀ e > 0, ∃ N, …` is a function: give it the number `e / 2` and a proof of `e / 2 > 0` (R2), and it
returns `∃ N, …`, which `obtain` takes apart into the witness and its property. -/
example (S : ℝ → ℕ → Prop) (h : ∀ e > 0, ∃ N : ℕ, ∀ n ≥ N, S e n) (e : ℝ) (he : e > 0)
    (G : Prop) (g : ∀ K : ℕ, (∀ n ≥ K, S (e / 2) n) → G) : G := by
  obtain ⟨K, hK⟩ := h (e / 2) (by positivity)
  exact g K hK

/-! ## One `N` for two sequences: `max` -/

/-! ### R4. `refine ⟨max K M, fun k hk => ?_⟩` · goal `∃ N, ∀ n ≥ N, S n` → context gains `k`, `hk`
`max K M` is the larger of `K` and `M`. The `fun` proves the `∀ n ≥ N` part; its body `?_` is the
new goal. `∀ n ≥ N, S n` is `∀ n, n ≥ N → S n`, so the `fun` takes two names. -/
example (S : ℕ → Prop) (K M : ℕ) (h : ∀ k, k ≥ max K M → S k) : ∃ N : ℕ, ∀ n ≥ N, S n := by
  refine ⟨max K M, fun k hk => ?_⟩
  exact h k hk

/-! ### R5. `have e := h k hk` · context gains `e : S k` (an instance of `h : ∀ n ≥ K, S n`)
Without a type after `have`, Lean takes the type of the term. -/
example (S : ℕ → Prop) (K k : ℕ) (h : ∀ n ≥ K, S n) (hk : k ≥ K) (G : Prop) (g : S k → G) : G := by
  have e := h k hk
  exact g e

/-! ### R6. `le_of_max_le_left` · `max a b ≤ c → a ≤ c` · closes `K ≤ k` from `hk : k ≥ max K M`
`k ≥ max K M` is notation for `max K M ≤ k`, so `hk` fits as it is. In general
`{α : Type} [LinearOrder α] {a b c : α}`; `ℕ`, `ℤ`, `ℚ`, `ℝ` qualify. -/
example (K M k : ℕ) (hk : k ≥ max K M) : K ≤ k := by
  exact le_of_max_le_left hk

/-! ### R7. `le_of_max_le_right` · `max a b ≤ c → b ≤ c` · closes `M ≤ k` from `hk : k ≥ max K M` -/
example (K M k : ℕ) (hk : k ≥ max K M) : M ≤ k := by
  exact le_of_max_le_right hk

/-! ## The estimate: a `calc` chain -/

/-! ### R8. `calc` · closes `a < d` by a chain `a = b`, `b ≤ c`, `c < d`, each step with its own proof
Lean composes the relations: `=` then `≤` then `<` gives `<`. Each `_` stands for the previous right-hand
side. The first term only has to be the goal's left side up to unfolding, so it may be written beta-reduced:
here the goal says `(fun n => f n + 1) k` and the chain starts from `f k + 1`. -/
example (f : ℕ → ℝ) (k : ℕ) (b c d : ℝ) (h1 : f k + 1 = b) (h2 : b ≤ c) (h3 : c < d) :
    (fun n => f n + 1) k < d := by
  calc f k + 1 = b := h1
    _ ≤ c := h2
    _ < d := h3

/-! ### R9. `ring_nf` · closes `|x + y - (u + v)| = |x - u + (y - v)|`
It puts every ring expression in normal form, also inside `|·|`; both sides become the same term. `ring`
treats `|·|` as opaque: it fails, then runs `ring_nf` and prints `Try this: ring_nf`. -/
example (x y u v : ℝ) : |x + y - (u + v)| = |x - u + (y - v)| := by
  ring_nf

/-! ### R10. `abs_add_le` · `|a + b| ≤ |a| + |b|` (triangle inequality) · closes that goal
In general `{α : Type} [Lattice α] [AddCommGroup α] [AddLeftMono α] (a b : α)`; `ℤ`, `ℚ`, `ℝ` qualify.
In a `calc` step write `abs_add_le _ _`: Lean reads `a` and `b` off the step. -/
example (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  exact abs_add_le a b

/-! ### R11. `add_lt_add` · `a < b → c < d → a + c < b + d` · closes `a + c < b + d`
In general `{α : Type} [Add α] [Preorder α] [AddLeftStrictMono α] [AddRightStrictMono α]`; `ℕ`, `ℤ`,
`ℚ`, `ℝ` qualify. -/
example (a b c d : ℝ) (h1 : a < b) (h2 : c < d) : a + c < b + d := by
  exact add_lt_add h1 h2

/-! ### R12. `ring` · closes `e / 2 + e / 2 = e`
In a field such as `ℝ`, `ring` handles division by a numeral (it reads `e / 2` as `e * 2⁻¹`). The lemma
`add_halves : a / 2 + a / 2 = a` does the same. -/
example (e : ℝ) : e / 2 + e / 2 = e := by
  ring

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Two "eventually" properties hold together from `max K M` on: R3, R4, R5 with R6 and R7 -/
example (S T : ℕ → Prop) (hS : ∃ K : ℕ, ∀ k ≥ K, S k) (hT : ∃ M : ℕ, ∀ k ≥ M, T k) :
    ∃ N : ℕ, ∀ n ≥ N, S n ∧ T n := by
  obtain ⟨K, hK⟩ := hS
  obtain ⟨M, hM⟩ := hT
  refine ⟨max K M, fun k hk => ?_⟩
  have e1 := hK k (le_of_max_le_left hk)
  have e2 := hM k (le_of_max_le_right hk)
  exact ⟨e1, e2⟩

/-! ### W2. Triangle inequality through a middle point, with `e / 3` and `2 * e / 3`: R8 with R9–R12 -/
example (x y z e : ℝ) (h1 : |x - y| < e / 3) (h2 : |y - z| < 2 * e / 3) : |x - z| < e := by
  calc |x - z| = |(x - y) + (y - z)| := by ring_nf
    _ ≤ |x - y| + |y - z| := abs_add_le _ _
    _ < e / 3 + 2 * e / 3 := add_lt_add h1 h2
    _ = e := by ring

end M068Guide
