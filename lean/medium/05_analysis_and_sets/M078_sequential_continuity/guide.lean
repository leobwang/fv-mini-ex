/- Guide for M078 (ε-δ continuity ⇔ sequential continuity).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` or `k` in an entry is only there to finish the example; it shows what the goal became.
`G : Prop` is an arbitrary goal; `k : … → G` consumes a fact that the step added to the context.
`Q`, `R`, `A`, `B` are arbitrary predicates ("some property"); in R8 `B : ℝ → ℝ` is an arbitrary
function.
Part W: worked combinations on objects that are NOT the exercise's (an unbounded sequence, `2 / (n + 1)`).
Assumed: Lean basics (E001–E033). New: Mathlib's real numbers `ℝ`, the cast `ℕ → ℝ`, absolute value
`|x|`, and the tactics `obtain`, `by_contra`, `push Not`, `choose`, `positivity`, `exact_mod_cast`,
`nlinarith`.
-/
import Mathlib

namespace M078Guide

/-! # Part R · Reference entries -/

/-! ## Splitting `↔`, taking ε-statements apart and building them -/

/-! ### R1. `constructor` on `↔` · goal `A ↔ B` → two goals `A → B` and `B → A` · goal list -/
example (A B : Prop) (hab : A → B) (hba : B → A) : A ↔ B := by
  constructor
  exacts [hab, hba]

/-! ### R2. `intro ε hε` · goal `∀ ε > 0, Q ε` → context gains `ε`, `hε : ε > 0` -/
example (Q : ℝ → Prop) (h : ∀ e : ℝ, 0 < e → Q e) : ∀ ε > 0, Q ε := by
  intro ε hε
  exact h ε hε

/-- A toy definition whose body is a `∀ ε > 0, …`, like the exercise's two definitions. -/
def ForallPos (Q : ℝ → Prop) : Prop := ∀ ε > 0, Q ε

/-! ### R3. `intro` sees through a `def` · goal `ForallPos Q` (body `∀ ε > 0, Q ε`) → context gains
`ε`, `hε` -/
example (Q : ℝ → Prop) (h : ∀ e : ℝ, 0 < e → Q e) : ForallPos Q := by
  intro ε hε
  exact h ε hε

/-! ### R4. `obtain ⟨δ, hδ, hR⟩ := hf ε hε` · apply `hf` at `ε`, `hε`, split the `∃ δ > 0` · context
gains `δ`, `hδ : δ > 0`, `hR` -/
example (R : ℝ → ℝ → Prop) (hf : ∀ ε > 0, ∃ δ > 0, R ε δ) (ε : ℝ) (hε : ε > 0) (G : Prop)
    (k : ∀ d : ℝ, d > 0 → R ε d → G) : G := by
  obtain ⟨δ, hδ, hR⟩ := hf ε hε
  exact k δ hδ hR

/-! ### R5. `refine ⟨N, fun n hn => ?_⟩` · goal `∃ M, ∀ n ≥ M, A n` → witness `N` given, context
gains `n`, `hn : n ≥ N`, goal is the body -/
example (A : ℕ → Prop) (N : ℕ) (h : ∀ n, N ≤ n → A n) : ∃ M : ℕ, ∀ n ≥ M, A n := by
  refine ⟨N, fun n hn => ?_⟩
  exact h n hn

/-! ## Proof by contradiction -/

/-! ### R6. `by_contra hf` · goal `G` → context gains `hf : ¬G`, goal `False` -/
example (G : Prop) (k : ¬G → False) : G := by
  by_contra hf
  exact k hf

/-! ### R7. `unfold ForallPos at h` · hypothesis: the name → its body · context -/
example (Q : ℝ → Prop) (h : ¬ForallPos Q) (k : (¬∀ ε > 0, Q ε) → False) : False := by
  unfold ForallPos at h
  exact k h

/-! ### R8. `push Not at h` · pushes `¬` inward through `∀`, `∃`, `→`, `<` · context
`¬∀ ε > 0, ∃ δ > 0, ∀ y, A δ y → B y < ε` → `∃ ε > 0, ∀ δ > 0, ∃ y, A δ y ∧ ε ≤ B y` -/
example (A : ℝ → ℝ → Prop) (B : ℝ → ℝ) (h : ¬∀ ε > 0, ∃ δ > 0, ∀ y, A δ y → B y < ε) (G : Prop)
    (k : (∃ ε > 0, ∀ δ > 0, ∃ y, A δ y ∧ ε ≤ B y) → G) : G := by
  push Not at h
  exact k h

/-! ## Building a sequence from "for every n there is a y" -/

/-! ### R9. `choose a ha1 ha2 using hb` · `hb : ∀ n, ∃ y, A n y ∧ B n y` → context gains the function
`a : ℕ → ℝ` and `ha1 : ∀ n, A n (a n)`, `ha2 : ∀ n, B n (a n)` -/
example (A B : ℕ → ℝ → Prop) (hb : ∀ n : ℕ, ∃ y, A n y ∧ B n y) (G : Prop)
    (k : ∀ a : ℕ → ℝ, (∀ n, A n (a n)) → (∀ n, B n (a n)) → G) : G := by
  choose a ha1 ha2 using hb
  exact k a ha1 ha2

/-! ### R10. `positivity` · closes `0 < t` (or `t > 0`) for `t` built from positive pieces -/
example (n : ℕ) : 1 / ((n : ℝ) + 1) > 0 := by
  positivity

/-! ## Archimedes, casts, and inequalities with division -/

/-! ### R11. `exists_nat_gt` · `(r : ℝ) : ∃ n : ℕ, r < ↑n` (Archimedes) · context gains `N`, `hN` -/
example (r : ℝ) (G : Prop) (k : ∀ N : ℕ, r < N → G) : G := by
  obtain ⟨N, hN⟩ := exists_nat_gt r
  exact k N hN

/-! ### R12. `lt_of_lt_of_le` · `a < b → b ≤ c → a < c`; `refine lt_of_lt_of_le hab ?_` · goal
`a < c` → `b ≤ c` -/
example (a b c : ℝ) (hab : a < b) (hbc : b ≤ c) : a < c := by
  refine lt_of_lt_of_le hab ?_
  exact hbc

/-! ### R13. `exact_mod_cast hn` · closes `(↑N : ℝ) ≤ ↑n` from `hn : n ≥ N` in `ℕ` -/
example (N n : ℕ) (hn : n ≥ N) : (N : ℝ) ≤ n := by
  exact_mod_cast hn

/-! ### R14. `div_le_iff₀` · `0 < c → (a / c ≤ b ↔ a ≤ b * c)` · goal: clears the division -/
example (a b c : ℝ) (hc : 0 < c) (h : a ≤ b * c) : a / c ≤ b := by
  rw [div_le_iff₀ hc]
  exact h

/-! ### R15. `div_lt_iff₀ … at h` · `0 < c → (a / c < b ↔ a < b * c)` · context: clears the division
in a hypothesis -/
example (a b c : ℝ) (hc : 0 < c) (h : a / c < b) (G : Prop) (k : a < b * c → G) : G := by
  rw [div_lt_iff₀ hc] at h
  exact k h

/-! ### R16. `nlinarith` · closes a linear-looking goal whose proof needs a product of two
hypotheses (here `(c - b) * a ≥ 0` from `hbc` and `ha`); `linarith` fails on it -/
example (a b c : ℝ) (ha : 0 < a) (hb : 1 < b * a) (hbc : b ≤ c) : 1 ≤ a * c := by
  nlinarith

/-! ## Closing the contradiction -/

/-! ### R17. `le_rfl` · `a ≤ a`; it proves `N ≥ N` when you instantiate `∀ n ≥ N, …` at `n := N`
· context gains the instance -/
example (A : ℕ → Prop) (N : ℕ) (hN : ∀ n ≥ N, A n) (G : Prop) (k : A N → G) : G := by
  have h1 := hN N le_rfl
  exact k h1

/-! ### R18. `not_lt` · `¬a < b ↔ b ≤ a`; `not_lt.mpr h` turns `h : b ≤ a` into `¬a < b` · context -/
example (a b : ℝ) (h : b ≤ a) (G : Prop) (k : ¬a < b → G) : G := by
  have h2 := not_lt.mpr h
  exact k h2

/-! ### R19. `absurd` · `absurd (ha : A) (hna : ¬A) : G` closes any goal `G` -/
example (A G : Prop) (ha : A) (hna : ¬A) : G := by
  exact absurd ha hna

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-- A toy definition: `g` takes values above every bound `M`. -/
def Unbounded (g : ℕ → ℝ) : Prop := ∀ M : ℝ, ∃ n, M < g n

/-! ### W1. Negating a definition: `unfold … at h`, then `push Not at h` (R7, R8) -/
example (g : ℕ → ℝ) (h : ¬Unbounded g) : ∃ M : ℝ, ∀ n, g n ≤ M := by
  unfold Unbounded at h
  push Not at h
  exact h

/-! ### W2. Two facts that contradict each other close any goal (R4, R18, R19) -/
example (g : ℕ → ℝ) (hu : Unbounded g) (hg : ∀ n, g n ≤ 5) : False := by
  obtain ⟨n, hn⟩ := hu 5
  exact absurd hn (not_lt.mpr (hg n))

/-! ### W3. A sequence from "every `δ > 0` has a `y`", with `δ = 1 / (n + 1)` (R9 with R10) -/
example (A B : ℝ → ℝ → Prop) (hb : ∀ δ > 0, ∃ y, A δ y ∧ B δ y) :
    ∃ a : ℕ → ℝ, ∀ n : ℕ, B (1 / ((n : ℝ) + 1)) (a n) := by
  choose a ha1 ha2 using fun n : ℕ => hb (1 / ((n : ℝ) + 1)) (by positivity)
  exact ⟨a, ha2⟩

/-! ### W4. `2 / (n + 1) ≤ η` for `n ≥ N`, from Archimedes `2 / η < N` (R11, R13, R14, R10, R15, R16) -/
example (η : ℝ) (hη : η > 0) : ∃ N : ℕ, ∀ n ≥ N, 2 / ((n : ℝ) + 1) ≤ η := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / η)
  refine ⟨N, fun n hn => ?_⟩
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_le_iff₀ (by positivity)]
  rw [div_lt_iff₀ hη] at hN
  nlinarith

end M078Guide
