/- Guide for E047 (match in proofs).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries write a `match` as `refine match … with | pat => ?_` so that every branch shows up as a
goal in the infoview. In the exercise you write the same `match` with a tactic block in each branch
(`match n with | 0 => tac | k + 1 => tac`, R1) or, in term mode, with a term in each branch (R5, R8).
Part W: worked combinations on `isPos`, `isOne` and other propositions, not on the exercise's.
Assumed: Lean basics (E001–E033).
-/

namespace E047Guide

/-- `isPos n = true` exactly when `n ≥ 1`; defined by the same two patterns `0` / `_ + 1`. -/
def isPos : Nat → Bool
  | 0 => false
  | _ + 1 => true

/-- `isOne n = true` exactly when `n = 1`; three patterns. -/
def isOne : Nat → Bool
  | 0 => false
  | 1 => true
  | _ + 2 => false

/-! # Part R · Reference entries -/

/-! ## Splitting a natural number -/

/-! ### R1. `match n with | 0 => … | k + 1 => …` · goal list: one goal → one goal per pattern
In each branch `n` is replaced by the pattern, in the goal AND in every hypothesis that mentions
`n` (here `hn`). `n` itself stays listed, unused. The tactic form is
`match n with | 0 => tac₀ | k + 1 => tac₁`; `tacᵢ` then sees exactly the goal of branch `i`. -/
example (P : Nat → Prop) (h0 : P 0) (hs : ∀ k, P (k + 1)) (n : Nat) (hn : n ≠ 7) : P n := by
  refine match n with
    | 0 => ?_
    | k + 1 => ?_
  · exact h0
  · exact hs k

/-! ## Building `∨` and `∃` -/

/-! ### R2. `Or.inl` · goal `A ∨ B` → `A`
`Or.inl : A → A ∨ B`. `exact Or.inl e` closes the goal when `e : A`; `refine Or.inl ?_` leaves `A`. -/
example (A B : Prop) (ha : A) : A ∨ B := by
  refine Or.inl ?_
  exact ha

/-! ### R3. `Or.inr` · goal `A ∨ B` → `B`
`Or.inr : B → A ∨ B`. -/
example (A B : Prop) (hb : B) : A ∨ B := by
  refine Or.inr ?_
  exact hb

/-! ### R4. `⟨w, ?_⟩` (anonymous constructor for `∃`) · goal `∃ x, A x` → `A w`
`⟨w, e⟩ : ∃ x, A x` when `e : A w`. For `A x := (x + 1 = w + 1)` at `x := w`, `e` can be `rfl`. -/
example {α : Type} (A : α → Prop) (w : α) (hw : A w) : ∃ x, A x := by
  refine ⟨w, ?_⟩
  exact hw

/-! ## Taking `∃` and `∨` apart -/

/-! ### R5. `match h with | ⟨w, hw⟩ => …` · context: from `h : ∃ x, A x` gain `w : α`, `hw : A w`
`∃` has one constructor, so the `match` has one branch. `h` stays listed. The same in term mode,
directly after `:=`: `match h with | ⟨w, hw⟩ => (a term using w, hw)`. -/
example {α : Type} (A : α → Prop) (G : Prop) (g : ∀ w, A w → G) (h : ∃ x, A x) : G := by
  refine match h with
    | ⟨w, hw⟩ => ?_
  exact g w hw

/-! ### R6. Nested pattern `⟨w, ha, hb⟩` · context: from `h : ∃ x, A x ∧ B x` gain `w`, `ha`, `hb`
`⟨w, ha, hb⟩` abbreviates `⟨w, ⟨ha, hb⟩⟩`: the `∃` and the `∧` inside it are taken apart at once. -/
example {α : Type} (A B : α → Prop) (G : Prop) (g : ∀ w, A w → B w → G)
    (h : ∃ x, A x ∧ B x) : G := by
  refine match h with
    | ⟨w, ha, hb⟩ => ?_
  exact g w ha hb

/-! ### R7. `⟨w, ?_, ?_⟩` · goal `∃ x, A x ∧ B x` → two goals `A w`, `B w`
The anonymous constructor flattens the same way: `⟨w, e₁, e₂⟩` is `⟨w, ⟨e₁, e₂⟩⟩`. -/
example {α : Type} (A B : α → Prop) (w : α) (ha : A w) (hb : B w) : ∃ x, A x ∧ B x := by
  refine ⟨w, ?_, ?_⟩
  · exact ha
  · exact hb

/-! ### R8. `match h with | .inl ha => … | .inr hb => …` · goal list: one goal → two;
context gains `ha : A` in the first, `hb : B` in the second. `∨` has two constructors, so two
branches. In term mode, each branch is a term: `| .inl ha => e₁ | .inr hb => e₂`. -/
example (A B G : Prop) (ga : A → G) (gb : B → G) (h : A ∨ B) : G := by
  refine match h with
    | .inl ha => ?_
    | .inr hb => ?_
  · exact ga ha
  · exact gb hb

/-! ### R9. `.inr e` / `.inl e` (leading-dot constructor) · goal `A ∨ B` → `B`
When the expected type is `A ∨ B` (that is, `Or A B`), `.inr` means `Or.inr`: Lean takes the
namespace from the expected type. Works for patterns (R8) and for terms. -/
example (A B : Prop) (hb : B) : A ∨ B := by
  refine .inr ?_
  exact hb

/-! ## Computing a Boolean function after the split -/

/-! ### R10. `simp only [f]` · goal: `f 0` or `f (k + 1)` → the right side of that equation of `f`
`simp only [isPos]` uses `isPos 0 = false` and `isPos (k + 1) = true`. It rewrites only where the
argument literally has the shape `0` or `_ + 1`, which is why you split `n` first (R1). -/
example (k : Nat) (P : Bool → Prop) (h : P true) : P (isPos (k + 1)) := by
  simp only [isPos]
  exact h

/-! ### R11. `Bool.false_eq_true` · `(false = true) = False` · goal: `false = true` → `False` -/
example (P : Prop → Prop) (h : P False) : P (false = true) := by
  simp only [Bool.false_eq_true]
  exact h

/-! ### R12. `Nat.add_one_ne_zero` · `n + 1 ≠ 0` · goal: `k + 1 = 0` → `False`
`simp` uses a lemma `a ≠ b` to rewrite `a = b` to `False`. -/
example (k : Nat) (P : Prop → Prop) (h : P False) : P (k + 1 = 0) := by
  simp only [Nat.add_one_ne_zero]
  exact h

/-! ### R13. `simp` · closes `A ↔ A` (lemma `iff_self`); also `a = a` (lemma `eq_self`) -/
example (A : Prop) : (A ↔ A) ∧ (0 = 0) := by
  simp

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Nested patterns with constructors inside: R6 and R8 in one `match`, then R9, R7
A pattern may contain `.inl` / `.inr`, so one `match` gives two branches with three variables each. -/
example {α : Type} (A B C : α → Prop) (h : ∃ x, A x ∧ (B x ∨ C x)) :
    ∃ x, (A x ∧ B x) ∨ (A x ∧ C x) :=
  match h with
  | ⟨w, ha, .inl hb⟩ => ⟨w, .inl ⟨ha, hb⟩⟩
  | ⟨w, ha, .inr hc⟩ => ⟨w, .inr ⟨ha, hc⟩⟩

/-! ### W2. A Boolean function with three patterns: R1 with three branches, then `simp [isOne]`
In each branch `simp [isOne]` unfolds the equation (R10) and finishes the `↔` (R11–R13);
it also knows `k + 2 = 1` is `False`. -/
theorem isOne_eq_true (n : Nat) : isOne n = true ↔ n = 1 := by
  refine match n with
    | 0 => ?_
    | 1 => ?_
    | k + 2 => ?_
  · simp [isOne]
  · simp [isOne]
  · simp [isOne]

/-! ### W3. The tactic form of R1, each branch closed by R2 / R3 and `rfl`
In the branch `k + 1` the goal mentions `isPos (k + 1)`, which computes to `true`, so `rfl` proves
`isPos (k + 1) = true`. On the unsplit `n`, `rfl` would fail: `isPos n` does not compute. -/
example (n : Nat) : isPos n = true ∨ n = 0 := by
  match n with
    | 0 => exact Or.inr rfl
    | k + 1 => exact Or.inl rfl

end E047Guide
