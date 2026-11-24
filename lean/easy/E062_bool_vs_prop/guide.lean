/- Guide for E062 (Bool vs Prop).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`decide` is banned in this exercise, so this file never writes it: `((p : Prop) : Bool)` is the
coercion from a decidable Prop to Bool, which elaborates to (and prints as) `decide p`.
Part W: worked combinations on `allEven` below, NOT the exercise's `allPos`.
Assumed: Lean basics (E001–E033), in particular `∧`/`↔` and `.1`/`.2` (E005), `rw` (E009),
Bool case analysis (E016), bounded quantifiers `∀ x ∈ l` (E025), `unfold` (E030), `refine` (E031).
-/

namespace E062Guide

/-- A Bool-valued list test, for the entries and the worked combinations. -/
def allEven (xs : List Nat) : Bool := xs.all (fun x => x % 2 == 0)

/-! # Part R · Reference entries -/

/-! ## From a Bool test on a list to a Prop -/

/-! ### R1. `unfold allEven` · goal: a defined name → its body -/
example (xs : List Nat) (P : Bool → Prop) (h : P (xs.all fun x => x % 2 == 0)) : P (allEven xs) := by
  unfold allEven
  exact h

/-! ### R2. `List.all_eq_true` · `l.all f = true ↔ ∀ x, x ∈ l → f x = true` · goal: Bool `all` → Prop `∀`
`∀ x ∈ l, Q x` is notation for `∀ x, x ∈ l → Q x`; core Lean prints the long form. -/
example {α : Type} (l : List α) (f : α → Bool) (P : Prop → Prop)
    (h : P (∀ x, x ∈ l → f x = true)) : P (l.all f = true) := by
  rw [List.all_eq_true]
  exact h

/-! ### R3. `refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩` · goal: an `↔` of two bounded `∀` → two goals
Each side is a function: take the hypothesis `h`, the element `x` and its membership proof `hx`. -/
example {α : Type} (l : List α) (A B : α → Prop) (hab : ∀ x, A x → B x) (hba : ∀ x, B x → A x) :
    (∀ x, x ∈ l → A x) ↔ (∀ x, x ∈ l → B x) := by
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  exact hab x (h x hx)
  exact hba x (h x hx)

/-! ## `decide`: the bridge between a decidable Prop and Bool -/

/-! ### R4. `of_decide_eq_true` · `{p : Prop} [Decidable p] : decide p = true → p` · closes `⊢ p` -/
example (p : Prop) [Decidable p] (h : (p : Bool) = true) : p := by
  exact of_decide_eq_true h

/-! ### R5. `decide_eq_true` · `{p : Prop} [Decidable p] : p → decide p = true` · closes `⊢ decide p = true` -/
example (p : Prop) [Decidable p] (hp : p) : (p : Bool) = true := by
  exact decide_eq_true hp

/-! ### R6. `Nat.lt_add_one` · `(n : Nat) : n < n + 1` · closes the goal -/
example (m : Nat) : m < m + 1 := by
  exact Nat.lt_add_one m

/-! ## `&&` and `==` -/

/-! ### R7. `rw [Bool.and_eq_true]` · `((a && b) = true) = (a = true ∧ b = true)` · goal: `&&` → `∧`
An `=` between Props, not an `↔`: use it with `rw`, not `exact`. After rewriting, `rw` tries `rfl`,
which closes a goal that has become `X ↔ X`. -/
example (a b : Bool) (P : Prop → Prop) (h : P (a = true ∧ b = true)) : P ((a && b) = true) := by
  rw [Bool.and_eq_true]
  exact h

/-! ### R8. `beq_iff_eq` · `{α} [BEq α] [LawfulBEq α] {a b : α} : (a == b) = true ↔ a = b` · goal: `==` → `=`
As a term, `beq_iff_eq` (or `.mp`, `.mpr`) proves the `↔` or one direction directly. -/
example {α : Type} [BEq α] [LawfulBEq α] (a b : α) (P : Prop → Prop) (h : P (a = b)) :
    P ((a == b) = true) := by
  rw [beq_iff_eq]
  exact h

/-! ## A Bool used where a Prop is expected -/

/-! ### R9. `(h : b)` with `b : Bool` · context: `h : b = true` (Lean inserts the coercion `· = true`) -/
example (b : Bool) (h : b) : b = true := by
  exact h

/-! ### R10. `rw [Bool.and_eq_true] at h` · context: `h : (a && b) = true` → `h : a = true ∧ b = true` -/
example (a b : Bool) (G : Prop) (g : a = true ∧ b = true → G) (h : a && b) : G := by
  rw [Bool.and_eq_true] at h
  exact g h

/-! ### R11. `h.1`, `h.2` (`And.left`, `And.right`) · closes a goal that is one side of `h : A ∧ B` -/
example (A B : Prop) (h : A ∧ B) : B := by
  exact h.2

/-! # Part W · Worked combinations (on `allEven`, not the exercise's `allPos`) -/

/-! ### W1. A Bool list test as a `∀`: R1, R2, R3, then R8 in each direction -/
example (xs : List Nat) : allEven xs = true ↔ ∀ x ∈ xs, x % 2 = 0 := by
  unfold allEven
  rw [List.all_eq_true]
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  exact beq_iff_eq.mp (h x hx)
  exact beq_iff_eq.mpr (h x hx)

/-! ### W2. A `decide` goal from a Prop proof: R5 with another arithmetic lemma
`Nat.le_add_right : (n k : Nat) → n ≤ n + k`. -/
example (m : Nat) : ((m ≤ m + 2 : Prop) : Bool) = true := by
  exact decide_eq_true (Nat.le_add_right m 2)

/-! ### W3. A nested `&&` hypothesis: R9, R10 twice (outer `&&` first), then R11 twice -/
example (a b c : Bool) (h : a && b && c) : b = true := by
  rw [Bool.and_eq_true] at h
  rw [Bool.and_eq_true] at h
  exact h.1.2

end E062Guide
