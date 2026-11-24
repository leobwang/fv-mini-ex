/- Guide for E006 (Or).
Part R: one reference entry per tactic or proof term the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`A B C G : Prop` are arbitrary propositions; `G` stands for "whatever the goal is". A hypothesis `k`
in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on propositions that are NOT the exercise's.
Assumed: E001–E005 (`intro`/`exact`/`apply`, `⟨_, _⟩`, `constructor` on `∧` and `↔`, `·` blocks,
`rintro ⟨ha, hb⟩`, `obtain`).
-/

namespace E006Guide

/-! # Part R · Reference entries -/

/-! ## Using an `∨` hypothesis: one goal per side -/

/-! ### R1. `cases h with | inl ha => tac₁ | inr hb => tac₂` · goal list: one goal per side of `h : A ∨ B`
A proof of `A ∨ B` was built either as `Or.inl ha` (from `ha : A`) or as `Or.inr hb` (from `hb : B`).
`cases` asks for the goal in both situations: `tac₁` sees `ha : A`, `tac₂` sees `hb : B`, and `h` is gone.
Each alternative starts with `|`, names its constructor (`inl` = left, `inr` = right), then the new name. -/
example (A B G : Prop) (k1 : A → G) (k2 : B → G) (h : A ∨ B) : G := by
  cases h with
    | inl ha => exact k1 ha
    | inr hb => exact k2 hb

/-! ### R2. `rcases h with ha | hb` · goal list: `G` → two goals `G`; context: `h` → `ha : A` / `hb : B`
The same split as R1 in pattern form: `ha | hb` reads "either `ha` or `hb`". Both goals stay open, the
`A` case first; close them in order (or one `·` block each). -/
example (A B G : Prop) (k1 : A → G) (k2 : B → G) (h : A ∨ B) : G := by
  rcases h with ha | hb
  exact k1 ha
  exact k2 hb

/-! ## Proving an `∨` goal: choose a side -/

/-! ### R3. `right` · goal `A ∨ B` → goal `B`
Commits to the right side: after it, `A` is no longer an option. -/
example (A B : Prop) (hb : B) : A ∨ B := by
  right
  exact hb

/-! ### R4. `left` · goal `A ∨ B` → goal `A` -/
example (A B : Prop) (ha : A) : A ∨ B := by
  left
  exact ha

/-! ## The same choice as a proof term -/

/-! ### R5. `Or.inl ha : A ∨ B` (`ha : A`) · `exact Or.inl ha` closes `A ∨ B`
`Or.inl` is the left constructor of `Or`; `B` is read off the goal. -/
example (A B : Prop) (ha : A) : A ∨ B := by
  exact Or.inl ha

/-! ### R6. `Or.inr hb : A ∨ B` (`hb : B`) · `exact Or.inr hb` closes `A ∨ B` -/
example (A B : Prop) (hb : B) : A ∨ B := by
  exact Or.inr hb

/-! ## Nested patterns: `∧` and `∨` together -/

/-! ### R7. `rintro ⟨ha, hb | hc⟩` · goal `A ∧ (B ∨ C) → G` → two goals `G`
`⟨_, _⟩` takes the `∧` apart; inside it, `hb | hc` splits the `∨`. Both goals keep `ha : A`. -/
example (A B C G : Prop) (k1 : A → B → G) (k2 : A → C → G) : A ∧ (B ∨ C) → G := by
  rintro ⟨ha, hb | hc⟩
  exact k1 ha hb
  exact k2 ha hc

/-! ### R8. `rintro (⟨ha, hb⟩ | ⟨ha', hc⟩)` · goal `(A ∧ B) ∨ (A ∧ C) → G` → two goals `G`
Here the `∨` is outermost, so the alternative `|` is the outer pattern. The parentheses are required:
`rintro p | q` would read as two separate patterns. Each side has its own copy of `A`. -/
example (A B C G : Prop) (k1 : A → B → G) (k2 : A → C → G) : (A ∧ B) ∨ (A ∧ C) → G := by
  rintro (⟨ha, hb⟩ | ⟨ha', hc⟩)
  exact k1 ha hb
  exact k2 ha' hc

/-! ### R9. `exact ⟨ha, Or.inl hb⟩` · closes `A ∧ (B ∨ C)`: a pair whose second half is an `∨` proof
The anonymous constructor (E004) builds the `∧`; inside it, `Or.inl hb : B ∨ C` (R5). With `hc : C`,
write `⟨ha, Or.inr hc⟩` (R6). -/
example (A B C : Prop) (ha : A) (hb : B) : A ∧ (B ∨ C) := by
  exact ⟨ha, Or.inl hb⟩

/-! # Part W · Worked combinations (not the exercise's propositions) -/

/-! ### W1. R1 with the same tactic in both branches: `A ∨ A → A` -/
example (A : Prop) : A ∨ A → A := by
  intro h
  cases h with
    | inl ha => exact ha
    | inr ha => exact ha

/-! ### W2. Three alternatives: `A ∨ B ∨ C` is `A ∨ (B ∨ C)`, and `ha | hb | hc` splits both `∨`s
Then R4, or R3 followed by R4 / R3, picks the side. -/
example (A B C : Prop) : A ∨ B ∨ C → A ∨ C ∨ B := by
  intro h
  rcases h with ha | hb | hc
  · left
    exact ha
  · right
    right
    exact hb
  · exact Or.inr (Or.inl hc)

/-! ### W3. R7, then a different side in each goal -/
example (A B C : Prop) : A ∧ (B ∨ C) → C ∨ A := by
  rintro ⟨ha, _ | hc⟩
  · right
    exact ha
  · left
    exact hc

/-! ### W4. R8, then the shared part: both alternatives provide `A` -/
example (A B C : Prop) : (A ∧ B) ∨ (A ∧ C) → A := by
  rintro (⟨ha, _⟩ | ⟨ha, _⟩)
  · exact ha
  · exact ha

/-! ### W5. `obtain` splits a hypothesis that is already in the context, with the same patterns -/
example (A B C : Prop) (h : A ∧ (B ∨ C)) : (B ∨ C) ∧ A := by
  obtain ⟨ha, hb | hc⟩ := h
  · exact ⟨Or.inl hb, ha⟩
  · exact ⟨Or.inr hc, ha⟩

end E006Guide
