/- Guide for E005 (And and Iff).
Part R: one reference entry per tactic or proof term the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`A B C G : Prop` are arbitrary propositions; `G` stands for "whatever the goal is". A hypothesis `k`
in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on propositions that are NOT the exercise's.
Assumed: E001–E004 (`rfl`, `decide`, `def`, `intro`/`exact`/`apply`, `⟨_, _⟩`, `.1`/`.2`, `fun`).
-/

namespace E005Guide

/-! # Part R · Reference entries -/

/-! ## Splitting an `↔` goal -/

/-! ### R1. `constructor` on `A ↔ B` · goal list: one goal → two goals `A → B` (case `mp`), `B → A` (case `mpr`)
`A ↔ B` ("A if and only if B") is a pair of implications; `constructor` asks for both. -/
example (A B : Prop) (f : A → B) (g : B → A) : A ↔ B := by
  constructor
  exact f
  exact g

/-! ### R2. `· tacs` · goal list: work on the first goal only; the block must close it
Type `·` as `\.` (a plain `.` also works). Every line of the block is indented under the `·`. -/
example (A B : Prop) (f : A → B) (g : B → A) : A ↔ B := by
  constructor
  · intro ha
    exact f ha
  · exact g

/-! ## Taking an `∧` apart -/

/-! ### R3. `rintro ⟨ha, hb⟩` · goal `A ∧ B → G` → goal `G`; context gains `ha : A`, `hb : B`
`intro` and destructuring in one step: the pattern `⟨ha, hb⟩` names the two halves. -/
example (A B G : Prop) (k : A → B → G) : A ∧ B → G := by
  rintro ⟨ha, hb⟩
  exact k ha hb

/-! ### R4. `obtain ⟨ha, hb⟩ := h` · context: `h : A ∧ B` → `ha : A`, `hb : B`; goal unchanged
The same pattern as R3, for a conjunction that is already in the context. -/
example (A B G : Prop) (h : A ∧ B) (k : B → G) : G := by
  obtain ⟨ha, hb⟩ := h
  exact k hb

/-! ## Building an `∧` -/

/-! ### R5. `exact ⟨ha, hb⟩` · closes `A ∧ B` (the anonymous constructor of E004) -/
example (A B : Prop) (ha : A) (hb : B) : A ∧ B := by
  exact ⟨ha, hb⟩

/-! ### R6. `constructor` on `A ∧ B` · goal list: one goal → `A` (case `left`), `B` (case `right`)
The step-by-step alternative to R5. It splits only the outermost `∧`. -/
example (A B : Prop) (ha : A) (hb : B) : A ∧ B := by
  constructor
  exact ha
  exact hb

/-! ## Three-part conjunctions: `∧` nests to the right -/

/-! ### R7. `rintro ⟨ha, hb, hc⟩` · goal `A ∧ B ∧ C → G` → `G`; context gains all three
`A ∧ B ∧ C` is `A ∧ (B ∧ C)`, and the flat pattern `⟨ha, hb, hc⟩` means `⟨ha, ⟨hb, hc⟩⟩`. -/
example (A B C G : Prop) (k : A → B → C → G) : A ∧ B ∧ C → G := by
  rintro ⟨ha, hb, hc⟩
  exact k ha hb hc

/-! ### R8. `rintro ⟨⟨ha, hb⟩, hc⟩` · goal `(A ∧ B) ∧ C → G` → `G`; context gains all three
Grouping on the left needs inner brackets in the pattern, matching the parentheses of the type. -/
example (A B C G : Prop) (k : A → B → C → G) : (A ∧ B) ∧ C → G := by
  rintro ⟨⟨ha, hb⟩, hc⟩
  exact k ha hb hc

/-! ### R9. `exact ⟨ha, hb, hc⟩` · closes `A ∧ B ∧ C` (flat brackets nest to the right) -/
example (A B C : Prop) (ha : A) (hb : B) (hc : C) : A ∧ B ∧ C := by
  exact ⟨ha, hb, hc⟩

/-! ### R10. `exact ⟨⟨ha, hb⟩, hc⟩` · closes `(A ∧ B) ∧ C` (inner brackets for the left group) -/
example (A B C : Prop) (ha : A) (hb : B) (hc : C) : (A ∧ B) ∧ C := by
  exact ⟨⟨ha, hb⟩, hc⟩

/-! ## Using an `↔` hypothesis -/

/-! ### R11. `h.mp` (`h : A ↔ B`) is a proof of `A → B` · `apply h.mp`: goal `B` → goal `A`
`.mp` ("modus ponens") is the left-to-right half; `h.mp ha : B` when `ha : A`. Same as `h.1`. -/
example (A B : Prop) (h : A ↔ B) (ha : A) : B := by
  apply h.mp
  exact ha

/-! ### R12. `h.mpr` (`h : A ↔ B`) is a proof of `B → A` · `apply h.mpr`: goal `A` → goal `B`
`.mpr` ("modus ponens reverse") is the right-to-left half; `h.mpr hb : A` when `hb : B`. Same as `h.2`. -/
example (A B : Prop) (h : A ↔ B) (hb : B) : A := by
  apply h.mpr
  exact hb

/-! ## Reaching `False` -/

/-! ### R13. `apply k` (`k : B → False`) · goal `False` → goal `B`
`False` is the proposition with no proof. `k : B → False` says "`B` is impossible": to reach `False`
it suffices to prove `B`. This is `apply` from E003 with conclusion `False`. -/
example (B : Prop) (k : B → False) (hb : B) : False := by
  apply k
  exact hb

/-! # Part W · Worked combinations (not the exercise's propositions) -/

/-! ### W1. R8 then R5: regroup and drop a part; `_` in a pattern discards that piece -/
example (A B C : Prop) : (A ∧ B) ∧ C → C ∧ A := by
  rintro ⟨⟨ha, _⟩, hc⟩
  exact ⟨hc, ha⟩

/-! ### W2. R1, R2, then R3/R5 in each direction -/
example (A : Prop) : A ∧ A ↔ A := by
  constructor
  · rintro ⟨ha, _⟩
    exact ha
  · intro ha
    exact ⟨ha, ha⟩

/-! ### W3. Chaining two `↔` hypotheses (R11 twice), as one term read inside out -/
example (A B C : Prop) (h1 : A ↔ B) (h2 : B ↔ C) (ha : A) : C := by
  exact h2.mp (h1.mp ha)

/-! ### W4. Both directions at once: `t <;> u` runs `u` on every goal `t` leaves -/
example (A : Prop) : A ↔ A := by
  constructor <;> intro h <;> exact h

end E005Guide
