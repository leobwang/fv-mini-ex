/- Guide for E058 (Classical logic).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`A B : Prop` are arbitrary propositions and `G : Prop` stands for "whatever the goal is". A hypothesis
in an entry whose name starts with `h` is only there to finish the example; it shows what the goal
became.
Part W: worked combinations on tautologies that are NOT the exercise's.
Assumed: Lean basics (E001–E033), in particular `intro`/`exact`/`apply` (E003), anonymous
constructors `⟨_, _⟩` (E004, E005), `left`/`right` and `rcases` on `∨` (E006), `¬A` as `A → False`
(E008), focusing with `·` and `refine` with `?_` (E031).
-/

namespace E058Guide

/-! # Part R · Reference entries -/

/-! ## Proof by contradiction -/

/-! ### R1. `refine Classical.byContradiction fun hn => ?_` · goal `A` → context gains `hn : ¬A`, goal `False`
`Classical.byContradiction {p : Prop} : (¬p → False) → p`. It needs the axiom of choice (via the
excluded middle); core Lean has no `by_contra` tactic. -/
example (A G : Prop) (h : ¬A → G) (hg : ¬G) : A := by
  refine Classical.byContradiction fun hn => ?_
  exact hg (h hn)

/-! ### R2. `exact hna ha` · closes `False` from `ha : A` and `hna : ¬A`
`¬A` unfolds to `A → False`, so a negation is a function: apply it to a proof of `A`. -/
example (A : Prop) (ha : A) (hna : ¬A) : False := by
  exact hna ha

/-! ## Implications and case splits -/

/-! ### R3. `intro h` on `A → B` · context gains `h : A`, goal `B` -/
example (A B : Prop) (hb : B) : A → B := by
  intro h
  exact hb

/-! ### R4. `by_cases h : A` · goal list: one goal → two, with `h : A` and with `h : ¬A`
Works for every `A : Prop` (it uses the excluded middle when `A` is not decidable).
Goal order: first the goal with `h : A` (case `pos`), then the one with `h : ¬A` (case `neg`). -/
example (A G : Prop) (hpos : A → G) (hneg : ¬A → G) : G := by
  by_cases h : A
  · exact hpos h
  · exact hneg h

/-! ### R5. `apply h` with `h : A → B` · goal `B` → goal `A` -/
example (A B : Prop) (h : A → B) (ha : A) : B := by
  apply h
  exact ha

/-! ### R6. `absurd` · `absurd {a : Prop} {b : Sort v} : a → ¬a → b` · closes ANY goal from `a` and `¬a` -/
example (A G : Prop) (ha : A) (hna : ¬A) : G := by
  exact absurd ha hna

/-! ### R7. `rcases Classical.em A with ha | hna` · goal list: one goal → two, with `ha : A` and `hna : ¬A`
`Classical.em (p : Prop) : p ∨ ¬p` is the excluded middle; `rcases` splits the `∨` (E006). -/
example (A G : Prop) (hpos : A → G) (hneg : ¬A → G) : G := by
  rcases Classical.em A with ha | hna
  · exact hpos ha
  · exact hneg hna

/-! ## Disjunctions and negations as goals -/

/-! ### R8. `right` · goal `A ∨ B` → goal `B` -/
example (A B : Prop) (hb : B) : A ∨ B := by
  right
  exact hb

/-! ### R9. `intro hb` on `¬B` · context gains `hb : B`, goal `False`
`¬B` is `B → False`, so `intro` works on it as on any implication (R3). -/
example (B : Prop) (h : B → False) : ¬B := by
  intro hb
  exact h hb

/-! ### R10. `exact h ⟨ha, hb⟩` with `h : ¬(A ∧ B)` · closes `False`
The argument of `h` is a proof of `A ∧ B`, built with the anonymous constructor `⟨ha, hb⟩`. -/
example (A B : Prop) (h : ¬(A ∧ B)) (ha : A) (hb : B) : False := by
  exact h ⟨ha, hb⟩

/-! ### R11. `left` · goal `A ∨ B` → goal `A` -/
example (A B : Prop) (ha : A) : A ∨ B := by
  left
  exact ha

/-! # Part W · Worked combinations (not the exercise's tautologies) -/

/-! ### W1. `¬(A → B) → A`: R3, then R1, then R2 with a function built by `fun` and R6 -/
example (A B : Prop) : ¬(A → B) → A := by
  intro h
  refine Classical.byContradiction fun hna => ?_
  exact h (fun ha => absurd ha hna)

/-! ### W2. `(A → B) → ¬A ∨ B`: R3, R4, then R8 / R11 in the two cases -/
example (A B : Prop) : (A → B) → ¬A ∨ B := by
  intro h
  by_cases ha : A
  · right
    exact h ha
  · left
    exact ha

/-! ### W3. `(¬A → B) → A ∨ B`: R3, R7, then R11 / R8 -/
example (A B : Prop) : (¬A → B) → A ∨ B := by
  intro h
  rcases Classical.em A with ha | hna
  · left
    exact ha
  · right
    exact h hna

/-! ### W4. `¬(A ∨ B) → ¬A`: no classical step needed; R3, R9, R2 with `Or.inl` -/
example (A B : Prop) : ¬(A ∨ B) → ¬A := by
  intro h
  intro ha
  exact h (Or.inl ha)

end E058Guide
