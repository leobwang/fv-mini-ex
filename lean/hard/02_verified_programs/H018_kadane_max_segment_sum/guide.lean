/- Guide for H018 (Kadane's maximum segment sum).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries about definitions use the guide's own `Both`, `shift` and `lastOr`, which are NOT the
exercise's.
Part W: worked combinations on a running maximum `foldl max` and on list lengths (not the exercise's).
Assumed: Lean basics (E001–E033). No Mathlib: everything here is core Lean.
-/

namespace H018Guide

/-! # Part R · Reference entries -/

/-! ## Building the invariant at the start (`inv_nil`) -/

/-- A predicate defined as a conjunction with an `∃` inside, like a loop invariant. -/
def Both {α : Type} (A : Prop) (Q : α → Prop) (y : α) : Prop := A ∧ ∃ z, Q z ∧ z = y

/-! ### R1. `refine ⟨?_, ⟨w, ?_, rfl⟩⟩` · goal list: a defined `∧`/`∃` → only the `?_` parts
The anonymous constructor `⟨…⟩` looks through the definition `Both` to the `∧` and `∃` it stands
for. `w` is the witness of the `∃`; `rfl` proves `w = y` when both sides are the same term. -/
example {α : Type} (A : Prop) (Q : α → Prop) (y : α) (hA : A) (hy : Q y) : Both A Q y := by
  refine ⟨?_, ⟨y, ?_, rfl⟩⟩
  · exact hA
  · exact hy

/-! ### R2. `List.nil_infix`, `List.nil_suffix` · `[] <:+: l`, `[] <:+ l` · close the goal
`l₁ <:+: l₂` (`List.IsInfix`) is `∃ s t, s ++ l₁ ++ t = l₂`: `l₁` is a contiguous segment of `l₂`.
`l₁ <:+ l₂` (`List.IsSuffix`) is `∃ t, t ++ l₁ = l₂`. The empty list is both, of every list. -/
example {α : Type} (l : List α) : [] <:+: l ∧ [] <:+ l := by
  refine ⟨List.nil_infix, ?_⟩
  exact List.nil_suffix

/-! ### R3. `List.eq_nil_of_infix_nil` · `l <:+: [] → l = []` · goal: `l` → `[]`
`List.eq_nil_of_suffix_nil : l <:+ [] → l = []` is the same for suffixes. -/
example {α : Type} (l : List α) (P : List α → Prop) (h : l <:+: []) (hP : P []) : P l := by
  rw [List.eq_nil_of_infix_nil h]
  exact hP

/-! ### R4. `List.sum_nil` · `([] : List α).sum = 0` · goal -/
example (P : Int → Prop) (h : P 0) : P ([] : List Int).sum := by
  rw [List.sum_nil]
  exact h

/-! ## One step of the loop (`inv_step`) -/

/-! ### R5. `obtain ⟨h1, h2, ⟨y, hy, hs⟩⟩ := h` · context: a defined `∧`/`∃` → its pieces
Like R1, the pattern looks through a definition. Each `⟨y, hy, hs⟩` opens one `∃ y, _ ∧ _`. -/
example {α : Type} (A B : Prop) (Q R : α → Prop) (G : Prop)
    (h : A ∧ B ∧ ∃ y, Q y ∧ R y) (g : A → B → ∀ y, Q y → R y → G) : G := by
  obtain ⟨h1, h2, ⟨y, hy, hs⟩⟩ := h
  exact g h1 h2 y hy hs

/-! ### R6. `List.suffix_concat_iff` · `l₁ <:+ l₂ ++ [a] ↔ l₁ = [] ∨ ∃ t, l₁ = t ++ [a] ∧ t <:+ l₂`
`.mp` is the `→` direction. Context: a suffix of `l₂ ++ [a]` is `[]` or an old suffix `t` plus `a`. -/
example {α : Type} (l₁ l₂ : List α) (a : α) (G : Prop) (h : l₁ <:+ l₂ ++ [a])
    (g : (l₁ = [] ∨ ∃ t, l₁ = t ++ [a] ∧ t <:+ l₂) → G) : G := by
  have h' := List.suffix_concat_iff.mp h
  exact g h'

/-! ### R7. `rcases h with rfl | ⟨t, rfl, ht⟩` · goal list: one goal per side of `∨`
`rfl` in a pattern substitutes the equation `l = …` away: `l` is replaced everywhere. -/
example {α : Type} (l : List α) (a : α) (Q : List α → Prop) (P : List α → Prop)
    (h : l = [] ∨ ∃ t, l = t ++ [a] ∧ Q t) (h0 : P []) (h1 : ∀ t, Q t → P (t ++ [a])) : P l := by
  rcases h with rfl | ⟨t, rfl, ht⟩
  · exact h0
  · exact h1 t ht

/-! ### R8. `List.sum_append` · `(l₁ ++ l₂).sum = l₁.sum + l₂.sum` · goal -/
example (l₁ l₂ : List Int) (P : Int → Prop) (h : P (l₁.sum + l₂.sum)) : P (l₁ ++ l₂).sum := by
  rw [List.sum_append]
  exact h

/-! ### R9. `List.sum_cons` · `(a :: l).sum = a + l.sum` · goal
`[x]` is `x :: []`, so `simp` turns `[x].sum` into `x` with R9, R4 and `Int.add_zero`. -/
example (a : Int) (l : List Int) (P : Int → Prop) (h : P (a + l.sum)) : P (a :: l).sum := by
  rw [List.sum_cons]
  exact h

/-! ### R10. `omega` · closes linear arithmetic over `Int`/`Nat`, `max` and `min` included
`max a b` is unfolded into its two cases; hypotheses in the context are used. -/
example (a b c : Int) (h : a ≤ c) (h' : b ≤ c) : max a b ≤ c := by
  omega

/-! ### R11. `by_cases h0 : c` · goal list: the same goal twice, with `h0 : c`, then `h0 : ¬c` -/
example (c : Prop) (G : Prop) (h1 : c → G) (h2 : ¬c → G) : G := by
  by_cases h0 : c
  · exact h1 h0
  · exact h2 h0

/-! ### R12. `List.suffix_concat_iff.mpr (.inr ⟨t, rfl, ?_⟩)` · goal: `t ++ [a] <:+ l ++ [a]` → `t <:+ l`
`.mpr` is the `←` direction of R6; `.inr` picks the right side of the `∨` (Lean infers `Or.inr`). -/
example {α : Type} (t l : List α) (a : α) (ht : t <:+ l) : t ++ [a] <:+ l ++ [a] := by
  refine List.suffix_concat_iff.mpr (.inr ⟨t, rfl, ?_⟩)
  exact ht

/-- A step function whose body is a `let` and a pair, like a loop body. -/
def shift (q : Int × Int) (y : Int) : Int × Int :=
  let d := q.1 - y
  (d, q.2 + d)

/-! ### R13. `simp only [f]` · goal: `(f st x).1` → the first component of `f`'s body
It unfolds `f`, substitutes the `let`, and reduces `(a, b).1` to `a`. `st.1`, `st.2` print as
`st.fst`, `st.snd`. -/
example (st : Int × Int) (x : Int) (P : Int → Prop) (h : P (st.1 - x)) : P (shift st x).1 := by
  simp only [shift]
  exact h

/-! ### R14. `List.infix_concat_iff` · `l₁ <:+: l₂ ++ [a] ↔ l₁ <:+ l₂ ++ [a] ∨ l₁ <:+: l₂`
A segment of `l₂ ++ [a]` either ends at the new `a` (a suffix) or lies inside `l₂`.
`rcases … with h1 | h1` gives one goal per case (R7). -/
example {α : Type} (l₁ l₂ : List α) (a : α) (G : Prop) (h : l₁ <:+: l₂ ++ [a])
    (g1 : l₁ <:+ l₂ ++ [a] → G) (g2 : l₁ <:+: l₂ → G) : G := by
  rcases List.infix_concat_iff.mp h with h1 | h1
  · exact g1 h1
  · exact g2 h1

/-! ### R15. `List.IsSuffix.isInfix` · `l₁ <:+ l₂ → l₁ <:+: l₂` · goal
Dot notation: for `h : l₁ <:+ l₂`, `h.isInfix : l₁ <:+: l₂`. -/
example {α : Type} (l₁ l₂ : List α) (h : l₁ <:+ l₂) : l₁ <:+: l₂ := by
  apply List.IsSuffix.isInfix
  exact h

/-! ## The whole fold (`inv_foldl`) -/

/-! ### R16. `induction l generalizing p s with` · goal list, and `ih` quantified over `p s`
Without `generalizing`, `ih` is about the fixed `p s`; a fold changes both at every step.
The arms are `?_` here so both goals stay open; in a proof write the arm's tactics after `=>`. -/
example {α β : Type} (f : β → α → β) (I : List α → β → Prop)
    (step : ∀ p s x, I p s → I (p ++ [x]) (f s x)) (l p : List α) (s : β) (h : I p s) :
    I (p ++ l) (l.foldl f s) := by
  induction l generalizing p s with | nil => ?_ | cons x l ih => ?_
  · simpa using h
  · simpa using ih (p ++ [x]) (f s x) (step p s x h)

/-! ### R17. `List.foldl_cons` · `foldl f b (a :: l) = foldl f (f b a) l` · goal
`List.foldl_nil : foldl f b [] = b`. `l.foldl f b` is `List.foldl f b l`. -/
example {α β : Type} (f : β → α → β) (b : β) (a : α) (l : List α) (P : β → Prop)
    (h : P (List.foldl f (f b a) l)) : P (List.foldl f b (a :: l)) := by
  rw [List.foldl_cons]
  exact h

/-! ### R18. `List.append_nil`, `List.nil_append` · `l ++ [] = l`, `[] ++ l = l` · goal -/
example {α : Type} (p : List α) (P : List α → Prop) (h : P p) : P (p ++ []) := by
  rw [List.append_nil]
  exact h

/-! ### R19. `List.append_assoc`, `List.singleton_append` · goal: `p ++ [x] ++ l` → `p ++ x :: l`
`++` groups to the left. This is the form `simp` puts both `ih` and the goal in. -/
example {α : Type} (p l : List α) (x : α) (P : List α → Prop) (h : P (p ++ x :: l)) :
    P (p ++ [x] ++ l) := by
  rw [List.append_assoc]
  rw [List.singleton_append]
  exact h

/-! ### R20. `simpa using e` · closes the goal: simplify `e`'s type and the goal, then match them
Here `simp` uses R17–R19 on both. -/
example {α : Type} (P : List α → Prop) (p l : List α) (x : α) (e : P (p ++ [x] ++ l)) :
    P (p ++ x :: l) := by
  simpa using e

/-! ## The main theorems -/

/-! ### R21. `h.1`, `h.2.2.1` · projections of `A ∧ B ∧ C ∧ D` (nested to the right)
`h.1 : A`, `h.2 : B ∧ C ∧ D`, `h.2.1 : B`, `h.2.2.1 : C`, `h.2.2.2 : D`. A `∀` inside is applied
to arguments: `h.1 x hx`. -/
example (A B C D : Prop) (h : A ∧ B ∧ C ∧ D) : C := by
  exact h.2.2.1

/-- A function defined by a fold, like a one-pass algorithm. -/
def lastOr (xs : List Nat) : Nat := xs.foldl (fun _ x => x) 0

/-! ### R22. `exact h` up to unfolding · closes `P (f xs)` with `h : P (body of f)`
`exact` compares types after unfolding definitions, so no `simp only [f]` is needed. -/
example (xs : List Nat) (P : Nat → Prop) (h : P (xs.foldl (fun _ x => x) 0)) : P (lastOr xs) := by
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-- W1's invariant: every element read so far is at most the accumulator `m`. -/
def AllLe (p : List Nat) (m : Nat) : Prop := ∀ y, y ∈ p → y ≤ m

/-! ### W1. A fold invariant: one step (`intro` through the definition, `simp at hy`, R7, R10),
the fold (R16, R20), the end (R20 with the start fact, then R22-style `exact`) -/
theorem allLe_step (p : List Nat) (m x : Nat) (h : AllLe p m) : AllLe (p ++ [x]) (max m x) := by
  intro y hy
  simp at hy
  rcases hy with hy | hy
  · have := h y hy
    omega
  · omega

theorem allLe_foldl (l p : List Nat) (m : Nat) (h : AllLe p m) : AllLe (p ++ l) (l.foldl max m) := by
  induction l generalizing p m with
    | nil => simpa using h
    | cons x l ih => simpa using ih (p ++ [x]) (max m x) (allLe_step p m x h)

example (xs : List Nat) (y : Nat) (hy : y ∈ xs) : y ≤ xs.foldl max 0 := by
  have hI : AllLe xs (xs.foldl max 0) := by
    simpa using allLe_foldl xs [] 0 (by simp [AllLe])
  exact hI y hy

/-! ### W2. Suffixes of `l ++ [a]` by cases: R6, R7, then `simp` and `omega` -/
example (l : List Nat) (a : Nat) (hl : ∀ t, t <:+ l → t.length ≤ l.length) :
    ∀ ys, ys <:+ l ++ [a] → ys.length ≤ l.length + 1 := by
  intro ys hys
  rcases List.suffix_concat_iff.mp hys with rfl | ⟨t, rfl, ht⟩
  · simp
  · have := hl t ht
    simp
    omega

end H018Guide
