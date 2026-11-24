/- Guide for E024 (List library facts).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on other statements (two different maps, three appended lists, `foldl`
on a concrete list), not on the exercise's.
Assumed: Lean basics up to E023 (`rw` E009, `omega` E011, lists E015, `have` E021, `∘` E022,
implicit arguments E023).
-/

namespace E024Guide

/-! # Part R · Reference entries -/

/-! ## Lengths -/

/-! ### R1. `rw [List.length_map]` · goal: `(List.map f l).length` → `l.length`
`List.length_map : (List.map f as).length = as.length`: mapping keeps the number of elements. -/
example {α β : Type} (f : α → β) (l : List α) (P : Nat → Prop) (h : P l.length) :
    P (l.map f).length := by
  rw [List.length_map]
  exact h

/-! ### R2. `rw [List.length_append]` · goal: `(l ++ l').length` → `l.length + l'.length` -/
example {α : Type} (l l' : List α) (P : Nat → Prop) (h : P (l.length + l'.length)) :
    P (l ++ l').length := by
  rw [List.length_append]
  exact h

/-! ### R3. `have h := List.length_filter_le p l` · context gains `h`; goal unchanged
`List.length_filter_le (p : α → Bool) (l : List α) : (List.filter p l).length ≤ l.length`.
Its two arguments are explicit, so you supply them; `have` then names the instance. -/
example {α : Type} (p : α → Bool) (l : List α) (G : Prop)
    (g : (l.filter p).length ≤ l.length → G) : G := by
  have h := List.length_filter_le p l
  exact g h

/-! ### R4. `omega` with a hypothesis · closes linear `Nat` goals, using the `≤` facts in context
`omega` treats `l.length`, `l'.length`, `(List.filter p l).length` as unknown numbers. -/
example {α : Type} (l l' : List α) (n : Nat) (h : n ≤ l.length) : n ≤ l.length + l'.length := by
  omega

/-! ## Folds -/

/-! ### R5. `exact List.foldl_append` · closes the goal; the implicit arguments come from the goal
`List.foldl_append : List.foldl f b (l ++ l') = List.foldl f (List.foldl f b l) l'`. All of
`f b l l'` are implicit `{…}`: Lean reads them off the goal, so the bare name is a proof. -/
example {α β : Type} (f : β → α → β) (b : β) (l l' : List α) :
    (l ++ l').foldl f b = l'.foldl f (l.foldl f b) := by
  exact List.foldl_append

/-! ## Filter after map -/

/-! ### R6. `rw [List.filter_map]` · goal: `List.filter p (List.map f l)` → `List.map f (List.filter (p ∘ f) l)`
`List.filter_map : List.filter p (List.map f l) = List.map f (List.filter (p ∘ f) l)`: testing
`p` on `f x` is testing `p ∘ f` on `x`, so the filter can move inside the map. -/
example {α β : Type} (f : α → β) (p : β → Bool) (l : List α) (P : List β → Prop)
    (h : P (List.map f (List.filter (p ∘ f) l))) : P ((l.map f).filter p) := by
  rw [List.filter_map]
  exact h

/-! ### R7. `rfl` · closes an equation whose sides differ only by `g ∘ f` vs `fun x => g (f x)`
`Function.comp` unfolds to the lambda, wherever it sits inside `P`. -/
example {α β γ δ : Type} (f : α → β) (g : β → γ) (P : (α → γ) → δ) :
    P (g ∘ f) = P (fun x => g (f x)) := by
  rfl

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. `foldl` computes left to right: `foldl f b [x, y, z] = f (f (f b x) y) z` -/
example : [1, 2, 3].foldl (· + ·) 0 = 6 := by
  rfl

example : [1, 2, 3].foldl (fun acc x => 10 * acc + x) 0 = 123 := by
  rfl

/-! ### W2. Several length rewrites in one `rw`: R2, then R1 twice -/
example {α β γ : Type} (f : α → γ) (g : β → γ) (l : List α) (l' : List β) :
    (l.map f ++ l'.map g).length = l.length + l'.length := by
  rw [List.length_append]
  rw [List.length_map]
  rw [List.length_map]

/-! ### W3. A library bound, a rewrite, then `omega`: R3, R1, R4 -/
example {α β : Type} (p : α → Bool) (f : α → β) (l : List α) :
    (l.filter p).length ≤ (l.map f).length + 1 := by
  have h := List.length_filter_le p l
  rw [List.length_map]
  omega

/-! ### W4. The fold lemma used with `rw`, twice, on three lists -/
example {α β : Type} (f : β → α → β) (b : β) (l₁ l₂ l₃ : List α) :
    (l₁ ++ l₂ ++ l₃).foldl f b = l₃.foldl f (l₂.foldl f (l₁.foldl f b)) := by
  rw [List.foldl_append]
  rw [List.foldl_append]

end E024Guide
