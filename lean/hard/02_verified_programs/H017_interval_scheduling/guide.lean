/- Guide for H017 (Greedy interval scheduling is optimal).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` or `k` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (lists of numbers, a filter, a
strictly increasing selection).
Assumed: Lean basics (E001–E033). Core Lean only: no Mathlib.
-/

namespace H017Guide

/-- The guide's own threshold scan: keep `x` when it is at least the bound `t`, then demand `x + 1`. -/
def bump : Nat → List Nat → List Nat
  | _, [] => []
  | t, x :: xs => if t ≤ x then x :: bump (x + 1) xs else bump t xs

/-- The guide's own chain predicate: every entry is at least the bound, and the bound rises past it. -/
def Above : Nat → List Nat → Prop
  | _, [] => True
  | t, x :: xs => t ≤ x ∧ Above (x + 1) xs

/-- The guide's own sortedness predicate, a `def` around `List.Pairwise`. -/
def Asc (xs : List Nat) : Prop := xs.Pairwise (fun a b => a ≤ b)

/-! # Part R · Reference entries -/

/-! ## Part 1 · Induction on the list with a moving threshold (MILESTONE 1) -/

/-! ### R1. `induction xs generalizing t` · goal list: one goal per constructor of `List`; `t` stays
universally quantified in the induction hypothesis
Without `with`, the new names are inaccessible (`head✝`, `tail✝`, `tail_ih✝`). Write
`induction xs generalizing t with | nil => … | cons x xs ih => …` to name them. -/
example {α : Type} (P : Nat → List α → Prop) (h0 : ∀ t, P t [])
    (hs : ∀ x xs, (∀ t, P t xs) → ∀ t, P t (x :: xs)) (t : Nat) (xs : List α) : P t xs := by
  induction xs generalizing t
  case nil => exact h0 t
  case cons x xs ih => exact hs x xs ih t

/-! ### R2. `simp [f]` · goal closed: `f` at `[]` unfolds to `[]`, and `[] <+ l` is `List.nil_sublist` -/
example (t : Nat) : (bump t []).Sublist [] := by
  simp [bump]

/-! ### R3. `simp only [f]` · goal: `f t (x :: xs)` → the body of `f`'s `cons` clause (an `if`) -/
example (t x : Nat) (xs : List Nat) (P : List Nat → Prop)
    (h : P (if t ≤ x then x :: bump (x + 1) xs else bump t xs)) : P (bump t (x :: xs)) := by
  simp only [bump]
  exact h

/-! ### R4. `split` (an `if` in the goal) · goal list: two goals; context gains the condition `h✝ : c`
or `h✝ : ¬c`, and the `if` becomes that branch -/
example {α : Type} (c : Prop) [Decidable c] (a b : α) (P : α → Prop) (ha : P a) (hb : P b) :
    P (if c then a else b) := by
  split
  · exact ha
  · exact hb

/-! ### R5. `List.Sublist.cons_cons` · `l₁ <+ l₂ → a :: l₁ <+ a :: l₂` · goal: keep the same head on
both sides. Term form: `h.cons_cons a`. -/
example {α : Type} (a : α) (l₁ l₂ : List α) (h : l₁.Sublist l₂) : (a :: l₁).Sublist (a :: l₂) := by
  apply List.Sublist.cons_cons
  exact h

/-! ### R6. `List.Sublist.cons` · `l₁ <+ l₂ → l₁ <+ a :: l₂` · goal: skip the head on the right.
Term form: `h.cons a`. -/
example {α : Type} (a : α) (l₁ l₂ : List α) (h : l₁.Sublist l₂) : l₁.Sublist (a :: l₂) := by
  apply List.Sublist.cons
  exact h

/-! ## Part 2 · A recursive `Prop` (MILESTONE 2) -/

/-! ### R7. `trivial` · goal closed: a recursive predicate at `[]` unfolds to `True` -/
example (t : Nat) : Above t [] := by
  trivial

/-! ### R8. `refine ⟨?_, ?_⟩` (or `exact ⟨e₁, e₂⟩`) · goal list: a predicate whose clause is `A ∧ B`
→ two goals. Lean unfolds the definition to see the `∧`. -/
example (t x : Nat) (xs : List Nat) (h1 : t ≤ x) (h2 : Above (x + 1) xs) : Above t (x :: xs) := by
  refine ⟨?_, ?_⟩
  · exact h1
  · exact h2

/-! ### R9. `assumption` (or the term `by assumption`) · goal closed by a hypothesis, even an
inaccessible one such as the `h✝` that `split` adds -/
example (t x : Nat) : t ≤ x → t ≤ x := by
  intro _
  assumption

/-! ## Part 3 · Lowering the threshold (MILESTONE 3) -/

/-! ### R10. `cases S` · goal list: `S` is `[]` or `i :: is` -/
example {α : Type} (P : List α → Prop) (h0 : P []) (h1 : ∀ i is, P (i :: is)) (S : List α) : P S := by
  cases S
  case nil => exact h0
  case cons i is => exact h1 i is

/-! ### R11. `h.1`, `h.2` · context: the two halves of a hypothesis whose type unfolds to `A ∧ B` -/
example (t x : Nat) (xs : List Nat) (h : Above t (x :: xs)) (G : Prop)
    (k : t ≤ x → Above (x + 1) xs → G) : G := by
  have h1 := h.1
  have h2 := h.2
  exact k h1 h2

/-! ### R12. `Nat.le_trans` · `n ≤ m → m ≤ k → n ≤ k` · goal: `a ≤ c` → `b ≤ c` once `a ≤ b` is given -/
example (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  apply Nat.le_trans hab
  exact hbc

/-! ## Part 4 · Sublists, sortedness and lengths (MILESTONE 4) -/

/-! ### R13. `cases hsub` with `hsub : S <+ []` · context: `hsub` gone, `S` replaced by `[]`
Only `List.Sublist.slnil : [] <+ []` can prove a sublist of `[]`. -/
example {α : Type} (S : List α) (P : List α → Prop) (hsub : S.Sublist []) (h : P []) : P S := by
  cases hsub
  exact h

/-! ### R14. `simp` · goal closed: `[].length ≤ n` is `0 ≤ n` -/
example {α : Type} (n : Nat) : ([] : List α).length ≤ n := by
  simp

/-! ### R15. `List.pairwise_cons` · `Pairwise R (a :: l) ↔ (∀ a' ∈ l, R a a') ∧ Pairwise R l` · context:
`.mp` turns `hs` into the conjunction; `.1` is "`a` is related to everything after it", `.2` the tail -/
example {α : Type} (R : α → α → Prop) (a : α) (l : List α) (hs : List.Pairwise R (a :: l)) (G : Prop)
    (k : (∀ a', a' ∈ l → R a a') → List.Pairwise R l → G) : G := by
  have h1 := (List.pairwise_cons.mp hs).1
  have h2 := (List.pairwise_cons.mp hs).2
  exact k h1 h2

/-! ### R16. `cases hsub` with `hsub : S <+ a :: l` · goal list: two goals, one per way `S` can sit
inside `a :: l`. `cons`: `S` skips `a` (`S <+ l`). `cons_cons`: `S` keeps `a` (`S` becomes `a :: l₁✝`).
With names: `cases hsub with | cons _ h => … | cons_cons _ h => …` (the `_` is the head `a`). -/
example {α : Type} (a : α) (l S : List α) (P : List α → Prop) (hsub : S.Sublist (a :: l))
    (k1 : ∀ S, S.Sublist l → P S) (k2 : ∀ S, S.Sublist l → P (a :: S)) : P S := by
  cases hsub
  case cons h => exact k1 S h
  case cons_cons S' h => exact k2 S' h

/-! ### R17. `List.Sublist.subset` · `l₁ <+ l₂ → l₁ ⊆ l₂` · goal: membership in `l₂` → membership in `l₁`
`l₁ ⊆ l₂` means `∀ a, a ∈ l₁ → a ∈ l₂`, so `hsub.subset hy : y ∈ l₂` when `hy : y ∈ l₁`. -/
example {α : Type} (y : α) (l₁ l₂ : List α) (hsub : l₁.Sublist l₂) (hy : y ∈ l₁) : y ∈ l₂ := by
  apply hsub.subset
  exact hy

/-! ### R18. `List.mem_cons_self` · `a ∈ a :: l` · goal closed (all arguments implicit) -/
example {α : Type} (a : α) (l : List α) : a ∈ a :: l := by
  exact List.mem_cons_self

/-! ### R19. `List.sublist_of_cons_sublist` · `a :: l₁ <+ l₂ → l₁ <+ l₂` · context: drop the head -/
example {α : Type} (a : α) (l₁ l₂ : List α) (hsub : (a :: l₁).Sublist l₂) (G : Prop)
    (k : l₁.Sublist l₂ → G) : G := by
  have h := List.sublist_of_cons_sublist hsub
  exact k h

/-! ### R20. `have := e` · context gains `this : T`, where `T` is the type Lean computes for `e`
Used to add an instance of the induction hypothesis before `omega`, which reads the context. -/
example {α : Type} (Q R : Nat → List α → Prop) (ih : ∀ t l, Q t l → R t l) (t : Nat) (l : List α)
    (hq : Q t l) (G : Prop) (k : R t l → G) : G := by
  have := ih t l hq
  exact k this

/-! ### R21. `simp only [List.length_cons]` · `(a :: l).length = l.length + 1` · goal -/
example {α : Type} (a b : α) (l₁ l₂ : List α) (P : Nat → Nat → Prop)
    (h : P (l₁.length + 1) (l₂.length + 1)) : P (a :: l₁).length (b :: l₂).length := by
  simp only [List.length_cons]
  exact h

/-! ### R22. `omega` · goal closed: linear arithmetic over `Nat`/`Int`, using the hypotheses; any other
term (`l.length`, `f x`) is treated as an unknown number -/
example {α : Type} (l₁ l₂ : List α) (this : l₁.length ≤ l₂.length) :
    l₁.length + 1 ≤ l₂.length + 1 := by
  omega

/-! ### R23. `rename_i h` · context: the LAST inaccessible name (`h✝`, `a✝`) gets the name `h` -/
example (c G : Prop) (k : ¬c → G) : ¬c → G := by
  intro _
  rename_i hc
  exact k hc

/-! ### R24. `absurd h hn` · `a → ¬a → b` · goal closed, whatever it is, from a contradiction -/
example (c G : Prop) (h : c) (hn : ¬c) : G := by
  exact absurd h hn

/-! ## Part 5 · Assembling a `def` that is a conjunction (the spec theorem) -/

/-- A guide `def` that is a conjunction. -/
def Capped (xs : List Nat) (k : Nat) : Prop := xs.length ≤ k ∧ ∀ x, x ∈ xs → x ≤ k

/-! ### R25. `unfold D` · goal: the name `D` → its body (optional: `refine ⟨?_, ?_⟩` sees through `D`) -/
example (xs : List Nat) (k : Nat) (P : Prop → Prop)
    (h : P (xs.length ≤ k ∧ ∀ x, x ∈ xs → x ≤ k)) : P (Capped xs k) := by
  unfold Capped
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-- Keep the entries that are at most `k` (a filter: the bound never moves). -/
def keepLe (k : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => if x ≤ k then x :: keepLe k xs else keepLe k xs

/-! ### W1. Induction, unfold, split, then a `Sublist` constructor per branch (R1–R6). The bound `k`
does not move, so no `generalizing` is needed here; in the exercise it does move. -/
example (k : Nat) (xs : List Nat) : (keepLe k xs).Sublist xs := by
  induction xs with
    | nil => simp [keepLe]
    | cons x xs ih =>
      simp only [keepLe]
      split
      · exact ih.cons_cons x
      · exact ih.cons x

/-! ### W2. Case on how `S` sits inside `x :: xs` (R16, R18, R24): if `x ∉ S`, `S` must skip `x` -/
example (x : Nat) (xs S : List Nat) (hsub : S.Sublist (x :: xs)) (hx : ¬ x ∈ S) : S.Sublist xs := by
  cases hsub with
    | cons _ h => exact h
    | cons_cons _ h => exact absurd List.mem_cons_self hx

/-! ### W3. Induction generalizing the sublist, `cases` on it, lengths, `omega` (R1, R13, R14, R16,
R20, R21, R22): a sublist is no longer than the list -/
example (xs S : List Nat) (hsub : S.Sublist xs) : S.length ≤ xs.length := by
  induction xs generalizing S with
    | nil => cases hsub; simp
    | cons x xs ih =>
      cases hsub with
      | cons _ h =>
        have := ih S h
        simp only [List.length_cons]; omega
      | cons_cons _ h =>
        have := ih _ h
        simp only [List.length_cons]; omega

/-! ### W4. Sortedness through a `def` (R15, R17, R18, R19): in a sorted `x :: xs`, the head of any
sublist of `xs` is at least `x`; the tail of a sorted list is sorted -/
example (x y : Nat) (xs S : List Nat) (hs : Asc (x :: xs)) (hsub : (y :: S).Sublist xs) :
    x ≤ y ∧ Asc xs ∧ S.Sublist xs := by
  have hy : y ∈ xs := hsub.subset List.mem_cons_self
  have hs' : Asc xs := (List.pairwise_cons.mp hs).2
  exact ⟨(List.pairwise_cons.mp hs).1 y hy, hs', List.sublist_of_cons_sublist hsub⟩

/-! ### W5. Reading a chain two steps deep (R11, R12): in a chain above `t`, the second entry is
also at least `t` -/
example (t i j : Nat) (is : List Nat) (h : Above t (i :: j :: is)) : t ≤ j := by
  have h1 := h.1
  have h2 := h.2.1
  exact Nat.le_trans h1 (Nat.le_trans (Nat.le_succ i) h2)

end H017Guide
