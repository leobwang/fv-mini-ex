/- Guide for M030 (Merge sorted lists).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries about two-list recursion use the guide's own function `inter` (intersection of two
sorted lists), which is NOT the exercise's `merge`.
Part W: worked combinations on `inter` and arbitrary lists.
Assumed: Lean basics (E001–E033). No Mathlib: everything here is core Lean.
-/

namespace M030Guide

/-- `inter l₁ l₂`: the common elements of two sorted lists. Compare the heads; drop the smaller one
(only that list shrinks, the other stays as it is); keep a head that occurs in both. -/
def inter (l₁ l₂ : List Nat) : List Nat :=
  match l₁, l₂ with
  | [], _ => []
  | _ :: _, [] => []
  | a :: as, b :: bs =>
    if a < b then inter as (b :: bs)
    else if b < a then inter (a :: as) bs
    else a :: inter as bs

/-! # Part R · Reference entries -/

/-! ## Defining a function on two lists -/

/-! ### R1. `def f (l₁ l₂ : List Nat) : List Nat := match l₁, l₂ with | … => …` · closes a test goal
`match l₁, l₂ with` matches both lists at once; one arm per combination of shapes, tried top to
bottom. Every recursive call shrinks one list and keeps the other, so no single argument always
shrinks: Lean then finds a well-founded order itself (here the pair `(l₁, l₂)` ordered
lexicographically: first list first) and you write no `termination_by`. Such a definition does not
compute inside proofs (`rfl` and `decide` fail on it); test it with `simp [inter]`, which applies its
defining equations, or with `#eval`. -/
example : inter [1, 2, 4] [2, 3, 4] = [2, 4] := by
  simp [inter]

/-! ### R2. `fun_induction f l₁ l₂ with | case1 … => … | …` · goal list: one goal per branch of `f`
Each branch of `f` (each `match` arm, and each side of an `if` inside an arm) becomes a goal in which
the call `f l₁ l₂` is already replaced by that branch's right-hand side. Every recursive call gets an
induction hypothesis `ih`. An arm names, in order: the arm's pattern variables, the `if` conditions
on the way to the branch, then the IHs. Here the arms are `?_`, so all goals stay open; in a proof
you write the arm's tactics after `=>`. -/
example (l₁ l₂ : List Nat) (P : List Nat → Prop) (h1 : P [])
    (h5 : ∀ (a : Nat) (as bs : List Nat), P (inter as bs) → P (a :: inter as bs)) :
    P (inter l₁ l₂) := by
  fun_induction inter l₁ l₂ with
    | case1 l => ?_
    | case2 a as => ?_
    | case3 a as b bs hlt ih => ?_
    | case4 a as b bs hnlt hgt ih => ?_
    | case5 a as b bs hnlt hngt ih => ?_
  · exact h1
  · exact h1
  · exact ih
  · exact ih
  · exact h5 a as bs ih

/-! ## Permutations: `l₁.Perm l₂` -/

/-! ### R3. `exact .refl _` (lemma `List.Perm.refl`) · closes `l.Perm l`, also up to computation
`List.Perm l₁ l₂`: `l₂` is a rearrangement of `l₁`. `List.Perm.refl l : l.Perm l`. `.refl` is short
for `List.Perm.refl`: Lean reads the namespace off the goal's head `List.Perm`. `exact` accepts
`l.Perm ([] ++ l)` too, because `[] ++ l` computes to `l`. -/
example {α : Type} (l : List α) : l.Perm ([] ++ l) := by
  exact .refl _

/-! ### R4. `simp` (lemmas `List.append_nil`, `List.Perm.refl`) · closes `l.Perm (l ++ [])`
`l ++ []` does NOT compute to `l` (`++` recurses on its left argument), so R3 fails here; `simp`
rewrites `l ++ [] = l` and then closes `l.Perm l`. -/
example {α : Type} (a : α) (l : List α) : (a :: l).Perm (a :: l ++ []) := by
  simp

/-! ### R5. `List.Perm.cons` · `l₁.Perm l₂ → (a :: l₁).Perm (a :: l₂)` · closes the goal (as a term)
Dot notation: for `h : l₁.Perm l₂`, `h.cons a` is `List.Perm.cons a h`. `::` binds tighter than `++`,
so `a :: as ++ bs` is `(a :: as) ++ bs`; it computes to `a :: (as ++ bs)` (lemma `List.cons_append`),
and `exact` sees through that computation. -/
example {α : Type} (a : α) (l₁ as bs : List α) (h : l₁.Perm (as ++ bs)) :
    (a :: l₁).Perm (a :: as ++ bs) := by
  exact h.cons a

/-! ### R6. `List.Perm.trans` · `l₁.Perm l₂ → l₂.Perm l₃ → l₁.Perm l₃` · goal: one step of a chain
`refine h.trans ?_` uses `h : l₁.Perm l₂` for the first step; the goal is the rest of the chain.
As a full term: `h.trans h'`. -/
example {α : Type} (l₁ l₂ l₃ : List α) (h : l₁.Perm l₂) (h' : l₂.Perm l₃) : l₁.Perm l₃ := by
  refine h.trans ?_
  exact h'

/-! ### R7. `List.Perm.symm` · `l₁.Perm l₂ → l₂.Perm l₁` · goal: swap the two sides
As a term: `h.symm`. -/
example {α : Type} (l₁ l₂ : List α) (h : l₂.Perm l₁) : l₁.Perm l₂ := by
  apply List.Perm.symm
  exact h

/-! ### R8. `List.perm_middle` · `(l₁ ++ a :: l₂).Perm (a :: (l₁ ++ l₂))` · closes the goal
Moving one element from the middle to the front is a permutation. All arguments are implicit, so
`List.perm_middle` alone is the proof; `List.perm_middle.symm` is the other direction (R7). -/
example {α : Type} (a : α) (l₁ l₂ : List α) : (l₁ ++ a :: l₂).Perm (a :: (l₁ ++ l₂)) := by
  exact List.perm_middle

/-! ## Sortedness: `List.Pairwise R l` -/

/-! ### R9. `fun_induction` with a hypothesis about the arguments · the IH becomes an implication
A hypothesis `hq : Q l₁` that mentions the induction variables is moved into every case: there it
says `Q` of that case's arguments (`hq : Q (a :: as)`), and `ih` asks for `Q` of the recursive call's
arguments (`ih : Q as → …`). You supply that, e.g. `ih hq'`. -/
example (l₁ l₂ : List Nat) (Q P : List Nat → Prop) (hq : Q l₁) (h1 : P [])
    (hQ : ∀ (a : Nat) (as : List Nat), Q (a :: as) → Q as)
    (h5 : ∀ (a : Nat) (as bs : List Nat), P (inter as bs) → P (a :: inter as bs)) :
    P (inter l₁ l₂) := by
  fun_induction inter l₁ l₂ with
    | case1 l => ?_
    | case2 a as => ?_
    | case3 a as b bs hlt ih => ?_
    | case4 a as b bs hnlt hgt ih => ?_
    | case5 a as b bs hnlt hngt ih => ?_
  · exact h1
  · exact h1
  · exact ih (hQ a as hq)
  · exact ih hq
  · exact h5 a as bs (ih (hQ a as hq))

/-! ### R10. `List.Pairwise.cons` · goal: `Pairwise R (a :: l)` → `a` is related to all of `l`, and `Pairwise R l`
`List.Pairwise R l`: `R x y` for every `x` that comes before `y` in `l`. With `R = (· ≤ ·)` (printed
`fun x1 x2 => x1 ≤ x2`) that is "sorted". The lemma:
`(∀ a' ∈ l, R a a') → Pairwise R l → Pairwise R (a :: l)`. -/
example {α : Type} (R : α → α → Prop) (a : α) (l : List α) (h1 : ∀ a' ∈ l, R a a')
    (h2 : List.Pairwise R l) : List.Pairwise R (a :: l) := by
  refine List.Pairwise.cons ?_ ?_
  exact h1
  exact h2

/-! ### R11. `List.Pairwise.of_cons` · `Pairwise R (a :: l) → Pairwise R l` · context gains the tail fact
As a term: `h.of_cons`, e.g. as an argument `ih h.of_cons`. -/
example {α : Type} (R : α → α → Prop) (a : α) (l : List α) (h : List.Pairwise R (a :: l))
    (P : Prop) (hp : List.Pairwise R l → P) : P := by
  have h' := h.of_cons
  exact hp h'

/-! ### R12. `intro z hz` on a bounded `∀` · context gains `z` and `hz : z ∈ l`
`∀ a' ∈ l, R a a'` is notation for `∀ (a' : α), a' ∈ l → R a a'`, so it takes two `intro` names. -/
example {α : Type} (R : α → α → Prop) (a : α) (l : List α) (h : ∀ z, z ∈ l → R a z) :
    ∀ a' ∈ l, R a a' := by
  intro z hz
  exact h z hz

/-! ### R13. `List.Perm.mem_iff` · `l₁.Perm l₂ → (a ∈ l₁ ↔ a ∈ l₂)` · context: rewrite `hz` along a permutation
Here `hp.mem_iff` is an `↔`, which `rw` uses like an equation. -/
example {α : Type} (z : α) (l₁ l₂ : List α) (hp : l₁.Perm l₂) (hz : z ∈ l₁) (P : Prop)
    (h : z ∈ l₂ → P) : P := by
  rw [hp.mem_iff] at hz
  exact h hz

/-! ### R14. `List.mem_append` · `a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t` · context -/
example {α : Type} (z : α) (s t : List α) (hz : z ∈ s ++ t) (P : Prop) (h : z ∈ s ∨ z ∈ t → P) :
    P := by
  rw [List.mem_append] at hz
  exact h hz

/-! ### R15. `List.mem_cons` · `a ∈ b :: l ↔ a = b ∨ a ∈ l` · context -/
example {α : Type} (z b : α) (l : List α) (hz : z ∈ b :: l) (P : Prop) (h : z = b ∨ z ∈ l → P) :
    P := by
  rw [List.mem_cons] at hz
  exact h hz

/-! ### R16. `rcases hz with hz | rfl | hz` · goal list: one goal per side of an `∨`
The pattern follows the shape of the `∨`: `A ∨ B ∨ C` is `A ∨ (B ∨ C)` and takes `p | q | r`;
`(A ∨ B) ∨ C` takes `(p | q) | r`. The pattern `rfl` on an equation `z = b` substitutes it away: one of
the two variables disappears everywhere (here `b` becomes `z`). -/
example {α : Type} (z b : α) (s t : List α) (P : α → Prop) (h1 : z ∈ s → P z) (h2 : P b)
    (h3 : z ∈ t → P z) (hz : z ∈ s ∨ z = b ∨ z ∈ t) : P z := by
  rcases hz with hz | rfl | hz
  · exact h1 hz
  · exact h2
  · exact h3 hz

example {α : Type} (z b : α) (s t : List α) (P : α → Prop) (h1 : z ∈ s → P z) (h2 : P b)
    (h3 : z ∈ t → P z) (hz : (z = b ∨ z ∈ s) ∨ z ∈ t) : P z := by
  rcases hz with (rfl | hz) | hz
  · exact h2
  · exact h1 hz
  · exact h3 hz

/-! ### R17. `List.rel_of_pairwise_cons` · `Pairwise R (a :: l) → a' ∈ l → R a a'` · context gains `R a z`
The head of a pairwise list is related to every later element. -/
example {α : Type} (R : α → α → Prop) (a z : α) (l : List α) (h : List.Pairwise R (a :: l))
    (hz : z ∈ l) (P : Prop) (hp : R a z → P) : P := by
  have := List.rel_of_pairwise_cons h hz
  exact hp this

/-! ### R18. `Nat.le_trans` · `n ≤ m → m ≤ k → n ≤ k` · closes the goal -/
example (n m k : Nat) (h₁ : n ≤ m) (h₂ : m ≤ k) : n ≤ k := by
  exact Nat.le_trans h₁ h₂

/-! ### R19. `omega` · closes linear `Nat`/`Int` arithmetic from the hypotheses, `¬x ≤ y` included -/
example (x y : Nat) (h : ¬x ≤ y) : y ≤ x := by
  omega

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A permutation chain: R6, then R5's lemma, then R8 -/
example {α : Type} (a b : α) (l₁ l₂ : List α) :
    (l₁ ++ b :: a :: l₂).Perm (b :: a :: (l₁ ++ l₂)) := by
  refine List.perm_middle.trans ?_
  apply List.Perm.cons
  exact List.perm_middle

/-! ### W2. A first lemma about `inter`: everything it returns lies in the first list.
R2, then R15 and `List.mem_cons_of_mem : a ∈ l → a ∈ b :: l` -/
theorem mem_inter (l₁ l₂ : List Nat) : ∀ z ∈ inter l₁ l₂, z ∈ l₁ := by
  fun_induction inter l₁ l₂ with
    | case1 l => ?_
    | case2 a as => ?_
    | case3 a as b bs hlt ih => ?_
    | case4 a as b bs hnlt hgt ih => ?_
    | case5 a as b bs hnlt hngt ih => ?_
  · simp
  · simp
  · intro z hz
    exact List.mem_cons_of_mem a (ih z hz)
  · exact ih
  · intro z hz
    rw [List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem a (ih z hz)

/-! ### W3. Sorted in, sorted out, using W2 to locate the tail's elements:
R9, R11, R10, R12, W2, R17 -/
example (l₁ l₂ : List Nat) (h : l₁.Pairwise (· ≤ ·)) : (inter l₁ l₂).Pairwise (· ≤ ·) := by
  fun_induction inter l₁ l₂ with
    | case1 l => ?_
    | case2 a as => ?_
    | case3 a as b bs hlt ih => ?_
    | case4 a as b bs hnlt hgt ih => ?_
    | case5 a as b bs hnlt hngt ih => ?_
  · exact .nil
  · exact .nil
  · exact ih h.of_cons
  · exact ih h
  · refine List.Pairwise.cons ?_ (ih h.of_cons)
    intro z hz
    exact List.rel_of_pairwise_cons h (mem_inter as bs z hz)

end M030Guide
