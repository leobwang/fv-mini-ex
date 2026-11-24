/- Guide for H010 (Merge sort).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries about recursive functions use the guide's own functions `keepGE` (keep the elements
`≥ a`, structural recursion) and `halves` (split in half, recurse, glue the halves back in swapped
order; well-founded recursion), which are NOT the exercise's.
Part W: worked combinations on `keepGE`, `halves` and arbitrary lists.
Assumed: Lean basics (E001–E033). No Mathlib: everything here is core Lean.
-/

namespace H010Guide

/-- `keepGE a l`: the elements of `l` that are `≥ a`, in order. Structural recursion with an `if`. -/
def keepGE (a : Nat) : List Nat → List Nat
  | [] => []
  | b :: l => if a ≤ b then b :: keepGE a l else keepGE a l

/-- `halves l`: cut `l` at `l.length / 2`, treat both halves recursively, glue them back swapped.
Well-founded recursion on the length, with a `let` for the cut point. -/
def halves (l : List Nat) : List Nat :=
  if _h : l.length < 2 then l
  else
    let k := l.length / 2
    halves (l.drop k) ++ halves (l.take k)
termination_by l.length

/-! # Part R · Reference entries -/

/-! ## Permutations: `l₁.Perm l₂` -/

/-! ### R1. `fun_induction f a l with | case1 … => … | …` · goal list: one goal per branch of `f`
Each branch of `f` (each clause, and each side of an `if` inside a clause) becomes a goal in which the
call `f a l` is already replaced by that branch's right-hand side. Every recursive call gets an
induction hypothesis `ih`. Each arm names the new variables, the `if` condition, then `ih`. Here the
arms are `?_`, so all goals stay open; in a proof you write the arm's tactics after `=>`. -/
example (a : Nat) (l : List Nat) (P : List Nat → Prop) (h1 : P [])
    (h2 : ∀ b l, a ≤ b → P (keepGE a l) → P (b :: keepGE a l))
    (h3 : ∀ b l, ¬a ≤ b → P (keepGE a l) → P (keepGE a l)) : P (keepGE a l) := by
  fun_induction keepGE a l with | case1 => ?_ | case2 b l hab ih => ?_ | case3 b l hab ih => ?_
  · exact h1
  · exact h2 b l hab ih
  · exact h3 b l hab ih

/-! ### R2. `exact .refl _` (lemma `List.Perm.refl`) · closes `l.Perm l`, also up to computation
`List.Perm.refl l : l.Perm l`. `.refl` is short for `List.Perm.refl`: Lean reads the namespace off
the goal's head `List.Perm`. `exact` accepts `l.Perm ([] ++ l)` too, because `[] ++ l` computes to `l`. -/
example {α : Type} (l : List α) : l.Perm ([] ++ l) := by
  exact .refl _

/-! ### R3. `simp` (lemmas `List.append_nil`, `List.Perm.refl`) · closes `l.Perm (l ++ [])`
`l ++ []` does NOT compute to `l` (`++` recurses on its left argument), so R2 fails here; `simp`
rewrites `l ++ [] = l` and then closes `l.Perm l`. -/
example {α : Type} (a : α) (l : List α) : (a :: l).Perm (a :: l ++ []) := by
  simp

/-! ### R4. `List.cons_append` · `a :: as ++ bs = a :: (as ++ bs)` · goal
`::` binds tighter than `++`, so `a :: as ++ bs` is `(a :: as) ++ bs`. Both sides compute to the same
list, so `exact` already treats them as equal; `rw` makes it visible. -/
example {α : Type} (a : α) (as bs : List α) (P : List α → Prop) (h : P (a :: (as ++ bs))) :
    P (a :: as ++ bs) := by
  rw [List.cons_append]
  exact h

/-! ### R5. `List.Perm.cons` · `l₁.Perm l₂ → (a :: l₁).Perm (a :: l₂)` · goal: drop the common head
As a term: `h.cons a`, for `h : l₁.Perm l₂`. -/
example {α : Type} (a : α) (l₁ l₂ : List α) (h : l₁.Perm l₂) : (a :: l₁).Perm (a :: l₂) := by
  apply List.Perm.cons
  exact h

/-! ### R6. `List.Perm.trans` · `l₁.Perm l₂ → l₂.Perm l₃ → l₁.Perm l₃` · goal: one step of a chain
`refine h.trans ?_` uses `h : l₁.Perm l₂` for the first step; the goal is the rest of the chain. -/
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
A hypothesis `hq : Q l` that mentions the induction variables is moved into every case: there it says
`Q` of that case's arguments (`hq : Q (b :: l)`), and `ih` asks for `Q` of the recursive call's
arguments (`ih : Q l → …`). You supply that, e.g. `ih hq'`. -/
example (a : Nat) (l : List Nat) (Q P : List Nat → Prop) (hq : Q l)
    (h1 : Q [] → P []) (h2 : ∀ b l, a ≤ b → Q (b :: l) → (Q l → P (keepGE a l)) → P (b :: keepGE a l))
    (h3 : ∀ b l, ¬a ≤ b → Q (b :: l) → (Q l → P (keepGE a l)) → P (keepGE a l)) :
    P (keepGE a l) := by
  fun_induction keepGE a l with | case1 => ?_ | case2 b l hab ih => ?_ | case3 b l hab ih => ?_
  · exact h1 hq
  · exact h2 b l hab hq ih
  · exact h3 b l hab hq ih

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

/-! ## Well-founded recursion: `msort`-style definitions -/

/-! ### R20. `fun_induction` on a well-founded recursive function with `if h :` and `let`
Two goals: the `then` branch with `h : cond`, and the `else` branch with `h : ¬cond`, the `let`
variable as a local definition `k : Nat := …`, and one IH per recursive call. The arm names them in
that order: `case2 l h k ih1 ih2`. -/
example (l : List Nat) (P : List Nat → Prop) (h1 : ∀ l, l.length < 2 → P l)
    (h2 : ∀ l : List Nat, P (halves (l.drop (l.length / 2))) → P (halves (l.take (l.length / 2))) →
      P (halves (l.drop (l.length / 2)) ++ halves (l.take (l.length / 2)))) :
    P (halves l) := by
  fun_induction halves l with | case1 l h => ?_ | case2 l h k ih1 ih2 => ?_
  · exact h1 l h
  · exact h2 l ih1 ih2

/-! ### R21. `List.Perm.append` · `l₁.Perm l₂ → l₃.Perm l₄ → (l₁ ++ l₃).Perm (l₂ ++ l₄)` · context
`have := h₁.append h₂` adds the fact under the name `this`. -/
example {α : Type} (l₁ l₂ l₃ l₄ : List α) (h₁ : l₁.Perm l₂) (h₂ : l₃.Perm l₄) (P : Prop)
    (hp : (l₁ ++ l₃).Perm (l₂ ++ l₄) → P) : P := by
  have := h₁.append h₂
  exact hp this

/-! ### R22. `List.take_append_drop` · `List.take n l ++ List.drop n l = l` · context (or goal)
`List.take n l` is the first `n` elements of `l`, `List.drop n l` the rest. -/
example {α : Type} (n : Nat) (l l' : List α) (this : l'.Perm (List.take n l ++ List.drop n l)) :
    l'.Perm l := by
  rw [List.take_append_drop] at this
  exact this

/-! ### R23. `match l, h with | [], _ => … | [x], _ => …` · goal list: one goal per short list
Matching on `l` together with `h : l.length < 2` lets Lean check that the other shapes (`a :: b :: r`,
length `≥ 2`) contradict `h`, so you write only the two possible arms. The `_` stands for `h` in that
arm; it reappears as `x✝ : [].length < 2`. Here written as `refine match … => ?_` to show the goals;
in a proof, write `match l, h with` as a tactic with `exact …` after each `=>`. -/
example (l : List Nat) (h : l.length < 2) (P : List Nat → Prop) (h0 : P []) (h1 : ∀ x, P [x]) :
    P l := by
  refine match l, h with
    | [], _ => ?_
    | [x], _ => ?_
  · exact h0
  · exact h1 _

/-! ### R24. `List.Pairwise.nil` · closes `List.Pairwise R []`; write `exact .nil` -/
example {α : Type} (R : α → α → Prop) : List.Pairwise R [] := by
  exact .nil

/-! ### R25. `List.pairwise_singleton` · `List.pairwise_singleton R a : List.Pairwise R [a]` · closes the goal -/
example {α : Type} (R : α → α → Prop) (a : α) : List.Pairwise R [a] := by
  exact List.pairwise_singleton R a

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A permutation chain: R6, then R5, then R8 -/
example {α : Type} (a b : α) (l₁ l₂ : List α) :
    (l₁ ++ b :: a :: l₂).Perm (b :: a :: (l₁ ++ l₂)) := by
  refine List.perm_middle.trans ?_
  apply List.Perm.cons
  exact List.perm_middle

/-! ### W2. Everything `keepGE a` keeps is `≥ a`: R1, R12, R15, R16 -/
example (a : Nat) (l : List Nat) : ∀ z ∈ keepGE a l, a ≤ z := by
  fun_induction keepGE a l with | case1 => ?_ | case2 b l hab ih => ?_ | case3 b l hab ih => ?_
  · simp
  · intro z hz
    rw [List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hab
    · exact ih z hz
  · exact ih

/-! ### W3. `halves l` is a permutation of `l`: R20, R2, R21, R6, then `List.perm_append_comm`
(`(l₁ ++ l₂).Perm (l₂ ++ l₁)`) and R22 on the goal, which `rw` then closes by `List.Perm.refl`. -/
example (l : List Nat) : (halves l).Perm l := by
  fun_induction halves l with | case1 l h => ?_ | case2 l h k ih1 ih2 => ?_
  · exact .refl _
  · have := ih1.append ih2
    refine this.trans ?_
    refine List.perm_append_comm.trans ?_
    rw [List.take_append_drop]

end H010Guide
