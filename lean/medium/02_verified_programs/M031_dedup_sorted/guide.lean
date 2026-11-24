/- Guide for M031 (Dedup a sorted list).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries about a three-arm list recursion use the guide's own function `squash` below, which is
NOT the exercise's `dedup`. The case alternatives are written `| caseK … => ?_` so every case stays
open as a goal you can inspect; in the exercise you write a tactic after `=>` instead.
Part W: worked combinations on `squash` and arbitrary lists.
Assumed: Lean basics (E001–E033). No Mathlib: everything here is core Lean.
-/

namespace M031Guide

/-- `squash l`: wherever two adjacent entries are equal, keep one of the pair and continue after the
pair (so `[1, 1, 1]` becomes `[1, 1]`). Three arms, one `if` on the third. -/
def squash (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | [a] => [a]
  | a :: b :: t => if a = b then a :: squash t else a :: squash (b :: t)

/-! # Part R · Reference entries -/

/-! ## Defining a function by the first two entries -/

/-! ### R1. `match l with | [] => … | [a] => … | a :: b :: t => if a = b then … else …` · closes a test goal
`[a]` is the one-element list `a :: []`; `a :: b :: t` is a list with at least two entries. The arms
are tried top to bottom and must cover every list. Every recursive call is on a proper tail
(`t` or `b :: t`), so Lean accepts it by structural recursion with no `termination_by`, and the
function computes inside proofs: `rfl` and `decide` can test it. `if a = b` works because equality
on `Nat` is decidable. -/
example : squash [1, 1, 1, 2, 3, 3] = [1, 1, 2, 3] := by
  rfl

/-! ## Membership: `z ∈ l` -/

/-! ### R2. `fun_induction f l with | case1 => … | case2 a => … | case3 a t ih => … | case4 a b t h ih => …` · goal list
One goal per branch of `f`: the three arms, the third split by its `if`. In each goal `l` becomes
that branch's pattern and `f l` its right-hand side; each recursive call gives an IH `ih`. In the
`then` branch of `if a = b` Lean substitutes `b := a` (no hypothesis `a = b` is left, and the case
names only `a t ih`); the `else` branch keeps the condition as `h : ¬a = b`. An arm names, in order:
pattern variables, the `if` condition, the IH. -/
example (l : List Nat) (P : List Nat → List Nat → Prop) (h1 : P [] []) (h2 : ∀ a, P [a] [a])
    (h3 : ∀ a t, P (a :: a :: t) (a :: squash t))
    (h4 : ∀ a b t, P (a :: b :: t) (a :: squash (b :: t))) : P l (squash l) := by
  fun_induction squash l with
    | case1 => ?_
    | case2 a => ?_
    | case3 a t ih => ?_
    | case4 a b t hab ih => ?_
  · exact h1
  · exact h2 a
  · exact h3 a t
  · exact h4 a b t

/-! ### R3. `List.mem_cons` · `a ∈ b :: l ↔ a = b ∨ a ∈ l` · goal, or a hypothesis with `at hz`
An `↔` lemma rewrites like an equation. `simp` and `simp_all` apply it by themselves. -/
example {α : Type} (z b : α) (l : List α) (hz : z ∈ b :: l) (P : Prop) (h : z = b ∨ z ∈ l → P) :
    P := by
  rw [List.mem_cons] at hz
  exact h hz

/-! ### R4. `simp_all` · closes the goal, using every hypothesis (the IH included) as a rewrite rule
`simp` uses only the lemmas you list; `simp_all` also rewrites the goal with each hypothesis, here
`ih : z ∈ f l ↔ z ∈ l`, then applies R3 and propositional clean-up (`p ∨ p ∨ q ↔ p ∨ q`). Use it
when the IH is an `↔` whose left side appears in the goal. -/
example {α : Type} (a z : α) (f : List α → List α) (l : List α) (ih : z ∈ f l ↔ z ∈ l) :
    z ∈ a :: f l ↔ z ∈ a :: a :: l := by
  simp_all

/-! ## Sortedness: `List.Pairwise R l` -/

/-! ### R5. `fun_induction` with a hypothesis about the argument · context: the IH becomes an implication
A hypothesis `hq : Q l` that mentions the induction variable is moved into every case: there it says
`Q` of that case's pattern (`hq : Q (a :: a :: t)`), and `ih` asks for `Q` of the recursive call's
argument (`ih : Q t → …`). You supply that argument, e.g. `ih hq'`. -/
example (l : List Nat) (Q : List Nat → Prop) (P : List Nat → Prop) (hq : Q l) (h1 : P [])
    (h2 : ∀ a, P [a]) (h3 : ∀ a t, (Q t → P (squash t)) → Q (a :: a :: t) → P (a :: squash t))
    (h4 : ∀ a b t, (Q (b :: t) → P (squash (b :: t))) → Q (a :: b :: t) →
      P (a :: squash (b :: t))) : P (squash l) := by
  fun_induction squash l with
    | case1 => ?_
    | case2 a => ?_
    | case3 a t ih => ?_
    | case4 a b t hab ih => ?_
  · exact h1
  · exact h2 a
  · exact h3 a t ih hq
  · exact h4 a b t ih hq

/-! ### R6. `simp` (lemmas `List.Pairwise.nil`, `List.pairwise_singleton`) · closes `Pairwise R []`, `Pairwise R [a]`
`List.Pairwise R l`: `R x y` holds for every `x` that comes before `y` in `l`. With `R = (· < ·)`,
printed `fun x1 x2 => x1 < x2`, that is "strictly increasing"; with `(· ≤ ·)` it is "sorted". A list
with fewer than two entries has no such pair, whatever `R` is. -/
example {α : Type} (R : α → α → Prop) (a : α) : List.Pairwise R [] ∧ List.Pairwise R [a] := by
  simp

/-! ### R7. `List.Pairwise.of_cons` · `Pairwise R (a :: l) → Pairwise R l` · context gains the tail fact
As a term: `h.of_cons` (dot notation: `h : List.Pairwise …`, so `h.of_cons` is
`List.Pairwise.of_cons h`). Use it as an argument, `ih h.of_cons`; twice, `h.of_cons.of_cons`, drops
two entries. -/
example {α : Type} (R : α → α → Prop) (a : α) (l : List α) (h : List.Pairwise R (a :: l))
    (P : Prop) (hp : List.Pairwise R l → P) : P := by
  have h' := h.of_cons
  exact hp h'

/-! ### R8. `List.Pairwise.cons` · goal: `Pairwise R (a :: l)` → `a` is related to all of `l`, and `Pairwise R l`
The lemma: `(∀ a' ∈ l, R a a') → Pairwise R l → Pairwise R (a :: l)`. With `refine` you leave a `?_`
for each part you prove next; `refine List.Pairwise.cons ?_ (ih …)` fills the second part at once. -/
example {α : Type} (R : α → α → Prop) (a : α) (l : List α) (h1 : ∀ a' ∈ l, R a a')
    (h2 : List.Pairwise R l) : List.Pairwise R (a :: l) := by
  refine List.Pairwise.cons ?_ ?_
  exact h1
  exact h2

/-! ### R9. `intro z hz` on a bounded `∀` · context gains `z` and `hz : z ∈ l`
`∀ a' ∈ l, R a a'` is notation for `∀ (a' : α), a' ∈ l → R a a'`, so it takes two `intro` names. -/
example {α : Type} (R : α → α → Prop) (a : α) (l : List α) (h : ∀ z, z ∈ l → R a z) :
    ∀ a' ∈ l, R a a' := by
  intro z hz
  exact h z hz

/-! ### R10. `rw [thm] at hz` with your own `↔` theorem · context: `hz` rewritten
A theorem proved earlier in the file, `thm : ∀ l z, z ∈ f l ↔ z ∈ l`, is a rewrite rule like any
library lemma; `rw` finds its arguments `l z` by matching `hz`. -/
example {α : Type} (z : α) (f : List α → List α) (l : List α)
    (thm : ∀ (l : List α) (z : α), z ∈ f l ↔ z ∈ l) (hz : z ∈ f l) (P : Prop) (h : z ∈ l → P) :
    P := by
  rw [thm] at hz
  exact h hz

/-! ### R11. `List.rel_of_pairwise_cons` · `Pairwise R (a :: l) → a' ∈ l → R a a'` · context gains `R a z`
The head of a pairwise list is related to every later entry. -/
example {α : Type} (R : α → α → Prop) (a z : α) (l : List α) (h : List.Pairwise R (a :: l))
    (hz : z ∈ l) (P : Prop) (hp : R a z → P) : P := by
  have hr := List.rel_of_pairwise_cons h hz
  exact hp hr

/-! ### R12. `List.mem_cons_self` · `a ∈ a :: l` · closes the goal
Both `a` and `l` are implicit: write `List.mem_cons_self` with no arguments. Combined with R11:
`List.rel_of_pairwise_cons h List.mem_cons_self : R a b` for `h : Pairwise R (a :: b :: l)`. -/
example {α : Type} (b : α) (l : List α) : b ∈ b :: l := by
  exact List.mem_cons_self

/-! ### R13. `rcases hz with rfl | hz` · goal list: one goal per side of an `∨`
On `hz : z = b ∨ z ∈ l` it gives two goals. In the first, the pattern `rfl` substitutes the equation
away: `b` is replaced by `z` everywhere (hypotheses included) and disappears. In the second,
`hz : z ∈ l`. -/
example {α : Type} (z b : α) (l : List α) (P : α → α → Prop) (h1 : P z z) (h2 : z ∈ l → P z b)
    (hz : z = b ∨ z ∈ l) : P z b := by
  rcases hz with rfl | hz
  · exact h1
  · exact h2 hz

/-! ### R14. `omega` · closes linear `Nat` arithmetic from the hypotheses, `¬x = y` included
`x ≤ y` and `¬x = y` give `x < y`; a chain `x ≤ y`, `y ≤ z` is combined the same way. -/
example (x y z : Nat) (h1 : x ≤ y) (h2 : y ≤ z) (hne : ¬x = y) : x < z := by
  omega

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `squash` keeps the same elements: R2, then `simp` for case1, case2 and R4 for case3, case4 -/
theorem mem_squash (l : List Nat) (z : Nat) : z ∈ squash l ↔ z ∈ l := by
  fun_induction squash l with
    | case1 => simp
    | case2 a => simp
    | case3 a t ih => simp_all
    | case4 a b t hab ih => simp_all

/-! ### W2. Sorted in, sorted out (`≤`, not `<`: `squash [1, 1, 1] = [1, 1]`), using W1 to locate the
tail's elements: R5, R6, R8 with R7, R9, R10, R11 -/
example (l : List Nat) (h : l.Pairwise (· ≤ ·)) : (squash l).Pairwise (· ≤ ·) := by
  fun_induction squash l with
    | case1 => simp
    | case2 a => simp
    | case3 a t ih =>
      refine List.Pairwise.cons ?_ (ih h.of_cons.of_cons)
      intro z hz
      rw [mem_squash] at hz
      exact List.rel_of_pairwise_cons h.of_cons hz
    | case4 a b t hab ih =>
      refine List.Pairwise.cons ?_ (ih h.of_cons)
      intro z hz
      rw [mem_squash] at hz
      exact List.rel_of_pairwise_cons h hz

/-! ### W3. A strict bound from the second entry: R12 with R11, R3, R13, R14 -/
example (a b z : Nat) (l : List Nat) (h : List.Pairwise (· ≤ ·) (a :: b :: l)) (hab : ¬a = b)
    (hz : z ∈ b :: l) (hl : ∀ w ∈ l, b ≤ w) : a < z := by
  have h1 : a ≤ b := List.rel_of_pairwise_cons h List.mem_cons_self
  rw [List.mem_cons] at hz
  rcases hz with rfl | hz
  · omega
  · have h2 := hl z hz
    omega

end M031Guide
