/- Guide for M024 (Is sorted).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries about a three-arm Bool recursion use the guide's own function `chainLt` below ("each
entry is strictly below the next"), which is NOT the exercise's `isSorted`. The case alternatives
of `fun_induction` are written `| caseK … => ?_` so every case stays open as a goal you can inspect;
in the exercise you write a tactic after `=>` instead.
Part W: worked combinations on `chainLt` and on the strict order `<`.
Assumed: Lean basics (E001–E033). No Mathlib: everything here is core Lean.
-/

namespace M024Guide

/-- `chainLt l`: `true` when every entry of `l` is strictly below the entry right after it. -/
def chainLt (l : List Nat) : Bool :=
  match l with
  | [] => true
  | [_] => true
  | a :: b :: t => decide (a < b) && chainLt (b :: t)

/-! # Part R · Reference entries -/

/-! ## A Bool test on adjacent entries -/

/-! ### R1. `match l with | [] => … | [_] => … | a :: b :: t => decide (a < b) && f (b :: t)` · closes a test goal
`[_]` is a one-element list whose entry is not named; `a :: b :: t` has at least two entries. The
arms are tried top to bottom and cover every list. `decide p : Bool` runs the decision procedure of
a decidable Prop `p` (`<`, `≤`, `=` on `Nat` have one) and returns `true` or `false`; `&&` is Bool
"and". The recursive call is on the proper tail `b :: t`, so Lean accepts it by structural
recursion, and the function computes: `decide` (the tactic) or `rfl` can test it. -/
example : chainLt [1, 2, 5] = true ∧ chainLt [2, 2] = false := by
  decide

/-! ## Induction along the function -/

/-! ### R2. `fun_induction f l with | case1 => … | case2 a => … | case3 a b t ih => …` · goal list
One goal per arm of `f`. In each, `l` becomes the arm's pattern and `f l` the arm's right-hand side;
the recursive call `f (b :: t)` gives the IH `ih : P (b :: t) (f (b :: t))`. An arm names, in
order, the pattern variables, then the IH; `[_]` still names its entry (`case2 a`). -/
example (l : List Nat) (P : List Nat → Bool → Prop) (h1 : P [] true) (h2 : ∀ a, P [a] true)
    (h3 : ∀ a b t, P (b :: t) (chainLt (b :: t)) →
      P (a :: b :: t) (decide (a < b) && chainLt (b :: t))) : P l (chainLt l) := by
  fun_induction chainLt l with
    | case1 => ?_
    | case2 a => ?_
    | case3 a b t ih => ?_
  · exact h1
  · exact h2 a
  · exact h3 a b t ih

/-! ### R3. `simp` (lemmas `List.Pairwise.nil`, `List.pairwise_singleton`) · closes the short-list cases
`List.Pairwise R l`: `R x y` holds for every `x` that comes before `y` in `l` (every pair, not only
neighbours). A list with fewer than two entries has no pair, so `Pairwise R` holds whatever `R`
is, and `true = true` is `True`. -/
example {α : Type} (R : α → α → Prop) (a : α) :
    (true = true ↔ List.Pairwise R []) ∧ (true = true ↔ List.Pairwise R [a]) := by
  simp

/-! ## From Bool back to Prop -/

/-! ### R4. `simp only [Bool.and_eq_true]` · `((a && b) = true) = (a = true ∧ b = true)` · goal: `&&` → `∧`
An `=` between Props (not an `↔`); `simp only` and `rw` both use it left to right. -/
example (a b : Bool) (P : Prop → Prop) (h : P (a = true ∧ b = true)) : P ((a && b) = true) := by
  simp only [Bool.and_eq_true]
  exact h

/-! ### R5. `simp only [decide_eq_true_eq]` · `(decide p = true) = p` · goal: Bool test → the Prop itself -/
example (p : Prop) [Decidable p] (P : Prop → Prop) (h : P p) : P (decide p = true) := by
  simp only [decide_eq_true_eq]
  exact h

/-! ### R6. `simp only [ih]` with an `↔` IH · goal: the IH's left side → its right side
`ih : f l = true ↔ Q l` is a rewrite rule like a lemma: every `f l = true` in the goal becomes `Q l`.
R4, R5, R6 combine into one call: `simp only [Bool.and_eq_true, decide_eq_true_eq, ih]`. -/
example (f : List Nat → Bool) (Q : List Nat → Prop) (l : List Nat) (ih : f l = true ↔ Q l)
    (P : Prop → Prop) (h : P (Q l)) : P (f l = true) := by
  simp only [ih]
  exact h

/-! ## Proving an `↔` about `Pairwise` -/

/-! ### R7. `constructor` on `A ↔ B` · goal list: `A ↔ B` → `A → B` (case `mp`), `B → A` (case `mpr`) -/
example (A B : Prop) (hab : A → B) (hba : B → A) : A ↔ B := by
  constructor
  · exact hab
  · exact hba

/-! ### R8. `rintro ⟨ha, hb⟩` · goal `A ∧ B → C` → context gains `ha : A`, `hb : B`, goal `C`
`intro` followed by taking the `∧` apart, in one step. -/
example (A B C : Prop) (g : A → B → C) : A ∧ B → C := by
  rintro ⟨ha, hb⟩
  exact g ha hb

/-! ### R9. `List.Pairwise.cons` · goal: `Pairwise R (a :: l)` → `a` is related to all of `l`, and `Pairwise R l`
The lemma: `(∀ a' ∈ l, R a a') → Pairwise R l → Pairwise R (a :: l)`. With `refine` you leave a `?_`
for each part you prove next; `refine List.Pairwise.cons ?_ hl` fills the second part at once. -/
example {α : Type} (R : α → α → Prop) (a : α) (l : List α) (h1 : ∀ a' ∈ l, R a a')
    (h2 : List.Pairwise R l) : List.Pairwise R (a :: l) := by
  refine List.Pairwise.cons ?_ ?_
  · exact h1
  · exact h2

/-! ### R10. `intro z hz` on a bounded `∀` · context gains `z` and `hz : z ∈ l`
`∀ a' ∈ l, R a a'` is notation for `∀ (a' : α), a' ∈ l → R a a'`, so it takes two `intro` names. -/
example {α : Type} (R : α → α → Prop) (a : α) (l : List α) (h : ∀ z, z ∈ l → R a z) :
    ∀ a' ∈ l, R a a' := by
  intro z hz
  exact h z hz

/-! ### R11. `rw [List.mem_cons] at hz` · `a ∈ b :: l ↔ a = b ∨ a ∈ l` · context: `hz` rewritten -/
example {α : Type} (z b : α) (l : List α) (hz : z ∈ b :: l) (P : Prop) (h : z = b ∨ z ∈ l → P) :
    P := by
  rw [List.mem_cons] at hz
  exact h hz

/-! ### R12. `rcases hz with rfl | hz` · goal list: one goal per side of an `∨`
On `hz : z = b ∨ z ∈ l` it gives two goals. In the first, the pattern `rfl` substitutes the equation
away: one of `z`, `b` is replaced by the other everywhere (hypotheses included) and disappears.
In the second, `hz : z ∈ l`. -/
example {α : Type} (z b : α) (l : List α) (P : α → α → Prop) (h1 : P z z) (h2 : z ∈ l → P z b)
    (hz : z = b ∨ z ∈ l) : P z b := by
  rcases hz with rfl | hz
  · exact h1
  · exact h2 hz

/-! ### R13. `Nat.le_trans` · `n ≤ m → m ≤ k → n ≤ k` · closes `n ≤ k` from the two links -/
example (n m k : Nat) (h1 : n ≤ m) (h2 : m ≤ k) : n ≤ k := by
  exact Nat.le_trans h1 h2

/-! ### R14. `List.rel_of_pairwise_cons` · `Pairwise R (a :: l) → a' ∈ l → R a a'` · context gains `R a z`
The head of a pairwise list is related to every later entry. -/
example {α : Type} (R : α → α → Prop) (a z : α) (l : List α) (h : List.Pairwise R (a :: l))
    (hz : z ∈ l) (P : Prop) (hp : R a z → P) : P := by
  have hr := List.rel_of_pairwise_cons h hz
  exact hp hr

/-! ### R15. `List.mem_cons_self` · `a ∈ a :: l` · closes the goal
Both `a` and `l` are implicit: write `List.mem_cons_self` with no arguments. Combined with R14:
`List.rel_of_pairwise_cons h List.mem_cons_self : R a b` for `h : Pairwise R (a :: b :: l)`. -/
example {α : Type} (b : α) (l : List α) : b ∈ b :: l := by
  exact List.mem_cons_self

/-! ### R16. `List.Pairwise.of_cons` · `Pairwise R (a :: l) → Pairwise R l` · context gains the tail fact
As a term: `h.of_cons` (dot notation: `h : List.Pairwise …`, so `h.of_cons` is
`List.Pairwise.of_cons h`). -/
example {α : Type} (R : α → α → Prop) (a : α) (l : List α) (h : List.Pairwise R (a :: l))
    (P : Prop) (hp : List.Pairwise R l → P) : P := by
  have h' := h.of_cons
  exact hp h'

/-! # Part W · Worked combinations (on `chainLt` and `<`, not the exercise's objects) -/

/-! ### W1. Read off the first comparison of `chainLt`: unfold, then R4, R5 on a hypothesis -/
example (a b : Nat) (t : List Nat) (h : chainLt (a :: b :: t) = true) : a < b := by
  simp only [chainLt, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-! ### W2. Strict order, head part: R9, R10, R11, R12, then `Nat.lt_trans` (the `<` analogue of R13)
with R14 -/
example (a b : Nat) (l : List Nat) (hab : a < b) (hl : List.Pairwise (· < ·) (b :: l)) :
    List.Pairwise (· < ·) (a :: b :: l) := by
  refine List.Pairwise.cons ?_ hl
  intro z hz
  rw [List.mem_cons] at hz
  rcases hz with rfl | hz
  · exact hab
  · exact Nat.lt_trans hab (List.rel_of_pairwise_cons hl hz)

/-! ### W3. Strict order, taking it apart: R14 with R15, and R16 -/
example (a b : Nat) (l : List Nat) (h : List.Pairwise (· < ·) (a :: b :: l)) :
    a < b ∧ List.Pairwise (· < ·) (b :: l) := by
  exact ⟨List.rel_of_pairwise_cons h List.mem_cons_self, h.of_cons⟩

end M024Guide
