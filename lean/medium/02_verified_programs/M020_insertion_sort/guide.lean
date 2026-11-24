/- Guide for M020 (Insertion sort).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries use the guide's own objects, which are NOT the exercise's:
  `Alt l`         an inductive predicate on `List Nat` with the same three-constructor shape as
                  `Sorted`, but with `x ≠ y` ("neighbours differ") instead of `x ≤ y`;
  `dropBig b l`   a recursive function with an `if` in its `::` clause, like `ins`;
  `pushBack x l`  appends `x` at the end of `l`.
Part W: worked combinations on these objects.
Assumed: Lean basics (E001–E033). No Mathlib: everything here is core Lean.
-/

namespace M020Guide

/-- `Alt l`: neighbouring elements of `l` differ. Same shape as the exercise's `Sorted`. -/
inductive Alt : List Nat → Prop
  | nil : Alt []
  | single (x : Nat) : Alt [x]
  | cons {x y : Nat} {rest : List Nat} : x ≠ y → Alt (y :: rest) → Alt (x :: y :: rest)

/-- `dropBig b l`: the elements of `l` that are `≤ b`. Structural recursion with an `if`. -/
def dropBig (b : Nat) (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | y :: ys => if y ≤ b then y :: dropBig b ys else dropBig b ys

/-- `pushBack x l`: `l` with `x` appended at the end. -/
def pushBack (x : Nat) (l : List Nat) : List Nat :=
  match l with
  | [] => [x]
  | y :: ys => y :: pushBack x ys

/-! # Part R · Reference entries -/

/-! ## Inductive predicates: building and taking apart derivations -/

/-! ### R1. `induction h with | nil => … | single x => … | @cons x y rest hxy hs ih => …` · goal list
`h : Alt l` is a derivation, a tree of constructor applications. Induction on it gives one goal per
constructor, with `l` replaced by that constructor's list. `cons` has implicit arguments
`{x y rest}`; the `@` lets you name them too, in order: implicit ones, then the explicit premises
(`hxy : x ≠ y`, `hs : Alt (y :: rest)`), then the induction hypothesis `ih : P (y :: rest)` for
the premise `hs`. The arms here are `?_`, so all goals stay open; in a proof you write tactics after `=>`. -/
example (P : List Nat → Prop) (h0 : P []) (h1 : ∀ x, P [x])
    (h2 : ∀ x y rest, x ≠ y → Alt (y :: rest) → P (y :: rest) → P (x :: y :: rest))
    (l : List Nat) (h : Alt l) : P l := by
  induction h with | nil => ?_ | single x => ?_ | @cons x y rest hxy hs ih => ?_
  · exact h0
  · exact h1 x
  · exact h2 x y rest hxy hs ih

/-! ### R2. `exact .single x` · closes `Alt [x]` with a constructor
`.single` is short for `Alt.single`: Lean reads the namespace off the goal's head `Alt`. -/
example (x : Nat) : Alt [x] := by
  exact .single x

/-! ### R3. `refine .cons ?_ ?_` (or `exact .cons h₁ h₂`) · goal → one goal per premise
The implicit `{x y rest}` are read off the goal. -/
example (x y : Nat) (rest : List Nat) (h₁ : x ≠ y) (h₂ : Alt (y :: rest)) :
    Alt (x :: y :: rest) := by
  refine .cons ?_ ?_
  exact h₁
  exact h₂

/-! ## Case splits on a comparison and evaluating an `if` -/

/-! ### R4. `by_cases hxy : x ≤ y` · goal list: two goals, context gains `hxy : x ≤ y` / `hxy : ¬x ≤ y` -/
example (x y : Nat) (P : Prop) (h1 : x ≤ y → P) (h2 : ¬x ≤ y → P) : P := by
  by_cases hxy : x ≤ y
  exact h1 hxy
  exact h2 hxy

/-! ### R5. `simp only [f]` · goal: unfold one clause of a pattern-matching `def`
`f`'s clauses are used as rewrite rules. A call is unfolded only when its list argument is
visibly `[]` or `_ :: _`; `dropBig b ys` with a variable `ys` stays as it is. -/
example (b y : Nat) (ys : List Nat) (P : List Nat → Prop)
    (h : P (if y ≤ b then y :: dropBig b ys else dropBig b ys)) : P (dropBig b (y :: ys)) := by
  simp only [dropBig]
  exact h

/-! ### R6. `simp only [hc, if_true]` (`hc : c`) · goal: `if c then a else e` → `a`
`simp` uses `hc` to rewrite `c` to `True`; `if_true : (if True then a else e) = a` finishes. -/
example (b y : Nat) (s t : List Nat) (P : List Nat → Prop) (hyb : y ≤ b) (h : P s) :
    P (if y ≤ b then s else t) := by
  simp only [hyb, if_true]
  exact h

/-! ### R7. `simp only [hc, if_false]` (`hc : ¬c`) · goal: `if c then a else e` → `e`
`simp` uses `hc : ¬c` to rewrite `c` to `False`; `if_false : (if False then a else e) = e`. -/
example (b y : Nat) (s t : List Nat) (P : List Nat → Prop) (hyb : ¬y ≤ b) (h : P t) :
    P (if y ≤ b then s else t) := by
  simp only [hyb, if_false]
  exact h

/-! ### R8. `simp only [f, hc, if_true] at ih` · context: the same rewriting inside a hypothesis
`at ih` rewrites `ih` instead of the goal; `at ih ⊢` does both. -/
example (b y : Nat) (ys : List Nat) (P : List Nat → Prop) (hyb : y ≤ b)
    (ih : P (dropBig b (y :: ys))) (h : P (y :: dropBig b ys) → False) : False := by
  simp only [dropBig, hyb, if_true] at ih
  exact h ih

/-! ### R9. `omega` · closes linear `Nat` arithmetic from the hypotheses, `¬x ≤ y` included -/
example (x y : Nat) (h : ¬x ≤ y) : y ≤ x := by
  omega

/-! ## Structural induction on a list -/

/-! ### R10. `induction l with | nil => … | cons y ys ih => …` · goal list: `[]` and `y :: ys`
`ih` is the goal for the tail `ys`. Arms `?_` keep the goals open, as in R1. -/
example (P : List Nat → Prop) (h0 : P []) (h1 : ∀ y ys, P ys → P (y :: ys)) (l : List Nat) :
    P l := by
  induction l with | nil => ?_ | cons y ys ih => ?_
  · exact h0
  · exact h1 y ys ih

/-! ## Permutations: `l₁.Perm l₂` -/

/-! ### R11. `exact .refl _` (lemma `List.Perm.refl`) · closes `l.Perm l`, also up to computation
`List.Perm.refl l : l.Perm l`. `exact` also accepts `(pushBack x []).Perm [x]`, since `pushBack x []`
computes to `[x]`. -/
example (x : Nat) : (pushBack x []).Perm [x] := by
  exact .refl _

/-! ### R12. `List.Perm.cons` · `l₁.Perm l₂ → (a :: l₁).Perm (a :: l₂)` · goal: drop the common head
As a term: `h.cons a`, for `h : l₁.Perm l₂`. -/
example {α : Type} (a : α) (l₁ l₂ : List α) (h : l₁.Perm l₂) : (a :: l₁).Perm (a :: l₂) := by
  apply List.Perm.cons
  exact h

/-! ### R13. `List.Perm.trans` · `l₁.Perm l₂ → l₂.Perm l₃ → l₁.Perm l₃` · goal: one step of a chain
As a term: `h.trans h'`. `refine h.trans ?_` uses `h` for the first step; the goal is the rest. -/
example {α : Type} (l₁ l₂ l₃ : List α) (h : l₁.Perm l₂) (h' : l₂.Perm l₃) : l₁.Perm l₃ := by
  refine h.trans ?_
  exact h'

/-! ### R14. `List.Perm.swap` · `List.Perm.swap x y l : (y :: x :: l).Perm (x :: y :: l)` · closes the goal
Mind the order: the arguments `x y` appear swapped on the LEFT side. -/
example {α : Type} (x y : α) (l : List α) : (y :: x :: l).Perm (x :: y :: l) := by
  exact List.Perm.swap x y l

/-! ## Using a proved lemma -/

/-! ### R15. `exact lem x ih` · closes the goal with a lemma, implicit arguments inferred
For `lem : ∀ (x : Nat) {l : List Nat}, Q l → Q (f x l)`, the `{l}` is read off `ih : Q l`.
`exact` also accepts it when the goal only *computes* to `Q (f x l)` (as `Sorted (isort (x :: xs))`
computes to `Sorted (ins x (isort xs))`). -/
example (Q : List Nat → Prop) (f : Nat → List Nat → List Nat)
    (lem : ∀ (x : Nat) {l : List Nat}, Q l → Q (f x l)) (x : Nat) (l : List Nat) (ih : Q l) :
    Q (f x l) := by
  exact lem x ih

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Induction on a derivation, then a constructor: R1, R5 `at ih ⊢`, R3, R9 -/
example (l : List Nat) (h : Alt l) : Alt (l.map (· + 1)) := by
  induction h with
    | nil => exact .nil
    | single x => exact .single (x + 1)
    | @cons x y rest hxy hs ih =>
      simp only [List.map] at ih ⊢
      exact .cons (by omega) ih

/-! ### W2. `by_cases` + `simp only [f, h, if_…]` in each branch: R4, R6/R7, R9 -/
example (b : Nat) (l : List Nat) : (dropBig b l).length ≤ l.length := by
  induction l with
    | nil => simp only [dropBig]; omega
    | cons y ys ih =>
      by_cases hyb : y ≤ b
      · simp only [dropBig, hyb, if_true, List.length_cons]
        omega
      · simp only [dropBig, hyb, if_false, List.length_cons]
        omega

/-! ### W3. A permutation by list induction: R10, R11, R5, R12, R13, R14 -/
theorem pushBack_perm (x : Nat) (l : List Nat) : (pushBack x l).Perm (x :: l) := by
  induction l with
    | nil => exact .refl _
    | cons y ys ih =>
      simp only [pushBack]
      exact (ih.cons y).trans (List.Perm.swap x y ys)

end M020Guide
