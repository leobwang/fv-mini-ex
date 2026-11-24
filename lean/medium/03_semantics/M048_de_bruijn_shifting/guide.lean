/- Guide for M048 (de Bruijn shifting).
Part R: one reference entry per tactic or proof move the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h`, `k` or `hp` in an entry is only there to finish the example; it shows what the goal became.
Induction and the defining equations need a concrete inductive type, so the entries use the toy
type `Tree` below (labelled leaves, a level marker `wrap`, binary nodes), NOT the exercise's `Tm`.
Part W: worked combinations on `Tree`.
Assumed: Lean basics (E001–E033). No Mathlib.
-/

namespace M048Guide

/-! # The toy type used by the entries

A `Tree` has leaves labelled by numbers, a unary `wrap` that opens one more level, and binary
`node`s. `clip c t` replaces every leaf label `n ≥ c` by `c`, where the bound `c` grows by one under
each `wrap`: the same "parameter that changes under a constructor" as the cutoff of `shift`. -/

inductive Tree where
  | leaf (n : Nat)
  | wrap (t : Tree)
  | node (l r : Tree)

/-- Cap every leaf label at the bound `c`; the bound grows by one under `wrap`. -/
def clip (c : Nat) : Tree → Tree
  | .leaf n => if n < c then .leaf n else .leaf c
  | .wrap t => .wrap (clip (c + 1) t)
  | .node l r => .node (clip c l) (clip c r)

/-! # Part R · Reference entries -/

/-! ## Induction on a syntax tree -/

/-! ### R1. `induction t with | leaf n => … | wrap t ih => … | node l r ihl ihr => …`
· goal list: one goal per constructor; context gains the constructor's arguments and one induction
hypothesis per argument of type `Tree`. `?_` leaves a case open; in a proof write its tactics after `=>`. -/
example (P : Tree → Prop) (hl : ∀ n, P (.leaf n)) (hw : ∀ t, P t → P (.wrap t))
    (hn : ∀ l r, P l → P r → P (.node l r)) (t : Tree) : P t := by
  induction t with
    | leaf n => ?_
    | wrap t ih => ?_
    | node l r ihl ihr => ?_
  exact hl n
  exact hw t ih
  exact hn l r ihl ihr

/-! ### R2. `induction t generalizing c` · the IH holds for EVERY `c`, not just the current one
Without `generalizing c`, `ih : P c t` is about the same `c` as the goal. Under `wrap` the recursive
call uses `c + 1`, so you need `ih : ∀ (c : Nat), P c t`. `generalizing c` puts `c` back into the
goal before the induction (so `c` is re-introduced in each case). -/
example (P : Nat → Tree → Prop) (hl : ∀ c n, P c (.leaf n))
    (hw : ∀ c t, (∀ c', P c' t) → P c (.wrap t)) (hn : ∀ c l r, P c (.node l r))
    (c : Nat) (t : Tree) : P c t := by
  induction t generalizing c with
    | leaf n => exact hl c n
    | wrap t ih => ?_
    | node l r ihl ihr => exact hn c l r
  exact hw c t ih

/-! ## Unfolding and splitting an `if` -/

/-! ### R3. `simp only [clip]` on `clip c (constructor …)` · goal: one defining equation applied
On a leaf this exposes the `if`; on `wrap t` it exposes the recursive call at `c + 1`.
`clip c t` with `t` a variable stays as it is. -/
example (c n : Nat) (P : Tree → Prop) (hp : P (if n < c then .leaf n else .leaf c)) :
    P (clip c (.leaf n)) := by
  simp only [clip]
  exact hp

example (c : Nat) (t : Tree) (P : Tree → Prop) (hp : P (.wrap (clip (c + 1) t))) :
    P (clip c (.wrap t)) := by
  simp only [clip]
  exact hp

/-! ### R4. `split` · goal list: a goal containing `if b then x else y` → two goals, one with an
anonymous hypothesis `h✝ : b` and goal `… x …`, one with `h✝ : ¬b` and goal `… y …`.
`next h => tac` names that hypothesis `h`; `split <;> rfl` closes both when each is `rfl`. -/
example {α : Type} (n c : Nat) (x y : α) (P : α → Prop) (hx : n < c → P x) (hy : ¬n < c → P y) :
    P (if n < c then x else y) := by
  split
  next h => exact hx h
  next h => exact hy h

/-! ### R5. `simp [clip, ih]` with `ih : ∀ c, …` · goal: unfold, then use the IH at `c + 1`
`simp` instantiates a `∀`-hypothesis by itself: here it uses `ih (c + 1)`. That only works because
`ih` was generalized (R2). -/
example (F : Nat → Tree → Tree) (t : Tree) (c : Nat) (ih : ∀ c, clip c (F c t) = F c t) :
    clip c (.wrap (F (c + 1) t)) = .wrap (F (c + 1) t) := by
  simp only [clip]
  simp [ih]

/-! ### R6. `by_cases h : n < c` · goal list: two copies of the goal, with `h : n < c` and
`h : ¬n < c`. Unlike `split`, the hypothesis is named, and you choose the condition. -/
example (n c : Nat) (G : Prop) (k1 : n < c → G) (k2 : ¬n < c → G) : G := by
  by_cases h : n < c
  exact k1 h
  exact k2 h

/-! ### R7. `simp [h]` with `h : b` or `h : ¬b` · goal: `if b then x else y` → `x` or `y` -/
example {α : Type} (n c : Nat) (x y : α) (P : α → Prop) (hp : P x) (h : n < c) :
    P (if n < c then x else y) := by
  simp [h]
  exact hp

example {α : Type} (n c : Nat) (x y : α) (P : α → Prop) (hp : P y) (h : ¬n < c) :
    P (if n < c then x else y) := by
  simp [h]
  exact hp

/-! ## Comparing indices -/

/-! ### R8. `omega` · closes a goal of linear arithmetic over `Nat`/`Int` (`+`, `-`, `<`, `≤`, `¬`,
numerals, multiplication by numerals), using the hypotheses in the context -/
example (n c d : Nat) (h : ¬n < c) : ¬n + d < c := by
  omega

/-! ### R9. `simp [show ¬n + d < c by omega]` · goal: decide an `if` whose condition is not a
hypothesis but follows from one. `show T by tac` is a term of type `T` proved on the spot. -/
example {α : Type} (n c d : Nat) (x y : α) (P : α → Prop) (hp : P y) (h : ¬n < c) :
    P (if n + d < c then x else y) := by
  simp [show ¬n + d < c by omega]
  exact hp

/-! ### R10. Constructor injectivity · `simp`: `Tree.leaf a = Tree.leaf b` → `a = b`
Every constructor is injective; Lean generates `Tree.leaf.injEq : (Tree.leaf a = Tree.leaf b) = (a = b)`
and `simp` uses it by itself. -/
example (a b : Nat) (h : a = b) : Tree.leaf a = Tree.leaf b := by
  simp
  exact h

/-! ### R11. `Nat.add_assoc` · `n + m + k = n + (m + k)` · goal: regroup a sum (`+` groups to the left) -/
example (n a b : Nat) (P : Nat → Prop) (hp : P (n + (a + b))) : P (n + a + b) := by
  rw [Nat.add_assoc]
  exact hp

/-! ### R12. `Nat.add_comm a b` · `a + b = b + a` · goal: swap two summands
Give the arguments: bare `Nat.add_comm` matches the first sum it finds (`rw`) or is used only as an
ordered rewrite (`simp`). -/
example (n a b : Nat) (P : Nat → Prop) (hp : P (n + (b + a))) : P (n + (a + b)) := by
  rw [Nat.add_comm a b]
  exact hp

/-! ## Two cutoffs and an assumption between them -/

/-! ### R13. `induction t generalizing c c'` with `h : c ≤ c'` · the IH quantifies over both and
takes the assumption as a premise. `h` mentions `c` and `c'`, so `generalizing` reverts it too:
`ih : ∀ (c c' : Nat), c ≤ c' → Q c c' t`, and `h` is re-introduced in each case. -/
example (Q : Nat → Nat → Tree → Prop) (hl : ∀ c c' n, c ≤ c' → Q c c' (.leaf n))
    (hw : ∀ c c' t, (∀ a b, a ≤ b → Q a b t) → Q c c' (.wrap t))
    (hn : ∀ c c' l r, Q c c' (.node l r)) (c c' : Nat) (t : Tree) (h : c ≤ c') : Q c c' t := by
  induction t generalizing c c' with
    | leaf n => exact hl c c' n h
    | wrap t ih => ?_
    | node l r ihl ihr => exact hn c c' l r
  exact hw c c' t ih

/-! ### R14. `ih (c + 1) (c' + 1) (by omega)` · a term: the IH at new cutoffs, premise proved by `omega`
Applying a `∀ … → …` hypothesis to arguments gives an ordinary fact (an equation in the exercise),
which you can pass to `simp [...]` or `rw [...]`, or name with `have`. `iht c c' h` reuses `h`. -/
example (Q : Nat → Nat → Prop) (c c' : Nat) (h : c ≤ c') (ih : ∀ a b, a ≤ b → Q a b) (G : Prop)
    (k : Q (c + 1) (c' + 1) → G) : G := by
  have h1 := ih (c + 1) (c' + 1) (by omega)
  exact k h1

/-! # Part W · Worked combinations (on `Tree`, not the exercise's `Tm`) -/

/-! ### W1. `clip` is idempotent: R2; leaf: R6 → R7 (`simp` decides `c < c` by itself); wrap: R5; node: R5 -/
example (c : Nat) (t : Tree) : clip c (clip c t) = clip c t := by
  induction t generalizing c with
    | leaf n =>
      by_cases h : n < c
      · simp [clip, h]
      · simp [clip, h]
    | wrap t ih => simp [clip, ih]
    | node l r ihl ihr => simp [clip, ihl, ihr]

/-! ### W2. A tighter bound wins: R13; leaf: R3, then R6 on the inner `if`, R7 + R9;
wrap: R14 inside `simp`; node: R14 with the same `h` -/
example (c c' : Nat) (t : Tree) (h : c ≤ c') : clip c (clip c' t) = clip c t := by
  induction t generalizing c c' with
    | leaf n =>
      simp only [clip]
      by_cases h1 : n < c'
      · simp [clip, h1]
      · simp [clip, h1, show ¬n < c by omega, show ¬c' < c by omega]
    | wrap t ih => simp [clip, ih (c + 1) (c' + 1) (by omega)]
    | node l r ihl ihr => simp [clip, ihl c c' h, ihr c c' h]

end M048Guide
