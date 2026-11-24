/- Guide for E017 (Structures).
Part R: one reference entry per tactic or term the exercise needs, stated with typed placeholders.
Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
All entries use the structure `Cell` below (a grid cell: row and column), NOT the exercise's `Point`.
Part W: worked combinations on `Cell` and a three-field structure `Trip`.
Assumed: Lean basics up to E016, in particular `rfl` (E001), `⟨_, _⟩` (E004), `constructor` and `∧`
(E005), `unfold` (E010).
-/

namespace E017Guide

/-- A grid cell. `structure` declares a type with named fields; it creates the constructor
`Cell.mk (row col : Nat) : Cell` and one projection per field, `Cell.row : Cell → Nat` and
`Cell.col : Cell → Nat`. -/
structure Cell where
  row : Nat
  col : Nat

/-- One row down. Declared in the namespace `Cell`, so `c.down` means `Cell.down c` (R3). -/
def Cell.down (c : Cell) : Cell := ⟨c.row + 1, c.col⟩

/-- A fixed cell, written with structure-instance notation (R1). -/
def Cell.corner : Cell := { row := 5, col := 7 }

/-! # Part R · Reference entries -/

/-! ## Building a value of a structure -/

/-! ### R1. `{ row := a, col := b }` (structure-instance notation) · closes a `⊢ Cell` goal
Each field is named, so the order does not matter. The infoview prints every `Cell` value this way. -/
example (a b : Nat) : Cell := by
  exact { row := a, col := b }

/-! ### R2. `⟨a, b⟩` (anonymous constructor) and `constructor` · goal `⊢ Cell` → one goal per field
`⟨a, b⟩` is `Cell.mk a b`: the arguments fill the fields IN DECLARATION ORDER (`row`, then `col`).
As a tactic, `constructor` applies `Cell.mk` and leaves one goal per field (`case row`, `case col`). -/
example (a b : Nat) : Cell := by
  constructor
  exact a
  exact b

/-! ## Reading fields -/

/-! ### R3. Projections and dot notation · `c.row` is `Cell.row c`; `c.down` is `Cell.down c`
`x.f` with `x : Cell` means `Cell.f x` for ANY `Cell.f` whose first explicit argument is a `Cell`:
a field (`Cell.row`) or a function declared as `def Cell.down`. The two spellings are the same term,
so `exact h` closes the goal; the infoview prints both as `c.down.row`. -/
example (c : Cell) (P : Nat → Prop) (h : P (Cell.row (Cell.down c))) : P c.down.row := by
  exact h

/-! ### R4. `constructor` (or `⟨_, _⟩`) on `A ∧ B` · goal → two goals
`∧` is itself a structure (`And.intro (left : A) (right : B)`), so the same R2 moves apply.
In term mode: `⟨ha, hb⟩`, e.g. `⟨rfl, rfl⟩`. -/
example (A B : Prop) (ha : A) (hb : B) : A ∧ B := by
  constructor
  exact ha
  exact hb

/-! ## Computing with fields -/

/-! ### R5. `unfold D` · goal: the defined name `D` → its body -/
example (c : Cell) (P : Nat → Prop) (h : P ({ row := c.row + 1, col := c.col } : Cell).row) :
    P c.down.row := by
  unfold Cell.down
  exact h

/-! ### R6. `dsimp only` · goal: a field of a constructor value → the value stored there
`{ row := a, col := b }.row` → `a` and `{ row := a, col := b }.col` → `b`. If both sides of an `=`
then agree, `dsimp only` closes the goal. -/
example (a b : Nat) (P : Nat → Prop) (h : P a) : P ({ row := a, col := b } : Cell).row := by
  dsimp only
  exact h

/-! ### R7. `rfl` · closes `a = b` when both sides agree after unfolding definitions and reducing
projections: it does R5 and R6 by itself. -/
example (c : Cell) : c.down.col = c.col := by
  rfl

/-! ### R8. Structure eta: `rfl` closes `{ row := c.row, col := c.col } = c`
Rebuilding a structure from its own fields gives back the same value BY DEFINITION, even when `c`
is a variable (nothing is known about its fields). `dsimp only` also closes such a goal. -/
example (c : Cell) : (⟨c.row, c.col⟩ : Cell) = c := by
  rfl

/-! # Part W · Worked combinations (on `Cell` and `Trip`, not the exercise's structure) -/

/-! ### W1. Three spellings of the same value (R1, R2, the constructor itself); `rfl` sees they agree -/
example : (⟨5, 7⟩ : Cell) = { row := 5, col := 7 } := rfl
example : Cell.mk 5 7 = Cell.corner := rfl

/-! ### W2. Two fields at once: R4 splits, then R5 → R6 on the first goal, R7 on the second -/
example (c : Cell) : c.down.down.row = c.row + 1 + 1 ∧ c.down.down.col = c.col := by
  constructor
  unfold Cell.down
  dsimp only
  rfl

/-- Three fields, and a function that rotates them. -/
structure Trip where
  a : Nat
  b : Nat
  c : Nat

def Trip.rot (t : Trip) : Trip := ⟨t.b, t.c, t.a⟩

/-! ### W3. Rotating three times: projections reduce to `⟨t.a, t.b, t.c⟩` (R5, R6), which is `t` (R8) -/
example (t : Trip) : t.rot.rot.rot = t := by
  rfl

example (t : Trip) : t.rot.rot.rot = t := by
  dsimp only [Trip.rot]

/-! ### W4. Functional update `{ c with row := r }`: a copy of `c` with the named fields replaced
The fields not named keep their values (`col := c.col`). Not needed for the exercise. -/
example (c : Cell) (r : Nat) : ({ c with row := r } : Cell) = ⟨r, c.col⟩ := rfl
example (c : Cell) (r : Nat) : ({ c with row := r } : Cell).col = c.col := rfl

end E017Guide
