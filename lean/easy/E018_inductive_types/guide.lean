/- Guide for E018 (Inductive types).
Part R: one reference entry per tactic or term the exercise needs, stated with typed placeholders.
Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
All entries use the type `Dir` below (four compass directions) and `Dir.turn` (a quarter turn
clockwise), NOT the exercise's `Color`.
Part W: worked combinations on `Dir`.
Assumed: Lean basics up to E017, in particular `rfl` and `decide` (E001), `match` (E002), `exact`
(E003), `⟨_, _⟩` (E004), `simp` and `simp only [f]` (E010), `cases` and `<;>` (E016), dot notation (E017).
-/

namespace E018Guide

/-- Four directions. `inductive` declares a type whose values are exactly the listed
constructors `Dir.north`, `Dir.east`, `Dir.south`, `Dir.west`, all different from each other.
`deriving DecidableEq` makes Lean generate a procedure deciding `a = b` for `a b : Dir` (used by
`decide`, R8). -/
inductive Dir where
  | north | east | south | west
  deriving DecidableEq

/-- A quarter turn clockwise: north → east → south → west → north. -/
def Dir.turn (d : Dir) : Dir :=
  match d with
  | .north => .east
  | .east => .south
  | .south => .west
  | .west => .north

/-! # Part R · Reference entries -/

/-! ## Defining a function on an inductive type -/

/-! ### R1. `match d with | .north => a | …` · closes a `⊢ Dir` goal, one arm per constructor
Every constructor needs exactly one arm (Lean rejects a missing one). In a `def` body you write the
`match` term directly after `:=`, as in `Dir.turn` above; here it is fed to `exact` to show the goal it
closes. This one is a quarter turn counter-clockwise. -/
example (d : Dir) : Dir := by
  exact match d with
    | .north => .west
    | .east => .north
    | .south => .east
    | .west => .south

/-! ### R2. `.east` (leading-dot constructor) · nothing changes: `.east` is `Dir.east`
When Lean already expects a `Dir`, `.east` is short for `Dir.east`. The infoview always prints the full
name `Dir.east`. -/
example (P : Dir → Prop) (h : P Dir.east) : P .east := by
  exact h

/-! ## Facts about specific constructors -/

/-! ### R3. `refine ⟨?_, ?_, ?_⟩` on `A ∧ B ∧ C` · goal → three goals
`∧` nests to the right (`A ∧ (B ∧ C)`), and `⟨…⟩` flattens the nesting, so one `?_` per conjunct.
In term mode the whole proof is `⟨ha, hb, hc⟩`. -/
example (A B C : Prop) (ha : A) (hb : B) (hc : C) : A ∧ B ∧ C := by
  refine ⟨?_, ?_, ?_⟩
  exact ha
  exact hb
  exact hc

/-! ### R4. `rfl` · closes `f c = v` when `c` is a constructor: the `match` picks its arm
`Dir.north.turn` unfolds to the `match` with `d := Dir.north`, which reduces to the `.north` arm. -/
example : Dir.north.turn = .east := by
  rfl

/-! ## Facts about an arbitrary value -/

/-! ### R5. `cases d` · context loses `d : Dir`; goal → one goal per constructor
Each goal is the old one with `d` replaced by that constructor, labelled `case north`, …, `case west`. -/
example (P : Dir → Prop) (hn : P .north) (he : P .east) (hs : P .south) (hw : P .west) (d : Dir) :
    P d := by
  cases d
  exact hn
  exact he
  exact hs
  exact hw

/-! ### R6. `simp only [Dir.turn]` · goal: `Dir.turn` applied to a constructor → that arm's value -/
example (P : Dir → Prop) (h : P Dir.south) : P Dir.east.turn := by
  simp only [Dir.turn]
  exact h

/-! ### R7. `simp` · closes `c₁ ≠ c₂` for two DIFFERENT constructors
Constructors of an inductive type are always distinct; `simp` knows this for every inductive type. -/
example : Dir.east ≠ Dir.north := by
  simp

/-! ### R8. `decide` · closes the same goal using the derived `DecidableEq Dir`
It evaluates the decision procedure on the two concrete values. Without `deriving DecidableEq`,
`decide` would fail here. -/
example : Dir.east ≠ Dir.north := by
  decide

/-! # Part W · Worked combinations (on `Dir`, not the exercise's type) -/

/-! ### W1. One constructor by hand: R6, then R7 -/
example : Dir.north.turn ≠ Dir.north := by
  simp only [Dir.turn]
  simp

/-! ### W2. An arbitrary `d`: R5 splits, then `simp [Dir.turn]` (R6 + R7 in one call) on every goal -/
example (d : Dir) : d.turn ≠ d := by
  cases d
  all_goals simp [Dir.turn]

/-! ### W3. Four quarter turns: R5, then R4 on each of the four goals (`<;>`) -/
example (d : Dir) : d.turn.turn.turn.turn = d := by
  cases d <;> rfl

end E018Guide
