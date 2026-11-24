/- Guide for E054 (Deriving instances).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
All entries use the guide's own types `Color` and `Pen` below, NOT the exercise's `Suit` and `Card`.
Part W: worked combinations on `Color` and `Pen`.
Assumed: Lean basics (E001–E033), in particular `decide` (E001), `rw` (E009), `simp` (E010), `cases`
(E016, E018), structures (E017), instances (E019), distinct constructors (E029), `<;>` (E031).
-/

namespace E054Guide

/-- An enumeration: three constructors with no arguments. `deriving` asks Lean to write the instances. -/
inductive Color where
  | red | green | blue
  deriving DecidableEq, Repr

/-- A structure whose fields have derivable types (`Nat`, `Color`), so it can derive the same instances. -/
structure Pen where
  width : Nat
  color : Color
  deriving DecidableEq, Repr

/-- A `Bool` test on `Color`, used by R3 and R6. -/
def isRed (c : Color) : Bool := c == .red

/-! # Part R · Reference entries -/

/-! ## Bool tests from `DecidableEq` -/

/-! ### R1. `a == b` · a `Bool` equality test (`BEq`, supplied by `DecidableEq`) · closes a `⊢ Bool` hole
Any `[DecidableEq α]`, derived or not, gives an instance `BEq α` whose `a == b` is `decide (a = b)`. -/
example {α : Type} [DecidableEq α] (a b : α) : Bool := by
  exact a == b

/-! ### R2. `decide (a = b)` · a decidable `Prop` turned into a `Bool` · closes a `⊢ Bool` hole
`decide p : Bool` needs `[Decidable p]`; `DecidableEq α` is exactly "`a = b` is decidable for all `a b`". -/
example {α : Type} [DecidableEq α] (a b : α) : Bool := by
  exact decide (a = b)

/-! ## From the `Bool` test back to a `Prop` -/

/-! ### R3. `unfold isRed` · goal: the name of a `def` applied to arguments → its body -/
example (c : Color) (P : Bool → Prop) (h : P (c == Color.red)) : P (isRed c) := by
  unfold isRed
  exact h

/-! ### R4. `beq_iff_eq` · `[BEq α] [LawfulBEq α] {a b : α} : (a == b) = true ↔ a = b` · goal
`LawfulBEq α` says `==` agrees with `=`; the `BEq` that `DecidableEq` supplies has it. -/
example {α : Type} [DecidableEq α] (a b : α) (P : Prop → Prop) (h : P (a = b)) :
    P ((a == b) = true) := by
  rw [beq_iff_eq]
  exact h

/-! ### R5. `decide_eq_true_iff` · `{p : Prop} [Decidable p] : decide p = true ↔ p` · goal -/
example (p : Prop) [Decidable p] (P : Prop → Prop) (h : P p) : P (decide p = true) := by
  rw [decide_eq_true_iff]
  exact h

/-! ### R6. `exact beq_iff_eq` through a definition · closes the goal
`exact` checks types up to unfolding `def`s, so `isRed c = true` is accepted as `(c == Color.red) = true`
without an `unfold` first. -/
example (c : Color) : isRed c = true ↔ c = Color.red := by
  exact beq_iff_eq

/-! ## Facts about concrete values -/

/-! ### R7. `decide` on a derived `DecidableEq` structure · closes `x ≠ y` for closed values
`decide` evaluates the derived equality test field by field. Only closed terms: no variables. -/
example : ({ width := 2, color := .red } : Pen) ≠ { width := 2, color := .green } := by
  decide

/-! ## Facts about a symbolic value of an enumeration -/

/-! ### R8. `cases c` (enumeration) · goal list: one goal per constructor; `c` is replaced everywhere
Hypotheses that mention `c` are rewritten too: `h : c ≠ Color.red` becomes `h : Color.red ≠ Color.red`. -/
example (P : Color → Prop) (hg : P .green) (hb : P .blue) (c : Color) (h : c ≠ .red) : P c := by
  cases c
  · exact absurd rfl h
  · exact hg
  · exact hb

/-! ### R9. `simp_all` · closes the goal when a hypothesis is `x ≠ x` (it simplifies to `False`) -/
example (G : Prop) (h : Color.green ≠ Color.green) : G := by
  simp_all

/-! ### R10. `simp` (constructor distinctness) · goal: `Color.green = Color.blue` → `False`
Distinct constructors are never equal; `simp` and `simp_all` know this (simproc `reduceCtorEq`).
Here `P ∨ False` then simplifies to `P`. -/
example (P : Prop) (h : P) : P ∨ Color.green = Color.blue := by
  simp
  exact h

/-! # Part W · Worked combinations (on `Color` and `Pen`, not the exercise's `Suit` and `Card`) -/

/-! ### W1. A `Bool` test on a field (R1), and its `Prop` meaning: by hand (R3, R4), in one step (R6) -/
def Pen.isThin (p : Pen) : Bool := p.width == 1

example (p : Pen) : p.isThin = true ↔ p.width = 1 := by
  unfold Pen.isThin
  rw [beq_iff_eq]

example (p : Pen) : p.isThin = true ↔ p.width = 1 := by
  exact beq_iff_eq

/-! ### W2. The `decide` form of the same test (R2), unpacked with R5 -/
def Pen.isThin' (p : Pen) : Bool := decide (p.width = 1)

example (p : Pen) : p.isThin' = true ↔ p.width = 1 := by
  unfold Pen.isThin'
  rw [decide_eq_true_iff]

/-! ### W3. `decide` on closed values (R7): different widths, and a `Bool` test evaluated -/
example : ({ width := 1, color := .blue } : Pen) ≠ { width := 3, color := .blue } := by
  decide

example : (Pen.mk 1 .red).isThin = true := by
  decide

/-! ### W4. A symbolic colour: `cases` (R8), then `simp_all` in every case (R9, R10) -/
example (c : Color) (h : c ≠ .blue) : c = .red ∨ c = .green := by
  cases c <;> simp_all

end E054Guide
