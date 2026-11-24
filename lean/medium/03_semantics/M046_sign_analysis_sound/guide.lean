/- Guide for M046 (Sign analysis is sound).
Part R: one reference entry per tactic or lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries run on a toy abstract domain `Nn` = {zero, nonneg, any} over `Int` (NOT the exercise's
signs) and a toy expression type `Tm` = `lit n | add t u`.
Part W: worked combinations on the toy objects.
Assumed: Lean basics (E001–E033). Core Lean only, no Mathlib.
-/

namespace M046Guide

/-! ## The toy objects (not the exercise's) -/

/-- A toy abstract domain: `zero` describes `0`, `nonneg` every `v ≥ 0`, `any` every integer. -/
inductive Nn where
  | zero
  | nonneg
  | any

/-- Concretisation of the toy domain, shaped like `Sign.gamma`. -/
def Nn.den : Nn → Int → Prop
  | .zero, v => v = 0
  | .nonneg, v => 0 ≤ v
  | .any, _ => True

/-- Abstract addition with overlapping patterns, shaped like `Sign.plus`. -/
def Nn.add : Nn → Nn → Nn
  | .zero, t => t
  | t, .zero => t
  | .nonneg, .nonneg => .nonneg
  | _, _ => .any

/-- Abstraction of a literal by nested `if`s, shaped like `Sign.ofInt`. -/
def Nn.ofInt (n : Int) : Nn :=
  if n = 0 then .zero else if 0 ≤ n then .nonneg else .any

/-- Toy expressions, their value, and their abstract value. -/
inductive Tm where
  | lit (n : Int)
  | add (t u : Tm)

def Tm.ev : Tm → Int
  | .lit n => n
  | .add t u => t.ev + u.ev

def Tm.abs : Tm → Nn
  | .lit n => Nn.ofInt n
  | .add t u => t.abs.add u.abs

/-! # Part R · Reference entries -/

/-! ## Finite case analysis -/

/-! ### R1. `cases a` on a value of an enumeration · goal list: one goal per constructor
`a` leaves the context and is replaced by `Nn.zero`, `Nn.nonneg`, `Nn.any` in turn. -/
example (P : Nn → Prop) (h0 : P .zero) (h1 : P .nonneg) (h2 : P .any) (a : Nn) : P a := by
  cases a
  · exact h0
  · exact h1
  · exact h2

/-! ### R2. `cases a <;> cases b` · goal list: one goal per pair of constructors (3 × 3 = 9 here)
`<;>` runs `cases b` on every goal `cases a` made. -/
example (P : Nn → Nn → Prop) (h : ∀ a b, P a b) (a b : Nn) : P a b := by
  cases a <;> cases b
  all_goals exact h _ _

/-! ### R3. `simp only [f]` on `f` applied to constructors · goal: the call → the table's value
Works through overlapping patterns: `Nn.add .nonneg .zero` hits the second line, `t, .zero => t`. -/
example (P : Nn → Prop) (h : P .nonneg) : P (Nn.add .nonneg .zero) := by
  simp only [Nn.add]
  exact h

/-! ### R4. `simp_all [f, g]` · context AND goal: unfolds `f`, `g` everywhere, then uses each
hypothesis to simplify the others and the goal. A hypothesis `x = 0` is substituted; a goal that
becomes `True` is closed. -/
example (x y : Int) (ha : Nn.nonneg.den x) (hb : Nn.nonneg.den y) :
    (Nn.add .nonneg .nonneg).den (x + y) := by
  simp_all [Nn.add, Nn.den]
  omega

/-! The same step closes the goal when `x = 0` is among the hypotheses: `simp_all` substitutes it,
`0 + y` becomes `y`, and the goal `0 ≤ y` is then `hb` itself. -/
example (x y : Int) (ha : Nn.zero.den x) (hb : Nn.nonneg.den y) :
    (Nn.add .zero .nonneg).den (x + y) := by
  simp_all [Nn.add, Nn.den]

/-! ### R5. `omega` · closes linear arithmetic over `Int`/`Nat`, using the hypotheses
`+`, `-`, `≤`, `<`, `=`, `∧`, `∨`, `¬` and multiplication by numerals. A product `x * y` of two
variables is one opaque atom to `omega`: it knows nothing about its sign. -/
example (x y : Int) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x + y := by
  omega

/-! ## The sign of a product (core `Int` lemmas) -/

/-! ### R6. `Int.mul_pos` · `0 < a → 0 < b → 0 < a * b` · closes the goal -/
example (a b : Int) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  exact Int.mul_pos ha hb

/-! ### R7. `Int.mul_pos_of_neg_of_neg` · `a < 0 → b < 0 → 0 < a * b` · closes the goal -/
example (a b : Int) (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  exact Int.mul_pos_of_neg_of_neg ha hb

/-! ### R8. `Int.mul_neg_of_pos_of_neg` · `0 < a → b < 0 → a * b < 0` · closes the goal -/
example (a b : Int) (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  exact Int.mul_neg_of_pos_of_neg ha hb

/-! ### R9. `Int.mul_neg_of_neg_of_pos` · `a < 0 → 0 < b → a * b < 0` · closes the goal -/
example (a b : Int) (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  exact Int.mul_neg_of_neg_of_pos ha hb

/-! ## Opening an `if` -/

/-! ### R10. `unfold f` · goal: the name `f` → its body (here an `if`) -/
example (n : Int) (P : Nn → Prop) (h : P (if n = 0 then .zero else if 0 ≤ n then .nonneg else .any)) :
    P (Nn.ofInt n) := by
  unfold Nn.ofInt
  exact h

/-! ### R11. `split` · goal list: `if c then t else e` in the goal → two goals,
one with `h✝ : c` and `t`, one with `h✝ : ¬c` and `e` -/
example (c : Prop) [Decidable c] (t e : Nn) (P : Nn → Prop) (ht : c → P t) (he : ¬c → P e) :
    P (if c then t else e) := by
  split
  · exact ht ‹c›
  · exact he ‹¬c›

/-! ## Induction on an expression -/

/-! ### R12. `induction t` · goal list: one goal per constructor of `Tm`, with an induction
hypothesis for every argument that is itself a `Tm`, named after it (`t_ih✝`, `u_ih✝`).
Write `induction t with | lit n => … | add t u iht ihu => …` to name them (W3). -/
example (P : Tm → Prop) (hl : ∀ n, P (.lit n)) (ha : ∀ t u, P t → P u → P (.add t u)) (t : Tm) :
    P t := by
  induction t
  · exact hl _
  · exact ha _ _ ‹_› ‹_›

/-! ### R13. `exact e` up to unfolding · a goal about `f (c x y)` accepts a proof about what the
defining equation of `f` gives for the constructor `c`. No `simp` needed first. -/
example (t u : Tm) (P : Int → Prop) (h : P (t.ev + u.ev)) : P (Tm.add t u).ev := by
  exact h

/-! # Part W · Worked combinations (toy objects, not the exercise's) -/

/-! ### W1. Toy addition is sound: R2, then R4 with both definitions, then R5 on what is left -/
theorem add_ok {a b : Nn} {x y : Int} (ha : a.den x) (hb : b.den y) : (a.add b).den (x + y) := by
  cases a <;> cases b <;> simp_all [Nn.add, Nn.den] <;> omega

/-! ### W2. Toy literals are sound: R10, R11, R4, and a second R11 for the nested `if` -/
theorem ofInt_ok (n : Int) : (Nn.ofInt n).den n := by
  unfold Nn.ofInt
  split
  · simp_all [Nn.den]
  · split <;> simp_all [Nn.den]

/-! ### W3. Soundness by induction with named alternatives: R12, each case by R13 with a lemma -/
example (t : Tm) : t.abs.den t.ev := by
  induction t with
    | lit n => exact ofInt_ok n
    | add t u iht ihu => exact add_ok iht ihu

/-! ### W4. Sign lemmas nest: the factors' signs give the product's sign, inside out (R7, R6) -/
example (x y z : Int) (hx : x < 0) (hy : y < 0) (hz : 0 < z) : 0 < x * y * z := by
  exact Int.mul_pos (Int.mul_pos_of_neg_of_neg hx hy) hz

end M046Guide
