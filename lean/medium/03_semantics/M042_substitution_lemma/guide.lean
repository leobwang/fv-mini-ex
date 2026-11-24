/- Guide for M042 (The substitution lemma).
Part R: one reference entry per tactic or proof move the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h`, `k` or `hp` in an entry is only there to finish the example; it shows what the goal became.
Induction and the defining equations need a concrete inductive type, so the entries use the toy
language `Form` below (boolean formulas over numbered atoms), NOT the exercise's `AExp`.
Part W: worked combinations on `Form`.
Assumed: Lean basics (E001–E033). No Mathlib.
-/

namespace M042Guide

/-! # The toy language used by the entries

A formula `Form` is a constant, an atom `p` (a numbered propositional variable), a conjunction or a
disjunction. A valuation `σ : Nat → Bool` gives every atom a truth value. -/

inductive Form where
  | lit (b : Bool)
  | atom (p : Nat)
  | and (f g : Form)
  | or (f g : Form)

/-- The truth value of a formula under the valuation `σ`. -/
def eval (σ : Nat → Bool) : Form → Bool
  | .lit b => b
  | .atom p => σ p
  | .and f g => eval σ f && eval σ g
  | .or f g => eval σ f || eval σ g

/-- Does atom `p` occur in the formula? -/
def occ (p : Nat) : Form → Bool
  | .lit _ => false
  | .atom q => q == p
  | .and f g => occ p f || occ p g
  | .or f g => occ p f || occ p g

/-- The valuation `σ` with atom `p` reset to `b`. -/
def upd (σ : Nat → Bool) (p : Nat) (b : Bool) : Nat → Bool := fun q => if q = p then b else σ q

/-- Swap `and` and `or`, negate the constants. -/
def dual : Form → Form
  | .lit b => .lit (!b)
  | .atom p => .atom p
  | .and f g => .or (dual f) (dual g)
  | .or f g => .and (dual f) (dual g)

/-! # Part R · Reference entries -/

/-! ## Induction on an inductive type -/

/-! ### R1. `induction f with | lit b => … | atom p => … | and f g ih1 ih2 => … | or f g ih1 ih2 => …`
· goal list: one goal per constructor; context gains the constructor's arguments and, for each
argument of type `Form`, an induction hypothesis (`ih1`, `ih2`) saying the goal holds for it.
`?_` leaves a case open for the next tactic; in a proof write the case's tactics after `=>`. -/
example (P : Form → Prop) (hl : ∀ b, P (.lit b)) (ha : ∀ p, P (.atom p))
    (hand : ∀ f g, P f → P g → P (.and f g)) (hor : ∀ f g, P f → P g → P (.or f g))
    (f : Form) : P f := by
  induction f with
    | lit b => ?_
    | atom p => ?_
    | and f g ih1 ih2 => ?_
    | or f g ih1 ih2 => ?_
  exact hl b
  exact ha p
  exact hand f g ih1 ih2
  exact hor f g ih1 ih2

/-! ### R2. `rfl` · closes a goal whose two sides compute to the same value
On a constructor, a definition by pattern matching reduces by its defining equation, even when
two definitions are nested: `eval σ (dual (.atom p))` → `eval σ (.atom p)` → `σ p`. -/
example (σ : Nat → Bool) (p : Nat) : eval σ (dual (.atom p)) = σ p := by
  rfl

/-! ### R3. `by_cases h : q = p` · goal list: two copies of the goal, with `h : q = p` and `h : ¬q = p` -/
example (p q : Nat) (P : Prop) (k1 : q = p → P) (k2 : ¬q = p → P) : P := by
  by_cases h : q = p
  exact k1 h
  exact k2 h

/-! ## Unfolding definitions -/

/-! ### R4. `simp only [dual]` on `dual (constructor …)` · goal: one defining equation of `dual` applied
`simp [dual]` uses the equations `dual (.and f g) = .or (dual f) (dual g)` etc. It rewrites only where
the argument is a constructor; `dual f` with `f` a variable stays. -/
example (f g : Form) (P : Form → Prop) (hp : P (.or (dual f) (dual g))) : P (dual (.and f g)) := by
  simp only [dual]
  exact hp

/-! ### R5. `simp only [upd]` · goal: a definition whose body is `fun q => …`, applied to `q`, is
unfolded and the `fun` applied (β-reduced) -/
example (σ : Nat → Bool) (p q : Nat) (b : Bool) (P : Bool → Prop)
    (hp : P (if q = p then b else σ q)) : P (upd σ p b q) := by
  simp only [upd]
  exact hp

/-! ### R6. `simp [h]` with `h : c` or `h : ¬c` · goal: `if c then t else e` → `t` or `e`
`simp` uses `h` to turn the condition into `True` or `False`, then the lemmas `if_pos` / `if_neg`.
A hypothesis `h : q ≠ p` works like `h : ¬q = p` (`≠` unfolds to `¬ … = …`). -/
example {α : Type} (c : Prop) [Decidable c] (t e : α) (P : α → Prop) (hp : P t) (h : c) :
    P (if c then t else e) := by
  simp [h]
  exact hp

example {α : Type} (c : Prop) [Decidable c] (t e : α) (P : α → Prop) (hp : P e) (h : ¬c) :
    P (if c then t else e) := by
  simp [h]
  exact hp

/-! ### R7. `simp only [eval]`, then `rw [ih1, ih2]` · goal: unfold one step, rewrite with the IHs
In a recursive case the IHs talk about `f` and `g`, the goal about `.and f g`. Unfold first so that
`f` and `g` appear, then rewrite. `simp [eval, ih1, ih2]` does both and closes the goal. -/
example (σ τ : Nat → Bool) (f g : Form) (ih1 : eval σ f = eval τ f) (ih2 : eval σ g = eval τ g) :
    eval σ (.and f g) = eval τ (.and f g) := by
  simp only [eval]
  rw [ih1, ih2]

/-! ### R8. `| and f g ih1 ih2 | or f g ih1 ih2 => tac` · goal list: one tactic for two cases
Two alternatives that bind the same names can share one `=> tac`; `tac` runs on each case. -/
example (P : Form → Prop) (hl : ∀ b, P (.lit b)) (ha : ∀ p, P (.atom p))
    (hbin : ∀ (k : Form → Form → Form) f g, P f → P g → P (k f g)) (f : Form) : P f := by
  induction f with
    | lit b => exact hl b
    | atom p => exact ha p
    | and f g ih1 ih2 | or f g ih1 ih2 => ?_
  exact hbin _ f g ih1 ih2
  exact hbin _ f g ih1 ih2

/-! ## A hypothesis about the induction variable -/

/-! ### R9. `induction f` when a hypothesis `h` mentions `f` · each IH becomes an implication
`induction` generalises `h` by itself: in case `and f g`, `h : Q (f.and g)` and
`ih1 : Q f → R f`. To use `ih1` you must first prove `Q f` (R11, R12). -/
example (Q R : Form → Prop) (k : ∀ f, Q f → R f) (f : Form) (h : Q f) : R f := by
  induction f with
    | lit b => ?_
    | atom p => ?_
    | and f g ih1 ih2 => ?_
    | or f g ih1 ih2 => ?_
  all_goals exact k _ h

/-! ### R10. Boolean equality `q == p` · `simp` turns `(q == p) = false` into `¬q = p`
`q == p : Bool` is the boolean test (class `BEq`); `q = p : Prop` is the proposition. `simp` knows
`beq_iff_eq : (a == b) = true ↔ a = b` and `beq_eq_false_iff_ne : (a == b) = false ↔ a ≠ b`. -/
example (p q : Nat) (hne : ¬q = p) : (q == p) = false := by
  simp
  exact hne

/-! ### R11. `simpa [occ] using h` · closes the goal: simplify `h` and the goal with the same lemmas,
then `h` closes the goal. With `have hne : q ≠ p := by simpa [occ] using h` it adds a fact. -/
example (p q : Nat) (h : occ p (.atom q) = false) : q ≠ p := by
  simpa [occ] using h

/-! ### R12. `simp only [occ, Bool.or_eq_false_iff] at h` · context: `h` about `.and f g` → a conjunction
`Bool.or_eq_false_iff : (a || b) = false ↔ a = false ∧ b = false` (`||` is boolean or). -/
example (p : Nat) (f g : Form) (G : Prop) (k : occ p f = false ∧ occ p g = false → G)
    (h : occ p (.and f g) = false) : G := by
  simp only [occ, Bool.or_eq_false_iff] at h
  exact k h

/-! ### R13. `rw [ih1 h.1]` · goal: rewrite with an IH after giving it its premise
`h.1 : A` and `h.2 : B` are the two halves of `h : A ∧ B` (`And.left`, `And.right`). `ih1 h.1` is an
equation, so it can be given to `rw` or `simp`: `simp [eval, ih1 h.1, ih2 h.2]`. -/
example (Q : Form → Prop) (F G : Form → Int) (f g : Form) (ih1 : Q f → F f = G f)
    (ih2 : Q g → F g = G g) (h : Q f ∧ Q g) : F f + F g = G f + G g := by
  rw [ih1 h.1]
  rw [ih2 h.2]

/-! ## Milestones -/

/-! ### R14. `apply g` · goal: `C e` → `B e`, the premise of the lemma `g : ∀ e, B e → C e`
To prove a theorem from milestone lemmas, apply the last one and prove its premise with the others.
In term mode the same proof is `g e (f e h)`. A milestone stated with implicit arguments
(`theorem m {p : Nat} (h : …) …`) is applied without writing them. -/
example {α : Type} (A B C : α → Prop) (f : ∀ e, A e → B e) (g : ∀ e, B e → C e) (e : α) (h : A e) :
    C e := by
  apply g
  exact f e h

/-! # Part W · Worked combinations (on `Form`, not the exercise's `AExp`) -/

/-! ### W1. `dual` is an involution: R1 with R8, R2 on the leaves, R4 → R7 on the nodes -/
example (f : Form) : dual (dual f) = f := by
  induction f with
    | lit b => simp [dual]
    | atom p => rfl
    | and f g ih1 ih2 | or f g ih1 ih2 => simp [dual, ih1, ih2]

/-! ### W2. Resetting an atom to its own value changes nothing: R3, then R5 and R6 in each case -/
example (σ : Nat → Bool) (p q : Nat) : upd σ p (σ p) q = σ q := by
  by_cases h : q = p
  · simp [upd, h]
  · simp [upd, h]

/-! ### W3. `dual` keeps an absent atom absent: R9, R11 at the atom, R12 → R13 on the nodes -/
example (p : Nat) (f : Form) (h : occ p f = false) : occ p (dual f) = false := by
  induction f with
    | lit b => rfl
    | atom q => simpa [dual] using h
    | and f g ih1 ih2 | or f g ih1 ih2 =>
      simp only [occ, Bool.or_eq_false_iff] at h
      simp [dual, occ, ih1 h.1, ih2 h.2]

end M042Guide
