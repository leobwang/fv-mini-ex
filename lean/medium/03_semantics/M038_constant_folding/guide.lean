/- Guide for M038 (Constant folding).
Part R: one reference entry per tactic or proof move the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis such as `h` or `L` in an entry is only there to finish the example; it shows what the goal
became.
The entries work on toy objects (a two-argument `clip` on `Nat`, Boolean formulas `BExp` with their
value `bval`, a smart constructor `mkAnd` and a simplifier `simpB`), NOT on the exercise's `Expr`,
`eval`, `mkPlus`, `mkTimes`, `fold`; every tactic behaves the same way on both.
Part W: worked combinations on the toy objects.
Assumed: Lean basics (E001–E033). Core Lean only, no Mathlib.
-/

namespace M038Guide

/-! ## Toy objects used by the entries (not the exercise's) -/

/-- A function by pattern matching on two arguments, with a literal pattern and catch-alls. -/
def clip : Nat → Nat → Nat
  | 0, m => m
  | n, 0 => n
  | n, m => n + m

/-- Boolean formulas over atoms `atom i`. -/
inductive BExp where
  | tt
  | ff
  | atom (i : Nat)
  | and (p q : BExp)

/-- The value of a formula when atom `i` has value `ρ i`. -/
def bval (ρ : Nat → Bool) : BExp → Bool
  | .tt => true
  | .ff => false
  | .atom i => ρ i
  | .and p q => bval ρ p && bval ρ q

/-- Smart constructor for `and`: `ff` absorbs, `tt` is dropped (shaped like the exercise's `mkTimes`). -/
def mkAnd : BExp → BExp → BExp
  | .ff, _ => .ff
  | _, .ff => .ff
  | .tt, q => q
  | p, .tt => p
  | p, q => .and p q

/-- Simplify bottom-up with the smart constructor; every other formula is left alone. -/
def simpB : BExp → BExp
  | .and p q => mkAnd (simpB p) (simpB q)
  | p => p

/-! # Part R · Reference entries -/

/-! ## A smart constructor: open its `match`, one goal per arm -/

/-! ### R1. `unfold f` · goal: `f a b` with variable arguments → the `match` that is `f`'s body
`simp only [f]` unfolds it the same way. `split` (R2) cannot see inside `f` until it is unfolded. -/
example (P : Nat → Prop) (h : ∀ n, P n) (a b : Nat) : P (clip a b) := by
  unfold clip
  exact h _

/-! ### R2. `split` · goal list: one goal per arm of the `match` in the goal
In arm `k` (`case h_k`) the matched variables are replaced by the arm's pattern, and the context gains
one fact per EARLIER arm saying it did not match (`a = 0 → False`). Leftover copies of the matched
values appear as unused `x✝ : Nat`. -/
example (P : Nat → Prop) (h : ∀ n, P n) (a b : Nat) :
    P (match a, b with
      | 0, m => m
      | n, 0 => n
      | n, m => n + m) := by
  split
  all_goals exact h _

/-! ### R3. `simp_all [f]` · closes an arm goal: unfold `f` on constructors in the goal and every
hypothesis, then the simp lemmas for `&&`, `+`, `*` (`true && x = x`, `0 + x = x`, `x * 1 = x`, …).
The "earlier arm failed" hypotheses are simplified too and do no harm. -/
example (ρ : Nat → Bool) (q : BExp) :
    bval ρ q = (bval ρ .tt && bval ρ q) := by
  simp_all [bval]

example (g : Nat → Nat) (x : Nat) : g x = (0 + g x) * 1 := by
  simp_all

/-! ## The simplifier: induction on the formula -/

/-! ### R4. `induction e with | tt => … | ff => … | atom i => … | and p q ihp ihq => …` · goal list:
one goal per constructor of your own type, one IH per recursive argument (`p` and `q` here) -/
example (P : BExp → Prop) (htt : P .tt) (hff : P .ff) (hat : ∀ i, P (.atom i))
    (hand : ∀ p q, P p → P q → P (.and p q)) (e : BExp) : P e := by
  induction e with
    | tt => ?_
    | ff => ?_
    | atom i => ?_
    | and p q ihp ihq => ?_
  exact htt
  exact hff
  exact hat i
  exact hand p q ihp ihq

/-! ### R5. `rfl` · closes an equation whose two sides compute to the same term
`simpB (.atom i)` falls into the catch-all arm `p => p`, so it IS `.atom i`. A closed term (no
variables) is computed all the way down. `decide` does not work here: `BExp` has no `DecidableEq`. -/
example (ρ : Nat → Bool) (i : Nat) : bval ρ (simpB (.atom i)) = bval ρ (.atom i) := by
  rfl

example : simpB (.and .tt (.and (.atom 3) .tt)) = .atom 3 := by
  rfl

/-! ### R6. `simp [f, L, g, ihp, ihq]` · goal, shown one lemma at a time with `simp only`
`f`'s equation on a constructor (`simpB (p.and q) = mkAnd (simpB p) (simpB q)`), then your own lemma
`L` about the smart constructor, then `g`'s equation (`bval`), then the IHs; `simp` closes the final
`x = x`. `simp [simpB, L, bval, ihp, ihq]` does all of it in one call. -/
example (ρ : Nat → Bool) (p q : BExp)
    (L : ∀ x y, bval ρ (mkAnd x y) = (bval ρ x && bval ρ y))
    (ihp : bval ρ (simpB p) = bval ρ p) (ihq : bval ρ (simpB q) = bval ρ q) :
    bval ρ (simpB (.and p q)) = bval ρ (.and p q) := by
  simp only [simpB]
  simp only [L]
  simp only [bval]
  simp only [ihp, ihq]

/-! # Part W · Worked combinations on the toy objects (not the exercise's) -/

/-! ### W1. The smart constructor keeps the value: R1, R2, then R3 on every arm (`<;>`) -/
theorem bval_mkAnd (ρ : Nat → Bool) (p q : BExp) :
    bval ρ (mkAnd p q) = (bval ρ p && bval ρ q) := by
  unfold mkAnd
  split <;> simp_all [bval]

/-! ### W2. The simplifier keeps the value: R4; R5 on the leaves; R6 with W1 on `and` -/
example (ρ : Nat → Bool) (e : BExp) : bval ρ (simpB e) = bval ρ e := by
  induction e with
    | tt => rfl
    | ff => rfl
    | atom i => rfl
    | and p q ihp ihq => simp [simpB, bval_mkAnd, bval, ihp, ihq]

end M038Guide
