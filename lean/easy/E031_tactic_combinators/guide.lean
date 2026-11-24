/- Guide for E031 (Tactic combinators).
Part R: one reference entry per tactic or combinator the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`A B C T G : Prop` are arbitrary propositions; `P Q : α → Prop` stand for "the rest of the statement".
A hypothesis `k` or `h` in an entry is only there to finish the example.
A combinator such as `t <;> u` is ONE step: the infoview shows the state before it and after it, never
in between. Part W unrolls combinators into single steps so you can see the intermediate goal lists.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: E001–E030, in particular `decide` (E001), `exact`/`assumption` (E003), `∧` and
`constructor` (E005), `rcases` on `∨` (E006), `simp` (E010), `omega` (E011) and `have` (E021).
-/

namespace E031Guide

/-! # Part R · Reference entries -/

/-! ## Several goals at once -/

/-! ### R1. `refine ⟨?_, ?_, ?_⟩` · goal list: `A ∧ B ∧ C` → three goals `A`, `B`, `C`
`∧` nests to the right (`A ∧ (B ∧ C)`), and the anonymous constructor flattens the nesting, so one
`?_` per conjunct. Each `?_` becomes a new goal; a plain `_` would have to be filled by Lean itself. -/
example (A B C : Prop) (ha : A) (hb : B) (hc : C) : A ∧ B ∧ C := by
  refine ⟨?_, ?_, ?_⟩
  · exact ha
  · exact hb
  · exact hc

/-! ### R2. `t <;> u` · goal list: run `t`, then `u` on EVERY goal `t` produced
All or nothing: if `u` fails on one of those goals, the whole step fails. Goals that `u` leaves open
stay open. -/
example {α : Type} (P : α → Prop) (a b : α) (h : ∀ x, P x) : P a ∧ P b := by
  constructor <;> exact h _

/-! ### R3. `simp [h]` with `h : a = b` · goal: simp lemmas plus the rewrite `a → b`
`simp` uses its built-in lemmas (`Nat.add_zero : n + 0 = n`, `Nat.zero_add : 0 + n = n`,
`Nat.mul_one : n * 1 = n`, …) and the extra equation `h`, left to right. It closes the goal when it
reaches `True` (e.g. `b = b`). -/
example (a b : Nat) (P : Nat → Prop) (h : a = b) (k : P b) : P (0 + a * 1) := by
  simp [h]
  exact k

/-! ### R4. `all_goals u` · goal list: run `u` on every open goal
Same effect as `<;>` but as its own line: it acts on whatever goals are open at that point, not only on
those produced by the previous tactic. Also all or nothing. -/
example (A B : Prop) (ha : A) (hb : B) : A ∧ B := by
  constructor
  all_goals assumption

/-! ## Nested conjunctions -/

/-! ### R5. `constructor` · goal list: splits only the OUTERMOST `∧`
On `(A ∧ B) ∧ C` it gives `A ∧ B` and `C`; the inner `∧` needs another `constructor`. -/
example (A B C : Prop) (hab : A ∧ B) (hc : C) : (A ∧ B) ∧ C := by
  constructor
  · exact hab
  · exact hc

/-! ### R6. `t <;> u <;> v` · goal list: read as `(t <;> u) <;> v`
`v` runs on every goal left after `u` ran on every goal of `t`. Two `constructor`s split two levels. -/
example {α : Type} (P : α → Prop) (a b c d : α) (h : ∀ x, P x) :
    (P a ∧ P b) ∧ (P c ∧ P d) := by
  constructor <;> constructor <;> exact h _

/-! ### R7. `assumption` · closes the goal when some hypothesis has exactly that type
It searches the whole context, so the same `assumption` closes goals that need different hypotheses:
the tactic to put after `<;>`. -/
example (A B : Prop) (ha : A) (hb : B) : A ∧ B := by
  constructor
  · assumption
  · assumption

/-! ## Case split on a finite set of values -/

/-! ### R8. `have : T := by tac` · context gains `this : T`; goal unchanged
Without a name, the fact is called `this`. -/
example (T G : Prop) (t : T) (g : T → G) : G := by
  have : T := t
  exact g this

/-! ### R9. `omega` · closes a disjunction of linear facts
`omega` proves an `∨` of equations and inequalities that follows from the linear hypotheses: here
`5 ≤ n < 8` leaves only three values. It does NOT handle a product of two variables such as `n * n`. -/
example (n : Nat) (h1 : 5 ≤ n) (h2 : n < 8) : n = 5 ∨ n = 6 ∨ n = 7 := by
  omega

/-! ### R10. `rcases h with rfl | rfl | rfl` · goal list: one goal per value; `n` replaced everywhere
`h : n = 5 ∨ n = 6 ∨ n = 7` nests to the right; the pattern `p₁ | p₂ | p₃` splits all of it. The
pattern `rfl` substitutes `n := 5` (resp. 6, 7): `n` leaves the context, and every hypothesis and the
goal that mentioned `n` now mention the number. -/
example (n : Nat) (Q : Nat → Prop) (hq : Q n) (h : n = 5 ∨ n = 6 ∨ n = 7) : Q n := by
  rcases h with rfl | rfl | rfl
  · exact hq
  · exact hq
  · exact hq

/-! ### R11. `decide` · closes a statement about concrete numbers by computing it -/
example : 7 * 7 < 50 := by
  decide

/-! ## When the goals need different tactics -/

/-! ### R12. `first | t | u` · per goal: try `t`; if it fails, try `u`
After `<;>` it chooses separately on each goal, so goals of different kinds close in one step.
Put it last in a chain, or in parentheses: `(first | t | u)`. -/
example (A : Prop) (a : Nat) (ha : A) : A ∧ a ≤ a + 1 := by
  constructor <;> first | assumption | omega

/-! ### R13. `try t` · run `t`; if it fails, do nothing (never fails)
Use it after `<;>` when `t` applies to some goals only. Here `constructor` splits `A ∧ B` but fails on
`C`, so a plain `constructor <;> constructor` would fail. -/
example (A B C : Prop) (ha : A) (hb : B) (hc : C) : (A ∧ B) ∧ C := by
  constructor <;> try constructor
  all_goals assumption

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. R1, then one simp for all three goals (R4): list identities -/
example (xs ys : List Nat) (h : xs = ys) : xs ++ [] = ys ∧ [] ++ xs = ys ∧ xs.reverse.reverse = ys := by
  refine ⟨?_, ?_, ?_⟩
  all_goals simp [h]

/-! ### W2. `constructor <;> constructor <;> decide` unrolled into single steps (R5, R4, R11) -/
example : (0 < 1 ∧ 1 < 2) ∧ (2 < 3 ∧ 3 < 4) := by
  constructor
  all_goals constructor
  all_goals decide

/-! ### W3. Case split on values: R8 with R9, then R10, then R11 on each goal -/
example (n : Nat) (h : n < 2) : n * n = n := by
  have : n = 0 ∨ n = 1 := by omega
  rcases this with rfl | rfl
  all_goals decide

end E031Guide
