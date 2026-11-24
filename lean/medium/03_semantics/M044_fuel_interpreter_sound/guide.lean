/- Guide for M044 (A fuel-based interpreter is sound and monotone).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` (or `Q`) stands for "the rest of your goal": the step changes only the part shown inside `P (…)`.
A hypothesis such as `hb` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on a toy fuel function `tick` that is NOT the exercise's interpreter.
Assumed: Lean basics (E001–E033). Core Lean only, no Mathlib.
-/

namespace M044Guide

/-! ## Toy objects used by some entries (not the exercise's) -/

/-- A toy fuel-driven function: the sum of a list, one unit of fuel per element.
`none` means "ran out of fuel". -/
def tick : Nat → List Nat → Option Nat
  | 0, _ => none
  | _ + 1, [] => some 0
  | n + 1, x :: xs =>
    match tick n xs with
    | some t => some (x + t)
    | none => none

/-- The relational ("big-step") description of the same sum. -/
inductive Sums : List Nat → Nat → Prop
  | nil : Sums [] 0
  | cons {x : Nat} {xs : List Nat} {t : Nat} : Sums xs t → Sums (x :: xs) (x + t)

/-- A type with a constructor whose name is a keyword. -/
inductive Tok where
  | «if»
  | num (k : Nat)

/-! # Part R · Reference entries -/

/-! ## Induction on the fuel -/

/-! ### R1. `induction n generalizing x with | zero => … | succ n ih => …` · goal list: one goal per case
`generalizing x` puts `x` back under `∀` first, so the IH `ih` holds for EVERY `x`, not only the
one in the context. -/
example (P : Nat → Nat → Prop) (h0 : ∀ x, P 0 x) (hs : ∀ n, (∀ x, P n x) → ∀ x, P (n + 1) x)
    (n x : Nat) : P n x := by
  induction n generalizing x with
    | zero => exact h0 x
    | succ n ih => exact hs n ih x

/-! R1, one goal at a time: without `with` the new names are inaccessible (`n✝`, `a✝`);
`rename_i n ih` names them as `| succ n ih` would. -/
example (P : Nat → Nat → Prop) (h0 : ∀ x, P 0 x) (hs : ∀ n, (∀ x, P n x) → ∀ x, P (n + 1) x)
    (n x : Nat) : P n x := by
  induction n generalizing x
  · exact h0 x
  rename_i n ih
  exact hs n ih x

/-! ## Unfolding one step of a fuel function -/

/-! ### R2. `simp only [f] at h` · context: `h` with one defining equation of `f` applied
It fires when the arguments of `f` match a pattern of its definition (`0`, `n + 1` with a constructor). -/
example (n r : Nat) (Q : Prop) (hq : 0 = r → Q) (h : tick (n + 1) [] = some r) : Q := by
  simp only [tick] at h
  simp only [Option.some.injEq] at h
  exact hq h

/-! ### R3. `simp at h` · goal list: closes the goal when `h` is `none = some a`
Different constructors are never equal, so `h` simplifies to `False`, and a `False` hypothesis
proves anything. `simp [f] at h` does R2 and R3 in one step. -/
example {α : Type} (a : α) (Q : Prop) (h : (none : Option α) = some a) : Q := by
  simp at h

example (xs : List Nat) (r : Nat) (Q : Prop) (h : tick 0 xs = some r) : Q := by
  simp [tick] at h

/-! ## Case analysis on the command -/

/-! ### R4. `cases t with | «if» => … | num k => …` · goal list: one goal per constructor
A constructor named by a keyword (`if`, `while`) is written in guillemets `«…»`. -/
example (P : Tok → Prop) (h1 : P .«if») (h2 : ∀ k, P (.num k)) (t : Tok) : P t := by
  cases t with
    | «if» => exact h1
    | num k => exact h2 k

/-! R4, one goal at a time. -/
example (P : Tok → Prop) (h1 : P .«if») (h2 : ∀ k, P (.num k)) (t : Tok) : P t := by
  cases t
  · exact h1
  rename_i k
  exact h2 k

/-! ## Turning `some a = some b` into a usable equation -/

/-! ### R5. `Option.some.injEq` · `(some a = some b) = (a = b)` · context: `h` loses the `some`s -/
example {α : Type} (a b : α) (Q : Prop) (hq : a = b → Q) (h : some a = some b) : Q := by
  simp only [Option.some.injEq] at h
  exact hq h

/-! ### R6. `subst h` · context and goal: `h : a = b` with `b` a variable; `b` is replaced by `a` everywhere -/
example {α : Type} (a b : α) (P : α → α → Prop) (hp : P a a) (h : a = b) : P a b := by
  subst h
  exact hp

/-! ### R7. `exact .ctor args` · closes the goal with a constructor of the goal's inductive type
`.nil` means `Sums.nil`: Lean reads the namespace off the goal `Sums …`. -/
example : Sums [] 0 := by
  exact .nil

example (x t : Nat) (xs : List Nat) (hxs : Sums xs t) : Sums (x :: xs) (x + t) := by
  exact .cons hxs

/-! ## Which branch produced the result? -/

/-! ### R8. `split at h` on a `match` · goal list: one goal per branch, the branch fact in the context
In the `some` branch the matched value is a new inaccessible variable `y✝`, and `heq✝` records
`f a = some y✝`; in the `none` branch `heq✝ : f a = none`. -/
example {α : Type} (f k : α → Option α) (a z : α) (Q : Prop)
    (h1 : ∀ y, f a = some y → k y = some z → Q) (h2 : f a = none → Q)
    (h : (match f a with | some y => k y | none => none) = some z) : Q := by
  split at h
  · exact h1 _ ‹_› h
  · exact h2 ‹_›

/-! ### R9. `‹T›` · a term: "the hypothesis of type `T`", also when its name is inaccessible (`h✝`)
`‹_›` lets Lean infer `T` from where the term is used. -/
example (A B : Prop) (f : A → B) : A → B := by
  intro _
  exact f ‹_›

/-! ### R10. `ih _ _ h` · apply a generalized IH; the `_` are found by unifying with `h` -/
example (R S : Nat → Nat → Prop) (ih : ∀ x y, R x y → S x y) (a b : Nat) (h : R a b) : S a b := by
  exact ih _ _ h

/-! ### R11. `split at h` on an `if` · goal list: two goals, with `h✝ : c` and `h✝ : ¬c` -/
example {α : Type} (b : Bool) (t e : Option α) (z : α) (Q : Prop)
    (h1 : b = true → t = some z → Q) (h2 : ¬b = true → e = some z → Q)
    (h : (if b = true then t else e) = some z) : Q := by
  split at h
  · exact h1 ‹_› h
  · exact h2 ‹_› h

/-! ### R12. `simpa using h` with `Bool.not_eq_true` · closes `b = false` from `h : ¬b = true` -/
example (b : Bool) (h : ¬b = true) : b = false := by
  simpa using h

/-! ## Monotonicity: unfold both sides, rewrite the inner call -/

/-! ### R13. `simp only [f] at h ⊢` · context and goal: unfold one step in `h` and in the goal -/
example (n r : Nat) (h : tick (n + 1) [] = some r) : tick (n + 1 + 1) [] = some r := by
  simp only [tick] at h ⊢
  exact h

/-! ### R14. `simpa [f] using h` · closes the goal when goal and `h` simplify to the same statement -/
example (n r : Nat) (h : tick (n + 1) [] = some r) : tick (n + 1 + 1) [] = some r := by
  simpa [tick] using h

/-! ### R15. `rw [h]` inside a `match`, then `exact` · goal: the scrutinee becomes `some b`
`match some b with | some y => k y | …` is `k b` by definition, so `exact` accepts a proof of `k b = r`. -/
example {α : Type} (f k : α → Option α) (a b : α) (r : Option α) (h : f a = some b) (hk : k b = r) :
    (match f a with | some y => k y | none => none) = r := by
  rw [h]
  exact hk

/-! ### R16. `if_pos` · `c → (if c then t else e) = t` · goal: the `if` → its `then` branch -/
example {α : Type} (c : Prop) [Decidable c] (t e : α) (P : α → Prop) (hc : c) (hp : P t) :
    P (if c then t else e) := by
  rw [if_pos hc]
  exact hp

/-! ### R17. `if_neg` · `¬c → (if c then t else e) = e` · goal: the `if` → its `else` branch -/
example {α : Type} (c : Prop) [Decidable c] (t e : α) (P : α → Prop) (hc : ¬c) (hp : P e) :
    P (if c then t else e) := by
  rw [if_neg hc]
  exact hp

/-! # Part W · Worked combinations on `tick` (not the exercise's interpreter) -/

/-! ### W1. Soundness of `tick`: R1, R3, R4, R2, R5, R6, R7, R8, R9, R10 -/
example (n : Nat) (xs : List Nat) (r : Nat) (h : tick n xs = some r) : Sums xs r := by
  induction n generalizing xs r with
    | zero => simp [tick] at h
    | succ n ih =>
      cases xs with
      | nil =>
        simp only [tick, Option.some.injEq] at h
        subst h
        exact .nil
      | cons x xs =>
        simp only [tick] at h
        split at h
        · simp only [Option.some.injEq] at h
          subst h
          exact .cons (ih _ _ ‹_›)
        · simp at h

/-! ### W2. Monotonicity of `tick`: R1, R3, R4, R14, R13, R8, R15, R10 -/
example (n : Nat) (xs : List Nat) (r : Nat) (h : tick n xs = some r) :
    tick (n + 1) xs = some r := by
  induction n generalizing xs r with
    | zero => simp [tick] at h
    | succ n ih =>
      cases xs with
      | nil => simpa [tick] using h
      | cons x xs =>
        simp only [tick] at h ⊢
        split at h
        · rw [ih _ _ ‹_›]
          exact h
        · simp at h

end M044Guide
