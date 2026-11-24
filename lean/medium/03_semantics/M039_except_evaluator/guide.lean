/- Guide for M039 (Except evaluator).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `H` in an entry is only there to finish the example; it shows what the goal became.
The entries work on a toy evaluator (`Tm`, `run`, `Clean`: natural-number subtraction that fails
when the result would be negative), NOT on the exercise's `Expr`, `eval`, `NoDiv`; every tactic
behaves the same way on both.
Part W: worked combinations on the toy objects and on `halve` / `quarter`.
Assumed: Lean basics (E001–E033). No Mathlib.
-/

namespace M039Guide

/-! ## The four simp lemmas problem.lean gives (copied here so the entries can use them)
`m >>= f` is "run `m`; if it gives `.ok x`, continue with `f x`". A `do` block is sugar for it:
`do let x ← m; rest` is `m >>= fun x => rest`. -/

@[simp] theorem ok_bind {α β : Type} (x : α) (f : α → Except String β) :
    (Except.ok x >>= f) = f x := rfl
@[simp] theorem error_bind {α β : Type} (e : String) (f : α → Except String β) :
    (Except.error e >>= f) = Except.error e := rfl
@[simp] theorem map_ok {α β : Type} (x : α) (f : α → β) :
    (f <$> (Except.ok x : Except String α)) = Except.ok (f x) := rfl
@[simp] theorem map_error {α β : Type} (e : String) (f : α → β) :
    (f <$> (Except.error e : Except String α)) = Except.error e := rfl

/-! ## The toy objects used by the entries -/

/-- Toy expressions: literals, subtraction, and a term that always fails. -/
inductive Tm where
  | lit (n : Nat)
  | sub (a b : Tm)
  | oops

/-- Evaluate in `Except String`: subtraction fails instead of truncating at 0. -/
def run : Tm → Except String Nat
  | .lit n => pure n
  | .sub a b => do
    let x ← run a
    let y ← run b
    if x < y then throw "negative" else pure (x - y)
  | .oops => throw "oops"

/-- A predicate defined by recursion: `∧` at `sub`, `False` at `oops`. -/
def Clean : Tm → Prop
  | .lit _ => True
  | .sub a b => Clean a ∧ Clean b
  | .oops => False

/-! # Part R · Reference entries -/

/-! ## Induction with a hypothesis about the induction variable -/

/-! ### R1. `induction t with | lit n => … | sub a b iha ihb => … | oops => …` · goal list: one goal
per constructor of `Tm`; a hypothesis `h : Q t` already in the context is carried into every case,
so each IH becomes an implication `Q a → P a` -/
example (P Q : Tm → Prop) (t : Tm) (h : Q t) (H0 : ∀ n, Q (.lit n) → P (.lit n))
    (H1 : ∀ a b, (Q a → P a) → (Q b → P b) → Q (.sub a b) → P (.sub a b))
    (H2 : Q .oops → P .oops) : P t := by
  induction t with
    | lit n => ?_
    | sub a b iha ihb => ?_
    | oops => ?_
  exact H0 n h
  exact H1 a b iha ihb h
  exact H2 h

/-! ### R2. `rfl` · closes an equation that holds by computation
In `Except ε`, `pure x` IS `Except.ok x` and `throw e` IS `Except.error e` (by definition), and a
function applied to a constructor unfolds by its defining equation. `simp` does not know the first
two facts as lemmas, so a goal `throw e = Except.error e` left by `simp` needs `rfl`. -/
example {α : Type} (x : α) : (pure x : Except String α) = Except.ok x := by
  rfl

example {α : Type} (e : String) : (throw e : Except String α) = Except.error e := by
  rfl

example (n : Nat) : run (.lit n) = Except.ok n := by
  rfl

/-! ### R3. `obtain ⟨ha, hb⟩ := h` · context: `h : Clean (.sub a b)` → `ha : Clean a`, `hb : Clean b`
`Clean (.sub a b)` is by definition `Clean a ∧ Clean b`; `obtain` unfolds it to see the `∧`. -/
example (a b : Tm) (h : Clean (.sub a b)) (G : Prop) (H : Clean a → Clean b → G) : G := by
  obtain ⟨ha, hb⟩ := h
  exact H ha hb

/-! ## Unfolding and computing a `do` block -/

/-! ### R4. `simp only [run]` · goal: `run` applied to a constructor → that case's body (a `do` block) -/
example (a b : Tm) (P : Except String Nat → Prop)
    (H : P (do
      let x ← run a
      let y ← run b
      if x < y then throw "negative" else pure (x - y))) :
    P (run (.sub a b)) := by
  simp only [run]
  exact H

/-! ### R5. `simp only [iha ha]` with `iha : Q a → f a = g a`, `ha : Q a` · goal: `f a` → `g a`
`iha ha` is the IH applied to the hypothesis: an equation `f a = g a` that `simp`/`rw` can use. -/
example {α β : Type} (f g : α → β) (Q : α → Prop) (a : α) (iha : Q a → f a = g a) (ha : Q a)
    (P : β → Prop) (H : P (g a)) : P (f a) := by
  simp only [iha ha]
  exact H

/-! ### R6. `ok_bind` (given) · `Except.ok x >>= f = f x` · goal: a bind on a success continues -/
example {α β : Type} (x : α) (k : α → Except String β) (P : Except String β → Prop)
    (H : P (k x)) : P (do let y ← Except.ok x; k y) := by
  simp only [ok_bind]
  exact H

/-! ### R7. `bind_pure_comp` (core, a simp lemma) · `m >>= (fun y => pure (f y)) = f <$> m` · goal
A `do` block whose last line is `pure (…)` becomes a map `f <$> m` ("apply `f` to the result"). -/
example {α β : Type} (m : Except String α) (f : α → β) (P : Except String β → Prop)
    (H : P (f <$> m)) : P (do let y ← m; pure (f y)) := by
  simp only [bind_pure_comp]
  exact H

/-! ### R8. `map_ok` (given) · `f <$> Except.ok x = Except.ok (f x)` · goal -/
example {α β : Type} (x : α) (f : α → β) (P : Except String β → Prop) (H : P (Except.ok (f x))) :
    P (f <$> (Except.ok x : Except String α)) := by
  simp only [map_ok]
  exact H

/-! ### R9. `exact absurd h id` · closes ANY goal when `h`'s type unfolds to `False`
`absurd : a → ¬a → b`. `¬a` is `a → False`; since `Clean .oops` is `False` by definition,
`id : Clean .oops → Clean .oops` has type `¬ Clean .oops`. (`exact h.elim` does the same.) -/
example (G : Prop) (h : Clean .oops) : G := by
  exact absurd h id

/-! ## Splitting on the result of a computation -/

/-! ### R10. `cases h : m with | error e => … | ok x => …` · goal list: one goal per result of `m`;
context gains `h : m = Except.error e` (resp. `h : m = Except.ok x`) -/
example {α : Type} (m : Except String α) (G : Prop) (H0 : ∀ e, m = .error e → G)
    (H1 : ∀ x, m = .ok x → G) : G := by
  cases h : m with
    | error e => ?_
    | ok x => ?_
  exact H0 e h
  exact H1 x h

/-! ### R11. `exact ⟨w, by tac⟩` · closes `∃ y, P y` with the witness `w` and a proof of `P w`
Same as `refine ⟨w, ?_⟩` (TACTIC_STATES) followed by `tac`. -/
example (P : Nat → Prop) (H : P 3) : ∃ y, P y := by
  exact ⟨3, by exact H⟩

/-! ### R12. `pure_bind` (core, a simp lemma) · `pure x >>= f = f x` · goal
After `simp only [run]` the literal `run (.lit n)` shows up as `pure n`. -/
example {α β : Type} (x : α) (k : α → Except String β) (P : Except String β → Prop)
    (H : P (k x)) : P (do let y ← (pure x : Except String α); k y) := by
  simp only [pure_bind]
  exact H

/-! ### R13. `↓reduceIte` (a simproc `simp` runs by itself) · goal: `if c then a else b` → `a` when
`simp` can prove `c` (here `0 = 0`), → `b` when it can refute `c` -/
example {α : Type} (a b : α) (P : α → Prop) (H : P a) : P (if (0 : Int) = 0 then a else b) := by
  simp only [↓reduceIte]
  exact H

/-! ### R14. `error_bind` (given) · `Except.error e >>= f = Except.error e` · goal: a failure
skips the rest of the `do` block -/
example {α β : Type} (e : String) (k : α → Except String β) (P : Except String β → Prop)
    (H : P (Except.error e)) : P (do let y ← Except.error e; k y) := by
  simp only [error_bind]
  exact H

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `pure` is `.ok`, `throw` is `.error`, and an error short-circuits (R2) -/
def halve (n : Int) : Except String Int := if n % 2 = 0 then pure (n / 2) else throw "odd"
def quarter (n : Int) : Except String Int := do let m ← halve n; halve m

example : halve 4 = .ok 2 := rfl
example : quarter 6 = .error "odd" := rfl

/-! ### W2. A closed term: `simp [run]` runs the whole `do` block (R4, R12, R13) -/
example : run (.sub (.lit 2) (.lit 5)) = .error "negative" := by
  simp only [run]
  simp
  rfl

/-! ### W3. Case split on a sub-result, then `simp` with the equation (R10, R4, R12, R13, R14 / R6)
In the `ok` case `simp` also refutes `x < 0` (`Nat.not_lt_zero`) and simplifies `x - 0` to `x`. -/
example (a : Tm) : run (.sub a (.lit 0)) = run a := by
  cases h : run a with
    | error e => ?_
    | ok x => ?_
  simp [run, h]
  simp [run, h]

end M039Guide
