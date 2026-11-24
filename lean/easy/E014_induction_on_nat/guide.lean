/- Guide for E014 (Induction on Nat).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries use `induction n with | zero => ?_ | succ k ih => ?_` so that both cases show up as
goals in the infoview; in the exercise you may put the tactics right after each `=>` instead.
Part W: a worked combination on `tri` (sum `0 + 1 + … + n`), not on the exercise's `dbl` / `sumOdd`.
Assumed: Lean basics up to E013 (`rfl`, `exact`, `simp only [f]` and `simp [f]` (E010), `omega` (E011)).
-/

namespace E014Guide

/-- `trip n = 3 + 3 + … + 3` (`n` times), defined by recursion on `n`. -/
def trip : Nat → Nat
  | 0 => 0
  | n + 1 => trip n + 3

/-- `tri n = 0 + 1 + … + n`, the `n`-th triangular number. -/
def tri : Nat → Nat
  | 0 => 0
  | n + 1 => tri n + (n + 1)

/-! # Part R · Reference entries -/

/-! ## Splitting `n` into `0` and `k + 1` -/

/-! ### R1. `induction n with | zero => ?_ | succ k ih => ?_` · goal list: one goal → two goals
Case `zero`: `n` is replaced by `0`. Case `succ`: `n` is replaced by `k + 1`, and the context gains
`k` and the induction hypothesis `ih : P k`, the goal for `k`. -/
example (P : Nat → Prop) (h0 : P 0) (hs : ∀ k, P k → P (k + 1)) (n : Nat) : P n := by
  induction n with | zero => ?_ | succ k ih => ?_
  · exact h0
  · exact hs k ih

/-! ## The `zero` case -/

/-! ### R2. `rfl` · closes a goal whose two sides compute to the same closed term
`trip 0` computes to `0` by the first equation of `trip`, and `3 * 0` computes to `0`. -/
example : trip 0 = 3 * 0 := by
  rfl

/-! ## The `succ` case -/

/-! ### R3. `simp only [f]` · goal: `f (k + 1)` → the right side of `f`'s `n + 1` equation
`simp only [trip]` rewrites with `trip 0 = 0` and `trip (n + 1) = trip n + 3` wherever the argument
literally is `0` or `_ + 1`. `trip k` with an unknown `k` stays as it is. -/
example (k : Nat) (P : Nat → Prop) (h : P (trip k + 3)) : P (trip (k + 1)) := by
  simp only [trip]
  exact h

/-! ### R4. `simp only [ih]` · goal: the left side of `ih` → its right side
Here `ih : trip k = 3 * k`. After R3 the goal contains `trip k`, which `ih` replaces. -/
example (k : Nat) (ih : trip k = 3 * k) (P : Nat → Prop) (h : P (3 * k + 3)) :
    P (trip k + 3) := by
  simp only [ih]
  exact h

/-! ## Expanding products -/

/-! ### R5. `Nat.add_mul` · `(a + b) * c = a * c + b * c` · goal: distribute from the right -/
example (a b c : Nat) (P : Nat → Prop) (h : P (a * c + b * c)) : P ((a + b) * c) := by
  rw [Nat.add_mul]
  exact h

/-! ### R6. `Nat.mul_add` · `a * (b + c) = a * b + a * c` · goal: distribute from the left -/
example (a b c : Nat) (P : Nat → Prop) (h : P (a * b + a * c)) : P (a * (b + c)) := by
  rw [Nat.mul_add]
  exact h

/-! ## Arithmetic left over -/

/-! ### R7. `omega` · closes linear arithmetic over `Nat`; a product of two unknowns is one atom
Here `k * k` is treated as a single unknown number, the same on both sides, so the goal is linear. -/
example (k : Nat) : k * k + k * 1 + (1 * k + 1) = k * k + 2 * k + 1 := by
  omega

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `2 * tri n = n * (n + 1)`: R1, R2 for `zero`; for `succ` one `simp only` with R3, R4,
R5, R6, then R7. `simp only` repeats until nothing applies, so it distributes every product
whose factor is a sum, including the ones `ih` introduces. -/
example (n : Nat) : 2 * tri n = n * (n + 1) := by
  induction n with | zero => ?_ | succ k ih => ?_
  · rfl
  simp only [tri, Nat.mul_add, Nat.add_mul, ih]
  omega

end E014Guide
