/- Guide for E048 (Recursive theorems).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries split on `n` with `refine match n with … => ?_` so that every case shows up as a goal in
the infoview; in the exercise you may write the same `match` directly after `:=` (term mode).
Part W: worked combinations on `half` (n ↦ ⌊n / 2⌋) and on powers of 3, not on the exercise's
`fib` / `evenB`.
Assumed: Lean basics (E001–E033).
-/

namespace E048Guide

/-- `half n = ⌊n / 2⌋`, defined by the same three-case pattern as a two-step recursion. -/
def half : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => half n + 1

/-! # Part R · Reference entries -/

/-! ## Splitting `n` the way the definition does -/

/-! ### R1. `match n with | 0 | 1 | m + 2` · goal list: one goal → one goal per pattern
`refine match n with | 0 => ?_ | 1 => ?_ | m + 2 => ?_` leaves the three `?_` as goals. The patterns
must cover every `Nat` exactly as a definition's equations do. `n` stays in the context, unused. -/
example (P : Nat → Prop) (h0 : P 0) (h1 : P 1) (h2 : ∀ m, P (m + 2)) (n : Nat) : P n := by
  refine match n with
    | 0 => ?_
    | 1 => ?_
    | m + 2 => ?_
  · exact h0
  · exact h1
  · exact h2 m

/-! ### R2. `decide` · closes a base case: a computable function at a literal
`half 1` and `2 ^ 1` are closed terms, so `decide` evaluates both sides of `<`. -/
example : half 1 < 2 ^ 1 := by
  decide

/-! ### R3. Recursive call `have ih := thm … m` · context gains the induction hypothesis
Inside its own proof a `theorem` may call itself on arguments structurally smaller than the case it is
in: from the case `m + 2`, both `m` and `m + 1` are allowed. The call is an ordinary proof term. -/
theorem twoStep (P : Nat → Prop) (h0 : P 0) (h1 : P 1) (step : ∀ m, P m → P (m + 1) → P (m + 2))
    (n : Nat) : P n := by
  refine match n with
    | 0 => h0
    | 1 => h1
    | m + 2 => ?_
  have ih1 := twoStep P h0 h1 step m
  have ih2 := twoStep P h0 h1 step (m + 1)
  exact step m ih1 ih2

/-! ## Unfolding a recursive definition -/

/-! ### R4. `simp only [f]` · goal: `f (m + 2)` → the right side of `f`'s `n + 2` equation
`simp only [half]` uses the equations `half 0 = 0`, `half 1 = 0`, `half (n + 2) = half n + 1`. It
rewrites only where the argument, as written, has one of the shapes `0`, `1`, `_ + 2` (a numeral offset
counts: `n + 3` is read as `(n + 1) + 2`). `2 * (m + 1)` does not match, although it computes to
`2 * m + 2` (R10). -/
example (n : Nat) (P : Nat → Prop) (h : P (half n + 1)) : P (half (n + 2)) := by
  simp only [half]
  exact h

/-! ### R5. `simp only [f] at *` · context and goal: unfold in every hypothesis and in the goal
`at h` rewrites only `h`; `at *` rewrites all hypotheses and the goal. -/
example (n : Nat) (P Q : Nat → Prop) (h : P (half (n + 2))) (g : ∀ k, P k → Q k) :
    Q (half (n + 2)) := by
  simp only [half] at *
  exact g _ h

/-! ## Arithmetic with powers -/

/-! ### R6. `Nat.pow_succ` · `b ^ (n + 1) = b ^ n * b` · goal
Lean states it as `Nat.pow_succ (n m : Nat) : n ^ m.succ = n ^ m * n`; `m.succ` is `m + 1`.
`simp only [Nat.pow_succ]` repeats it, so `b ^ (n + 2)` becomes `b ^ n * b * b` (W3). -/
example (b n : Nat) (P : Nat → Prop) (h : P (b ^ n * b)) : P (b ^ (n + 1)) := by
  rw [Nat.pow_succ]
  exact h

/-! ### R7. `omega` · closes linear arithmetic over `Nat`/`Int`; other terms are unknowns
`3 ^ k` (and any `f x`) is one opaque number to `omega`, so `3 ^ k * 3` is linear in it. -/
example (x y k : Nat) (hx : x < 3 ^ k) (hy : y ≤ 3 ^ k * 3) : x + y < 3 ^ k * 4 := by
  omega

/-! ## One-step split, arguments of the form `2 * n` -/

/-! ### R8. `match n with | 0 | m + 1` · goal list: one goal → two goals -/
example (P : Nat → Prop) (h0 : P 0) (h : ∀ m, P (m + 1)) (n : Nat) : P n := by
  refine match n with
    | 0 => ?_
    | m + 1 => ?_
  · exact h0
  · exact h m

/-! ### R9. `rfl` · closes `f (2 * 0) = v`: Lean computes `2 * 0` to `0`, then `f 0` -/
example : half (2 * 0) = 0 := by
  rfl

/-! ### R10. `show G'` · goal `G` → `G'`, when `G` and `G'` are equal by computation
`Nat.mul` recurses on its second argument: `2 * (m + 1)` computes to `2 * m + 2`. `show` checks the
two goals are definitionally equal (equal after unfolding), and fails otherwise. -/
example (P : Nat → Prop) (m : Nat) (h : P (2 * m + 2)) : P (2 * (m + 1)) := by
  show P (2 * m + 2)
  exact h

/-- The odd form: the outermost operation must become `_ + 2`, so regroup as `(2 * m + 1) + 2`. -/
example (P : Nat → Prop) (m : Nat) (h : P (2 * m + 1 + 2)) : P (2 * (m + 1) + 1) := by
  show P (2 * m + 1 + 2)
  exact h

/-! ### R11. Recursive call `exact thm … m` · closes a goal that is the statement at a smaller `m` -/
theorem oneStep (P : Nat → Prop) (h0 : P 0) (step : ∀ m, P m → P (m + 1)) (n : Nat) : P n := by
  refine match n with
    | 0 => h0
    | m + 1 => step m ?_
  exact oneStep P h0 step m

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Three cases, two base cases by `decide`, one recursive call, unfold, `omega`
R1, R2, R3, R4, R7. -/
theorem half_le (n : Nat) : half n ≤ n := by
  refine match n with
    | 0 => ?_
    | 1 => ?_
    | m + 2 => ?_
  · decide
  · decide
  · have ih := half_le m
    simp only [half]
    omega

/-! ### W2. Arguments `2 * n`: `show` the `_ + 2` form, unfold, close with the recursive call
R8, R9, R10, R4, then `rw [half_double m]` (R11 used through `rw`). -/
theorem half_double (n : Nat) : half (2 * n) = n := by
  refine match n with
    | 0 => rfl
    | m + 1 => ?_
  show half (2 * m + 2) = m + 1
  simp only [half]
  rw [half_double m]

/-! ### W3. Powers with a `+ 2` exponent: rewrite to `b ^ k * b * b` everywhere, then `omega`
R5 with R6, then R7. -/
example (x k : Nat) (h : x < 3 ^ (k + 1)) : x + x < 3 ^ (k + 2) := by
  simp only [Nat.pow_succ] at *
  omega

end E048Guide
