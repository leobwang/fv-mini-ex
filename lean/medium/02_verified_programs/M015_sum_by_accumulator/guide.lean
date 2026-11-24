/- Guide for M015 (Sum by accumulator).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries use `induction n generalizing acc with | zero => ?_ | succ k ih => ?_` so that both
cases show up as goals in the infoview; in a proof you put the tactics right after each `=>`.
The guide's own objects, which are NOT the exercise's:
  `oddAcc n acc`  tail-recursive: adds the odd numbers `2n-1, …, 3, 1` onto the accumulator `acc`;
  `oddLoop n`     the wrapper `oddAcc n 0`, the sum of the first `n` odd numbers.
Part W: worked combinations on these objects.
Assumed: Lean basics (E001–E033), in particular E014 (induction on `Nat`, `Nat.mul_add`,
`Nat.add_mul`, `omega`). No Mathlib: everything here is core Lean.
-/

namespace M015Guide

/-- `oddAcc n acc = acc + (2n-1) + … + 3 + 1`: a loop that adds `2k+1` for `k = n-1, …, 0`. -/
def oddAcc : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => oddAcc n (acc + (2 * n + 1))

/-- `oddLoop n`: run the loop from an empty accumulator. -/
def oddLoop (n : Nat) : Nat := oddAcc n 0

/-! # Part R · Reference entries -/

/-! ## Induction with a varying accumulator -/

/-! ### R1. `induction n generalizing acc with | zero => ?_ | succ k ih => ?_` · goal list, context
Plain `induction n` keeps `acc` fixed, so `ih` speaks about that one `acc` only. `generalizing acc`
puts `acc` back into the goal, inducts, and re-introduces it in each case, so the induction
hypothesis is `ih : ∀ (acc : Nat), P k acc`: usable at the NEW accumulator of the recursive call. -/
example (P : Nat → Nat → Prop) (h0 : ∀ acc, P 0 acc)
    (h1 : ∀ k, (∀ acc, P k acc) → ∀ acc, P (k + 1) acc) (n acc : Nat) : P n acc := by
  induction n generalizing acc with | zero => ?_ | succ k ih => ?_
  · exact h0 acc
  · exact h1 k ih acc

/-! ## The `zero` case -/

/-! ### R2. `simp [f]` · closes the `zero` case: unfolds `f 0 acc`, then cleans up `0 * x`, `x + 0`
`simp` uses `f`'s first clause `f 0 acc = acc` and the core lemmas `Nat.zero_mul : 0 * n = 0`,
`Nat.mul_zero : n * 0 = 0`, `Nat.add_zero : n + 0 = n`; then both sides are equal. -/
example (acc : Nat) : oddAcc 0 acc = acc + 0 * 0 := by
  simp [oddAcc]

/-! ## The `succ` case -/

/-! ### R3. `simp only [f]` · goal: `f (k + 1) acc` → `f`'s second clause, with the NEW accumulator
A call is unfolded only when its first argument is visibly `0` or `_ + 1`; `oddAcc k t` with an
unknown `k` stays. -/
example (k acc : Nat) (P : Nat → Prop) (h : P (oddAcc k (acc + (2 * k + 1)))) :
    P (oddAcc (k + 1) acc) := by
  simp only [oddAcc]
  exact h

/-! ### R4. `simp only [ih]` with `ih : ∀ acc, c * f k acc = g acc` · goal: `c * f k t` → `g t`
`simp` instantiates the `∀` itself (`acc := t`). The left side of `ih` must appear literally:
`c * f k t` is matched, but `f k t` alone (without `c *`) or `c * (f k t + 1)` is not. -/
example (f : Nat → Nat → Nat) (g : Nat → Nat) (c k t : Nat)
    (ih : ∀ acc, c * f k acc = g acc) (P : Nat → Prop) (h : P (g t)) : P (c * f k t) := by
  simp only [ih]
  exact h

/-! ## Expanding products -/

/-! ### R5. `Nat.mul_add` · `a * (b + c) = a * b + a * c` · goal: distribute from the left -/
example (a b c : Nat) (P : Nat → Prop) (h : P (a * b + a * c)) : P (a * (b + c)) := by
  rw [Nat.mul_add]
  exact h

/-! ### R6. `Nat.add_mul` · `(a + b) * c = a * c + b * c` · goal: distribute from the right -/
example (a b c : Nat) (P : Nat → Prop) (h : P (a * c + b * c)) : P ((a + b) * c) := by
  rw [Nat.add_mul]
  exact h

/-! ### R7. `omega` · closes linear arithmetic over `Nat`; a product of two unknowns is one atom
`k * k` is one unknown number, the same on both sides; `k * 1`, `1 * k` count as `k`. -/
example (a k : Nat) : a + (2 * k + 1) + k * k = a + (k * k + 1 * k + (k * 1 + 1 * 1)) := by
  omega

/-! ## Specialising the accumulator lemma -/

/-! ### R8. `simp only [g]` · goal: a non-recursive wrapper `g n` → its body
`oddLoop n` becomes `oddAcc n 0`: the loop started at accumulator `0`. -/
example (n : Nat) (P : Nat → Prop) (h : P (oddAcc n 0)) : P (oddLoop n) := by
  simp only [oddLoop]
  exact h

/-! ### R9. `rw [L]` with `L : ∀ n acc, c * f n acc = c * acc + g n` · goal: the case `acc = 0`
`rw` instantiates both `∀`s from the goal (`n := n`, `acc := 0`). With your own theorem `L`
declared above, write `rw [L]` the same way. -/
example (f : Nat → Nat → Nat) (g : Nat → Nat) (c n : Nat)
    (L : ∀ n acc, c * f n acc = c * acc + g n) (P : Nat → Prop) (h : P (c * 0 + g n)) :
    P (c * f n 0) := by
  rw [L]
  exact h

/-! ### R10. `Nat.mul_zero`, `Nat.zero_add` · goal: `c * 0 + x` → `x` (`simp` uses both by itself) -/
example (c x : Nat) (P : Nat → Prop) (h : P x) : P (c * 0 + x) := by
  rw [Nat.mul_zero]
  rw [Nat.zero_add]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The loop invariant for `oddAcc`: R1, R2 for `zero`; R3, R4, R5, R6 in one `simp only`,
then R7. `simp only` repeats until nothing applies. -/
example (n acc : Nat) : oddAcc n acc = acc + n * n := by
  induction n generalizing acc with | zero => ?_ | succ k ih => ?_
  · simp [oddAcc]
  simp only [oddAcc, ih, Nat.mul_add, Nat.add_mul]
  omega

/-! ### W2. Using the invariant at `acc = 0`: R8, R9, R10
`L` stands for the invariant, proved as its own theorem above. -/
example (L : ∀ n acc, 3 * oddAcc n acc = 3 * acc + 3 * (n * n)) (n : Nat) :
    3 * oddLoop n = 3 * (n * n) := by
  simp only [oddLoop]
  rw [L]
  simp

end M015Guide
