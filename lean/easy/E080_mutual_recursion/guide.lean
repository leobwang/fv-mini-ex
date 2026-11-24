/- Guide for E080 (Mutual recursion).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries split `n` with `refine match n with … => ?_` and `induction n with | … => ?_` so that every
case shows up as a goal in the infoview; in the exercise each arm may hold its proof directly.
Part W: worked combinations on a mod-3 triple `r0, r1, r2` and on a mutual pair `up, dn`, not on the
exercise's `isEven` / `isOdd`.
Assumed: Lean basics (E001–E033), recursive theorems (E048).
-/

namespace E080Guide

/-! Three functions defined by mutual recursion: `r0 n`, `r1 n`, `r2 n` say whether `n % 3` is
`0`, `1`, `2`. Each one's `n + 1` equation calls another one at `n`. -/
mutual
def r0 : Nat → Bool
  | 0 => true
  | n + 1 => r2 n
def r1 : Nat → Bool
  | 0 => false
  | n + 1 => r0 n
def r2 : Nat → Bool
  | 0 => false
  | n + 1 => r1 n
end

/-! # Part R · Reference entries -/

/-! ## Induction with both functions in the statement -/

/-! ### R1. `induction n with | zero => … | succ k ih => …` · goal list: two goals; context gains `k`, `ih`
The `succ` case names the predecessor `k` and the induction hypothesis `ih : P k`. Arms `?_` leave both
cases as goals, so the infoview shows them. -/
example (P : Nat → Prop) (h0 : P 0) (hs : ∀ k, P k → P (k + 1)) (n : Nat) : P n := by
  induction n with | zero => ?_ | succ k ih => ?_
  · exact h0
  · exact hs k ih

/-! ### R2. `rfl` · closes an equation whose two sides compute to the same value
With a literal argument every mutual function evaluates: `r1 0` is `false` and `(0 % 3 == 1)` is
`false`. -/
example : r1 0 = (0 % 3 == 1) := by
  rfl

/-! ### R3. `simp only [f, g]` · goal: every `f (k + 1)`, `g (k + 1)` → the right side of its equation
Name each mutual function you want unfolded; `simp only [r0]` alone leaves `r1 (k + 1)` untouched. -/
example (k : Nat) (P : Bool → Bool → Prop) (h : P (r2 k) (r0 k)) : P (r0 (k + 1)) (r1 (k + 1)) := by
  simp only [r0, r1]
  exact h

/-! ### R4. `Bool.not_not` · `(!!b) = b` · goal: a double Boolean negation disappears -/
example (b : Bool) (P : Bool → Prop) (h : P b) : P (!!b) := by
  rw [Bool.not_not]
  exact h

/-! ## Two-step recursion through a mutual pair -/

/-! ### R5. `match n with | 0 | 1 | m + 2` · goal list: one goal → one goal per pattern
Two unfoldings (`f` then `g`) take `m + 2` back to `m`, so the split needs two base cases. -/
example (P : Nat → Prop) (h0 : P 0) (h1 : P 1) (h2 : ∀ m, P (m + 2)) (n : Nat) : P n := by
  refine match n with
    | 0 => ?_
    | 1 => ?_
    | m + 2 => ?_
  · exact h0
  · exact h1
  · exact h2 m

/-! ### R6. `rw [f]` · goal: ONE equation of `f` is used, once
`r0 (m + 2)` is `r0 ((m + 1) + 1)`, so `rw [r0]` turns it into `r2 (m + 1)` and stops. Each further
step needs its own name: `rw [r0, r2]` gives `r1 m`. -/
example (m : Nat) (P : Bool → Prop) (h : P (r2 (m + 1))) : P (r0 (m + 2)) := by
  rw [r0]
  exact h

/-! ### R7. Recursive call `rw [thm m]` · goal: the statement at the smaller `m` used as a rewrite rule
`thm m : f m = v m` replaces `f m` by `v m`. From the case `m + 2` the call at `m` is allowed (E048). -/
theorem viaSelf (f : Nat → Nat) (h0 : f 0 = 0) (h1 : f 1 = 1) (hs : ∀ m, f (m + 2) = f m)
    (n : Nat) : f n = n % 2 := by
  refine match n with
    | 0 => h0
    | 1 => h1
    | m + 2 => ?_
  rw [hs m]
  rw [viaSelf f h0 h1 hs m]
  exact (Nat.add_mod_right m 2).symm

/-! ## Arithmetic on `%` and Boolean `==` -/

/-! ### R8. `Nat.add_mod_right` · `(x + z) % z = x % z` · goal: drop one `+ z` under `% z` -/
example (x : Nat) (P : Nat → Prop) (h : P (x % 2)) : P ((x + 2) % 2) := by
  rw [Nat.add_mod_right]
  exact h

/-! ### R9. `Nat.mul_mod_right` · `m * n % m = 0` · goal: a multiple of `m` is `0` mod `m` -/
example (m n : Nat) (P : Nat → Prop) (h : P 0) : P (m * n % m) := by
  rw [Nat.mul_mod_right]
  exact h

/-! ### R10. `BEq.rfl` · `(a == a) = true` · goal: a Boolean test of a value against itself → `true` -/
example (a : Nat) (P : Bool → Prop) (h : P true) : P (a == a) := by
  rw [BEq.rfl]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! A mutual pair on `Nat → Nat`: each step adds one and switches function. -/
mutual
def up : Nat → Nat
  | 0 => 0
  | n + 1 => dn n + 1
def dn : Nat → Nat
  | 0 => 0
  | n + 1 => up n + 1
end

/-! ### W1. Induction on a statement about both functions: R1, R2 (twice), then `simp [up, dn, ih]`
`simp` unfolds both (R3), rewrites with both halves of `ih`, and closes `k + 1 = k + 1`. -/
example (n : Nat) : up n = n ∧ dn n = n := by
  induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ k ih => simp [up, dn, ih]

/-! ### W2. Three steps back through `r0 → r2 → r1 → r0`: R5 with a third base case, R2, R6, R7, R8 -/
theorem r0_mod (n : Nat) : r0 n = (n % 3 == 0) := by
  refine match n with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | m + 3 => ?_
  rw [r0, r2, r1]
  rw [r0_mod m]
  rw [Nat.add_mod_right]

/-! ### W3. Unfold once, then a theorem already proved, R9, R10: `simp [r1, r0_mod]` does all of it -/
example (n : Nat) : r1 (3 * n + 1) = true := by
  simp only [r1]
  rw [r0_mod]
  rw [Nat.mul_mod_right]
  rw [BEq.rfl]

example (n : Nat) : r1 (3 * n + 1) = true := by
  simp [r1, r0_mod]

end E080Guide
