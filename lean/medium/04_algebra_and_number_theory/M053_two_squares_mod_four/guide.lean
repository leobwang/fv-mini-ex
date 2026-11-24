/- Guide for M053 (Sums of two squares mod 4).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` (or `g : … → G`) in an entry is only there to finish the example; it shows what the
goal or the context became.
Part W: worked combinations on objects that are NOT the exercise's (cubes mod 9, squares mod 3,
a residue mod 5).
Assumed: Lean basics.
-/
import Mathlib

namespace M053Guide

/-! # Part R · Reference entries -/

/-! ## Checking every element of a finite type -/

/-! ### R1. `revert x` · context loses `x : α`; goal `P x` → `∀ x, P x`
The inverse of `intro x`. -/
example {α : Type} (P : α → Prop) (h : ∀ x, P x) (x : α) : P x := by
  revert x
  exact h

/-! ### R2. `decide` · closes a closed statement by evaluating it
`ZMod n` (integers mod `n`) has `n` elements when `n > 0`, so `∀ x : ZMod n, …` with `=`, `∨`, `∧`,
`→` is decided by checking every element. The goal must mention no variable from the context (R1). -/
example : ∀ x : ZMod 3, x ^ 3 = x := by
  decide

/-! ## From an integer statement to `ZMod n` -/

/-! ### R3. `intro h` on `≠` · goal `a ≠ b` → `False`; context gains `h : a = b`
`a ≠ b` is notation for `¬ (a = b)`, which is defined as `a = b → False`. -/
example {α : Type} (a b : α) (g : a = b → False) : a ≠ b := by
  intro h
  exact g h

/-! ### R4. `ZMod.intCast_mod` · `∀ (a : ℤ) (b : ℕ), ((a % ↑b : ℤ) : ZMod b) = (a : ZMod b)` · context
Casting `a` into `ZMod b` forgets everything but its remainder mod `b`. The modulus `b` is a `ℕ`; inside
`a % ↑b` it is cast to `ℤ`. -/
example (a : ℤ) (n : ℕ) (G : Prop) (g : ((a % (n : ℤ) : ℤ) : ZMod n) = (a : ZMod n) → G) : G := by
  have h1 := ZMod.intCast_mod a n
  exact g h1

/-! ### R5. `push_cast at h1` · context: casts in `h1` move inward
Lemmas `Int.cast_add : ↑(a + b) = ↑a + ↑b` and `Int.cast_pow : ↑(a ^ k) = ↑a ^ k`, for the cast
`ℤ → R` into any ring `R` (`ZMod n`, `ℚ`, `ℝ`, `ℂ`). A cast of `%` does NOT move: `↑(a % m)` stays. -/
example {R : Type} [CommRing R] (a b : ℤ) (k : ℕ) (G : Prop) (h1 : ((a ^ k + b : ℤ) : R) = 0)
    (g : (a : R) ^ k + (b : R) = 0 → G) : G := by
  push_cast at h1
  exact g h1

/-! ### R6. `push_cast` on a numeral cast · goal: `↑4` (the `ℕ`-numeral `4` cast to `ℤ`) → `4`
Lemma `Nat.cast_ofNat : ((OfNat.ofNat n : ℕ) : R) = OfNat.ofNat n`. `R4` produces such a `↑4`. -/
example (a : ℤ) (P : ℤ → Prop) (h : P (a % 4)) : P (a % ((4 : ℕ) : ℤ)) := by
  push_cast
  exact h

/-! ### R7. `push_cast [h] at h1` · context: push casts in `h1` AND rewrite it with `h : a % ↑n = r` -/
example (n : ℕ) (a r : ℤ) (h : a % n = r) (h1 : ((a % (n : ℤ) : ℤ) : ZMod n) = (a : ZMod n))
    (g : (r : ZMod n) = (a : ZMod n) → False) : False := by
  push_cast [h] at h1
  exact g h1

/-! ## Forgetting where an element came from -/

/-! ### R8. `generalize (a : ZMod n) = x at h1` · context gains `x : ZMod n`; `↑a` in `h1` → `x`
Afterwards nothing records that `x` is a cast of `a`, so a claim about `x` is a claim about every
element of `ZMod n`. -/
example (a : ℤ) (n : ℕ) (Q : ZMod n → Prop) (h1 : Q (a : ZMod n)) (g : ∀ x : ZMod n, Q x → False) :
    False := by
  generalize (a : ZMod n) = x at h1
  exact g x h1

/-! ### R9. `revert x y` with `h1` mentioning them · context loses `x y` and `h1`; goal gains
`∀ x y, (type of h1) → …`. `revert` takes every hypothesis that depends on `x` or `y` along. -/
example {α : Type} (Q : α → α → Prop) (G : Prop) (g : ∀ x y, Q x y → G) (x y : α) (h1 : Q x y) :
    G := by
  revert x y
  exact g

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Cubes mod 9 are `0`, `1` or `8`: R1, R2 -/
example (x : ZMod 9) : x ^ 3 = 0 ∨ x ^ 3 = 1 ∨ x ^ 3 = 8 := by
  revert x
  decide

/-! ### W2. No square is `2 mod 3`: R3, R4, R7, R8, R9, R2 -/
example (a : ℤ) : a ^ 2 % 3 ≠ 2 := by
  intro h
  have h1 := ZMod.intCast_mod (a ^ 2) 3
  push_cast [h] at h1
  generalize (a : ZMod 3) = x at h1
  revert x
  decide

/-! ### W3. The long way round R7: `push_cast`, then `rw`, then `push_cast` again
`rw [h] at h1` only works once R6 has turned `↑5` into `5`; the result `↑2` is a cast of the
integer `2`, which the second `push_cast` turns into the `ZMod 5` numeral `2`. -/
example (a : ℤ) (h : a % 5 = 2) : (2 : ZMod 5) = a := by
  have h1 := ZMod.intCast_mod a 5
  push_cast at h1
  rw [h] at h1
  push_cast at h1
  exact h1

end M053Guide
