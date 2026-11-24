/- Guide for M026 (Fibonacci, iterative).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries use the guide's own objects, which are NOT the exercise's:
  `pell n`          the Pell numbers 0, 1, 2, 5, 12, 29, …: `pell (n + 2) = 2 * pell (n + 1) + pell n`;
  `pellAux n a b`   the same recurrence run `n` times on an accumulator pair `(a, b)`;
  `pellIter n`      `pellAux n 0 1`, the linear-time version.
Part W: the worked combination on `pell`.
Assumed: Lean basics (E001–E033). Core Lean only: no Mathlib.
-/

namespace M026Guide

/-- Pell numbers, the exponential-time recursive definition. -/
def pell : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * pell (n + 1) + pell n

/-- `n` steps of `(a, b) ↦ (b, 2 * b + a)`, then return the first component. -/
def pellAux (n a b : Nat) : Nat :=
  match n with
  | 0 => a
  | n + 1 => pellAux n b (2 * b + a)

/-- Linear time: start the accumulator pair at `(pell 0, pell 1) = (0, 1)`. -/
def pellIter (n : Nat) : Nat := pellAux n 0 1

/-! # Part R · Reference entries -/

/-! ## Induction with a re-quantified start index -/

/-! ### R1. `induction n generalizing k with | zero => ?_ | succ n ih => ?_` · goal list: two goals;
context: `ih : ∀ (k : Nat), …`
`generalizing k` removes `k` from the context before the induction, so the statement proved by
induction is `∀ k, P n k` and the hypothesis `ih` holds for EVERY `k`. You will use it at `k + 1`
(R5), not at `k`. -/
example (P : Nat → Nat → Prop) (h0 : ∀ k, P 0 k) (hs : ∀ n, (∀ k, P n k) → ∀ k, P (n + 1) k)
    (n k : Nat) : P n k := by
  induction n generalizing k with | zero => ?_ | succ n ih => ?_
  · exact h0 k
  · exact hs n ih k

/-! ### R2. `rfl` · closes the zero case: both sides compute to the same value
`pellAux 0 a b` computes to `a` (first equation), and `k + 0` computes to `k` (`Nat.add` recurses on
its second argument), so both sides become `f k`. -/
example (f : Nat → Nat) (k : Nat) : pellAux 0 (f k) (f (k + 1)) = f (k + 0) := by
  rfl

/-! ## The succession step -/

/-! ### R3. `have h : e₁ = e₂ := rfl` · context gains an equation that holds by computation
`pell (k + 1 + 1)` matches the pattern `n + 2` with `n := k`, so it computes to the right side of
that equation. Stating the fact right to left gives `rw [h]` the direction you need: it folds the
sum back into one `pell` application. -/
example (k : Nat) (G : Prop) (t : G) : G := by
  have h : 2 * pell (k + 1) + pell k = pell (k + 1 + 1) := rfl
  exact t

/-! ### R4. `simp only [pellAux]` · goal: one accumulator step `pellAux (n + 1) a b` →
`pellAux n b (2 * b + a)`
It rewrites with `pellAux`'s equations, only where the first argument literally is `0` or `_ + 1`. -/
example (n a b : Nat) (P : Nat → Prop) (h : P (pellAux n b (2 * b + a))) :
    P (pellAux (n + 1) a b) := by
  simp only [pellAux]
  exact h

/-! ### R5. `rw [ih (k + 1)]` · goal: use the generalised hypothesis at a different index
`ih : ∀ (k : Nat), g n (f k) (f (k + 1)) = f (k + n)`. `ih (k + 1)` is the instance
`g n (f (k + 1)) (f (k + 1 + 1)) = f (k + 1 + n)`; `rw` needs its left side literally in the goal.
`g : (n a b : Nat) → Nat` is the type `Nat → Nat → Nat → Nat` with its arguments named (steps,
accumulator pair); the infoview prints the arrow form. `g` plays `pellAux`, `f` plays `pell`. -/
example (g : (n a b : Nat) → Nat) (f : Nat → Nat) (n k : Nat) (P : Nat → Prop)
    (ih : ∀ (k : Nat), g n (f k) (f (k + 1)) = f (k + n)) (h : P (f (k + 1 + n))) :
    P (g n (f (k + 1)) (f (k + 1 + 1))) := by
  rw [ih (k + 1)]
  exact h

/-! ### R6. `congr 1` · goal `f a = f b` → `a = b`
It strips one function application from both sides. The new goal can be harder than the old one
(it may be false while `f a = f b` is true), but here the arguments really are equal. `congr 1`
closes the new goal itself when it is `rfl` or a hypothesis; otherwise it stays for you (R7). -/
example (f : Nat → Nat) (k n : Nat) : f (k + 1 + n) = f (k + (n + 1)) := by
  congr 1
  omega

/-! ### R7. `omega` · closes linear arithmetic over `Nat`/`Int`
`k + 1 + n` is `(k + 1) + n` (`+` groups to the left); `omega` proves it equals `k + (n + 1)`. -/
example (k n : Nat) : k + 1 + n = k + (n + 1) := by
  omega

/-! ## From the milestone to the theorem -/

/-! ### R8. `have h := thm n 0` · context gains the milestone at the start index `k := 0`
A theorem with explicit arguments is a function: `thm n 0` is its statement with `k` replaced by `0`.
Lean does not simplify the instance: `0 + 1` and `0 + n` stay as written. -/
theorem shift (g : (n a b : Nat) → Nat) (f : Nat → Nat)
    (hg : ∀ n k, g n (f k) (f (k + 1)) = f (k + n)) (n k : Nat) :
    g n (f k) (f (k + 1)) = f (k + n) := hg n k

example (g : (n a b : Nat) → Nat) (f : Nat → Nat)
    (hg : ∀ n k, g n (f k) (f (k + 1)) = f (k + n)) (n : Nat) (G : Prop) (t : G) : G := by
  have h := shift g f hg n 0
  exact t

/-! ### R9. `simp only [Nat.zero_add] at h` · context: `0 + x` → `x` inside `h`
`Nat.zero_add (n : Nat) : 0 + n = n`. It is not true by `rfl` for a variable `n` (`Nat.add`
recurses on its SECOND argument), so it needs this lemma. -/
example (g : (n a b : Nat) → Nat) (f : Nat → Nat) (n : Nat) (G : Prop)
    (t : g n (f 0) (f 1) = f n → G) (h : g n (f 0) (f (0 + 1)) = f n) : G := by
  simp only [Nat.zero_add] at h
  exact t h

/-! ### R10. `exact h` · closes a goal that equals `h`'s type after unfolding definitions
`exact` accepts `h` when its type and the goal are definitionally equal: here `pellIter n` unfolds
to `pellAux n 0 1`, and `pell 0`, `pell 1` compute to `0`, `1`. No rewriting needed. -/
example (n : Nat) (h : pellAux n (pell 0) (pell 1) = pell n) : pellIter n = pell n := by
  exact h

/-! # Part W · Worked combination (not the exercise's objects) -/

/-! ### W1. The Pell accumulator invariant: after `n` steps from `(pell k, pell (k + 1))` the pair is
`(pell (k + n), …)`. R1, R2, then in the succ case R3, R4, `rw [h]`, R5, R6, R7. -/
theorem pellAux_shift (n k : Nat) : pellAux n (pell k) (pell (k + 1)) = pell (k + n) := by
  induction n generalizing k with
    | zero => rfl
    | succ n ih =>
      have h : 2 * pell (k + 1) + pell k = pell (k + 1 + 1) := rfl
      simp only [pellAux]
      rw [h, ih (k + 1)]
      congr 1
      omega

/-! ### W2. The succ case on its own, one step per line, to read every state -/
example (n k : Nat) (ih : ∀ (k : Nat), pellAux n (pell k) (pell (k + 1)) = pell (k + n)) :
    pellAux (n + 1) (pell k) (pell (k + 1)) = pell (k + (n + 1)) := by
  have h : 2 * pell (k + 1) + pell k = pell (k + 1 + 1) := rfl
  simp only [pellAux]
  rw [h]
  rw [ih (k + 1)]
  congr 1
  omega

end M026Guide
