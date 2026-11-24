/- Guide for M028 (Integer square root).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h…` in an entry is only there to finish the example; it shows what the goal became.
The case alternatives in R4 are written `| zero => ?_ | succ n ih => ?_` so that every case stays
open as a goal you can inspect; in the exercise you write tactics after `=>` instead.
The entries use the guide's own functions, which are NOT the exercise's:
  `tri n`     the triangular number 0 + 1 + … + n (R1);
  `sqPlus n`  (n + 1)² + (n + 1), written with a `let` (R2);
  `div3 n`    ⌊n / 3⌋, computed by counting up one step at a time (R3, R5, R6, W1).
Part W: worked combinations on `div3` and on squares of `a + 2`.
Assumed: Lean basics (E001–E033). Core Lean only: no Mathlib.
-/

namespace M028Guide

/-! # Part R · Reference entries -/

/-! ## Writing the function -/

/-! ### R1. `match n with | 0 => … | n + 1 => … f n …` · term: structural recursion on `Nat`
The arm `n + 1` may call the function on `n`: the argument shrinks, so Lean accepts the recursion
without a termination proof. Each arm becomes one equation that `simp [f]` / `simp only [f]` uses. -/
def tri (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => tri n + (n + 1)

example : tri 4 = 10 := rfl

/-! ### R2. `let x := e; body` · term: name a value once, use it several times
Inside a `def` write the `let` on its own line, the body below it at the same indentation. Lean
computes `e` once; in proofs `simp only [f]` substitutes `e` for `x` (R6). -/
def sqPlus (n : Nat) : Nat :=
  let m := n + 1
  m * m + m

example : sqPlus 2 = 12 := rfl

/-! ### R3. `if c then a else b` · term: choose by a decidable condition
`c` is a `Prop` that Lean can decide, such as `x ≤ y` or `x = y` on `Nat`. Combined with R1 and R2:
`div3` adds one to the previous quotient exactly when `3 * (q + 1)` still fits under `n + 1`. -/
def div3 (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 =>
    let q := div3 n
    if 3 * (q + 1) ≤ n + 1 then q + 1 else q

example : div3 7 = 2 ∧ div3 9 = 3 := ⟨rfl, rfl⟩

/-! ## Induction and unfolding -/

/-! ### R4. `induction n with | zero => ?_ | succ n ih => ?_` · goal list: cases `0` and `n + 1`;
context gains `ih`, the statement at `n` -/
example (P : Nat → Prop) (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) (n : Nat) : P n := by
  induction n with | zero => ?_ | succ n ih => ?_
  · exact h0
  · exact hs n ih

/-! ### R5. `simp [f]` · closes the base case: `f 0` evaluates by the `0` arm, then arithmetic -/
example : div3 0 * 3 ≤ 0 ∧ 0 < (div3 0 + 1) * 3 := by
  simp [div3]

/-! ### R6. `simp only [f]` · goal: `f (n + 1)` → the `n + 1` arm, with the `let` substituted
The `let q := div3 n` disappears: every `q` becomes `div3 n`. -/
example (n : Nat) (P : Nat → Prop)
    (h : P (if 3 * (div3 n + 1) ≤ n + 1 then div3 n + 1 else div3 n)) : P (div3 (n + 1)) := by
  simp only [div3]
  exact h

/-! ### R7. `split` · goal list: an `if c then a else b` in the goal → two goals
The first goal has `a` and a nameless hypothesis `h✝ : c`; the second has `b` and `h✝ : ¬c`. -/
example {α : Type} (c : Prop) [Decidable c] (a b : α) (P : α → Prop) (ha : c → P a)
    (hb : ¬c → P b) : P (if c then a else b) := by
  split
  · exact ha ‹c›
  · exact hb ‹¬c›

/-! ### R8. `rename_i h` · context: the newest nameless hypothesis `h✝` → `h`
A name with `✝` cannot be typed; `rename_i` gives it a name you can use. It acts on the first
open goal; here the two goals are worked one after the other (in the exercise, put it after `·`). -/
example (c : Prop) [Decidable c] (n : Nat) (P : Nat → Prop) (hp : c → P (n + 1)) :
    P (if c then n + 1 else n) ∨ ¬c := by
  split
  rename_i h
  exact Or.inl (hp h)
  rename_i h
  exact Or.inr h

/-! ### R9. `refine ⟨h, ?_⟩` · goal `A ∧ B` with `h : A` in the context → goal `B` -/
example (A B : Prop) (h : A) (hb : B) : A ∧ B := by
  refine ⟨h, ?_⟩
  exact hb

/-! ## Expanding products for `omega` -/

/-! ### R10. `Nat.add_mul` · `(a + b) * c = a * c + b * c` · goal: distribute a sum on the left -/
example (a b c : Nat) (P : Nat → Prop) (h : P (a * c + b * c)) : P ((a + b) * c) := by
  rw [Nat.add_mul]
  exact h

/-! ### R11. `Nat.mul_add` · `a * (b + c) = a * b + a * c` · goal: distribute a sum on the right -/
example (a b c : Nat) (P : Nat → Prop) (h : P (a * b + a * c)) : P (a * (b + c)) := by
  rw [Nat.mul_add]
  exact h

/-! ### R12. `simp only [Nat.add_mul, Nat.mul_add] at h ⊢` · context and goal: every product of
sums expanded, in `h` and in the goal
`simp only` repeats R10 and R11 until no product of a sum is left. It leaves `1 * a` and `a * 2` as
they are: `omega` reads those. List several hypotheses before `⊢` (`at ih h ⊢`). -/
example (a m : Nat) (P : Nat → Prop) (h : (a + 2) * (a + 2) ≤ m) (hp : ∀ k, k ≤ m → P k) :
    P (a * (a + 1)) := by
  simp only [Nat.add_mul, Nat.mul_add] at h ⊢
  exact hp _ (by omega)

/-! ### R13. `omega` · closes linear arithmetic over `Nat`, treating `a * a` as one unknown
`omega` knows `+`, `-`, `*` by a numeral, `<`, `≤`, `=`, `∧`, `∨`, `¬` and uses the hypotheses. A
product of two variables, such as `a * a`, is one opaque number to it. `(a + 1) * (a + 1)` is a
DIFFERENT opaque number, unrelated to `a * a`: expand first (R12). -/
example (a m : Nat) (h1 : a * a + 1 * a + (a * 1 + 1 * 1) ≤ m) (h2 : m < a * a + 3) : a = 0 := by
  omega

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `3 * div3 n ≤ n`: R4, R5, R6, R7, R8, R13 -/
example (n : Nat) : 3 * div3 n ≤ n := by
  induction n with
    | zero => simp [div3]
    | succ n ih =>
      simp only [div3]
      split
      · rename_i h
        omega
      · omega

/-! ### W2. A square of a sum against a bound: expand only `h` (R12), then R13 -/
example (a m : Nat) (h : (a + 2) * (a + 2) ≤ m) : a * a + 4 * a + 4 ≤ m := by
  simp only [Nat.add_mul, Nat.mul_add] at h
  omega

end M028Guide
