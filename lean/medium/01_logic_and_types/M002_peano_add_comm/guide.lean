/- Guide for M002 (Peano addition is commutative).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on the toy function `plus2 n m` ("n + 2·m") below, which is NOT the
exercise's `add`.
Assumed: Lean basics (E001–E033). Core Lean only: no Mathlib.
-/

namespace M002Guide

/-! ## Toy objects used by the entries (not the exercise's) -/

/-- Unary naturals, built the same way as the exercise's type: `zero` and `succ`. -/
inductive U where
  | zero : U
  | succ (n : U) : U

/-- `plus2 n m` is "n + 2·m". Like the exercise's `add`, it recurses on its SECOND argument, so
`plus2 n .zero` and `plus2 n (.succ m)` unfold by computation, `plus2 .zero n` does not. -/
def plus2 : U → U → U
  | n, .zero => n
  | n, .succ m => .succ (.succ (plus2 n m))

/-! # Part R · Reference entries -/

/-! ## Induction on your own inductive type -/

/-! ### R1. `induction n with | zero => … | succ n ih => …` · goal list: `zero` and `succ`;
context: `ih` in the `succ` case
One goal per constructor of `U`. In `succ` the induction hypothesis `ih` is the statement for `n`,
and the goal is the statement for `n.succ` (Lean prints `U.succ n` as `n.succ`). -/
example (P : U → Prop) (h0 : P .zero) (hs : ∀ n, P n → P (.succ n)) (n : U) : P n := by
  induction n
  exact h0
  apply hs
  assumption

/-- R1 with `with`: the `succ` case's variable and hypothesis get the names `n` and `ih`. Each `|`
alternative is the tactic block for that goal; in your own file the `|` lines may sit at the same
column as `induction` (as is usual) or further right. -/
example (P : U → Prop) (h0 : P .zero) (hs : ∀ n, P n → P (.succ n)) (n : U) : P n := by
  induction n with
    | zero => exact h0
    | succ n ih => exact hs n ih

/-! ## Unfolding by computation -/

/-! ### R2. `rfl` · closes an equation whose two sides compute to the same term
`plus2 n .zero` is literally the first equation of `plus2`, so both sides reduce to `n`. The same
works under other calls: `plus2 (plus2 a b) .zero` reduces to `plus2 a b`. -/
example (n : U) : plus2 n .zero = n := by
  rfl

/-! ### R3. `simp only [f]` · goal: `f n (.succ m)` → the right side of that equation of `f`
Each `| pattern => body` line of a `def` is one equation. `simp only [plus2]` rewrites wherever the
SECOND argument is literally `.zero` or `.succ _`; with an unknown second argument it does nothing. -/
example (n m : U) (P : U → Prop) (h : P (.succ (.succ (plus2 n m)))) : P (plus2 n (.succ m)) := by
  simp only [plus2]
  exact h

/-! ### R4. `U.succ.injEq` · `(U.succ a = U.succ b) = (a = b)` · goal: peel `succ` off both sides
Lean generates this lemma for every constructor (constructors are injective). `simp` applies it by
itself, so after unfolding, a goal `x.succ = y.succ` becomes `x = y`. -/
example (a b : U) (h : a = b) : U.succ a = U.succ b := by
  simp only [U.succ.injEq]
  exact h

/-! ## Using equations: the induction hypothesis and helper lemmas -/

/-! ### R5. `rw [ih]` with `ih : l = r` · goal: every `l` → `r`
`l` must appear literally in the goal. `rw` tries `rfl` afterwards, so it may close the goal. -/
example (l r : U) (ih : l = r) (P : U → Prop) (h : P (.succ r)) : P (.succ l) := by
  rw [ih]
  exact h

/-! ### R6. `rw [lem]` with `lem : ∀ x y, f x y = g x y` · goal: `lem` instantiated at the
first match, then rewritten
A helper lemma is a `theorem` you state yourself, outside the spec regions and ABOVE the theorem that
uses it; `rw` or `simp` then fills in its `∀` arguments by matching. `rw [← lem]` rewrites right to
left. -/
example (f g : U → U → U) (lem : ∀ x y, f (.succ x) y = g x y) (a b : U) (P : U → Prop)
    (h : P (g a b)) : P (f (.succ a) b) := by
  rw [lem]
  exact h

/-! ### R7. `simp [f, ih]` / `simp [f, lem]` · closes: unfold `f` (R3), peel constructors (R4) and
rewrite with the equations given (R5, R6), until both sides agree
The usual way to finish an induction step in one line. `simp` also handles an `ih` such as
`f a b = f b a` without looping: it rewrites with it only when that makes the term smaller in a fixed
order. -/
example (a m : U) (ih : plus2 a m = m) :
    plus2 a (.succ m) = U.succ (U.succ m) := by
  simp [plus2, ih]

/-! # Part W · Worked combinations (on `plus2`, not the exercise's `add`) -/

/-! ### W1. A helper lemma: `succ` on the FIRST argument moves out
Induct on the argument `plus2` recurses on (the second): R1, then R2 for `zero`, R7 for `succ`. -/
theorem succ_plus2 (a b : U) : plus2 (.succ a) b = .succ (plus2 a b) := by
  induction b with
    | zero => rfl
    | succ b ih => simp [plus2, ih]

/-! ### W2. The induction step that is stuck without the helper
Goal: `plus2 (plus2 a b) c = plus2 (plus2 a c) b` ("a + 2b + 2c" both ways), by induction on `c`.
Here is its `succ` step on its own. After R3 the right side is `plus2 (plus2 a c).succ.succ b`: a
`succ` on the FIRST argument, which no equation of `plus2` unfolds. W1 moves it out (R6, twice);
then the goal is `ih` under two `succ`s (R5). -/
example (a b c : U) (ih : plus2 (plus2 a b) c = plus2 (plus2 a c) b) :
    plus2 (plus2 a b) (.succ c) = plus2 (plus2 a (.succ c)) b := by
  simp only [plus2]
  rw [succ_plus2, succ_plus2]
  rw [ih]

/-! ### W3. The whole proof: R1, R2 for `zero`, one `simp` with the definition, the helper and the
IH for `succ` (R7) -/
theorem plus2_swap (a b c : U) : plus2 (plus2 a b) c = plus2 (plus2 a c) b := by
  induction c with
    | zero => rfl
    | succ c ih => simp [plus2, succ_plus2, ih]

end M002Guide
