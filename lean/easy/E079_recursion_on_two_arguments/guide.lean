/- Guide for E079 (Recursion on two arguments).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries split `n` with `induction n with | … => ?_` so that both cases show up as goals in the
infoview; in the exercise each arm may hold its proof directly.
Part W: worked combinations on the guide's own two-argument function `g`, not on the exercise's `ack`.
Assumed: Lean basics (E001–E033), in particular `simp` (E010), `omega` (E011) and
`induction` on `Nat` (E014).
-/

namespace E079Guide

/-! `g` recurses on two arguments, like the exercise's function, but with other base values.
`termination_by m n => (m, n)` states the measure: the pair `(m, n)`, compared lexicographically
(first by `m`, then by `n`). The call `g m 2` lowers `m`; the inner call `g (m + 1) n` keeps `m + 1`
and lowers `n`; the outer call `g m (…)` lowers `m`, whatever its second argument. Without the
`termination_by` line Lean finds the same measure by itself.
Lean generates one equation lemma per pattern:
  `g.eq_1 : ∀ (x : Nat), g 0 x = x + 3`
  `g.eq_2 : ∀ (m : Nat), g m.succ 0 = g m 2`
  `g.eq_3 : ∀ (m n : Nat), g m.succ n.succ = g m (g (m + 1) n)` -/
def g : Nat → Nat → Nat
  | 0, n => n + 3
  | m + 1, 0 => g m 2
  | m + 1, n + 1 => g m (g (m + 1) n)
termination_by m n => (m, n)

/-! # Part R · Reference entries -/

/-! ## Closed computations -/

/-! ### R1. `simp [f]` · closes `f a b = v` for numerals `a b v`
`simp` rewrites with all equation lemmas of `f`, again and again, until only numerals are left.
A literal such as `2` matches the pattern `m + 1` (with `m := 1`). -/
example : g 1 2 = 11 := by
  simp [g]

/-! ### R2. `rw [f]` · goal: ONE equation of `f` is used, once
`rw [g]` picks the equation whose pattern matches the first `g …` it finds; here `g.eq_3`. -/
example (m n : Nat) (P : Nat → Prop) (h : P (g m (g (m + 1) n))) : P (g (m + 1) (n + 1)) := by
  rw [g]
  exact h

/-! ## Induction on the second argument -/

/-! ### R3. `induction n with | zero => … | succ k ih => …` · goal list: two goals; context gains `k`, `ih`
The `succ` case names the predecessor `k` and the induction hypothesis `ih : P k`. -/
example (P : Nat → Prop) (h0 : P 0) (hs : ∀ k, P k → P (k + 1)) (n : Nat) : P n := by
  induction n with | zero => ?_ | succ k ih => ?_
  · exact h0
  · exact hs k ih

/-! ### R4. `simp only [f, ih]` · goal: unfold `f`, rewrite with `ih`, unfold again
`g 1 (k + 1)` → `g 0 (g 1 k)` (equation 3) → `g 0 c` (`ih`) → `c + 3` (equation 1). `simp` repeats
until nothing applies, so the order of the names does not matter. -/
example (k c : Nat) (ih : g 1 k = c) (P : Nat → Prop) (h : P (c + 3)) : P (g 1 (k + 1)) := by
  simp only [g, ih]
  exact h

/-! ### R5. `simp only [thm]` with `thm : ∀ x, f x = e x` · goal: every `f y` → `e y`
`simp` chooses `x := y` itself. A theorem proved earlier in the file is used the same way, by its
name; here a hypothesis `hf` plays that theorem. -/
example (hf : ∀ x, g 1 x = 3 * x + 5) (y : Nat) (P : Nat → Prop) (h : P (3 * y + 5)) :
    P (g 1 y) := by
  simp only [hf]
  exact h

/-! ### R6. `omega` · closes a linear (in)equality over `Nat` or `Int`
Linear: built from variables, numerals, `+`, `-`, and multiplication by a numeral. -/
example (k : Nat) : 3 * k + 5 + 3 = 3 * (k + 1) + 5 := by
  omega

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A closed form for `g 1`, one step at a time: R3, R1, then R2, `rw [ih]`, R2, R6
After the first `rw [g]` the literal `1` is printed `0 + 1`: Lean matched `1` against `m + 1`.
`rw [ih]` still finds `g (0 + 1) k`, since `0 + 1` and `1` are the same number. -/
theorem g_one (n : Nat) : g 1 n = 3 * n + 5 := by
  induction n with
    | zero => ?_
    | succ k ih => ?_
  · simp [g]
  rw [g]
  rw [ih]
  rw [g]
  omega

/-! ### W2. The same with one `simp` in the step (R4); `simp` stops at arithmetic, `omega` ends it -/
example (n : Nat) : g 1 n = 3 * n + 5 := by
  induction n with
    | zero => simp [g]
    | succ k ih => simp [g, ih]; omega

/-! ### W3. One level up: unfold `g 2 (n + 1)`, then the earlier theorem `g_one` (R5), then R6 -/
example (n : Nat) : g 2 (n + 1) = 3 * (g 2 n + 1) + 2 := by
  simp [g, g_one]
  omega

end E079Guide
