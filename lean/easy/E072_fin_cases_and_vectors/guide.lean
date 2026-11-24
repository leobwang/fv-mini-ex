/- Guide for E072 (fin_cases and vectors).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`exacts [h0, h1, h2]` closes the open goals in order with those terms.
Part W: worked combinations on objects that are NOT the exercise's (another vector, `ZMod 2`).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace E072Guide

/-! # Part R · Reference entries -/

/-! ## Vectors and case splits on `Fin n` -/

/-! ### R1. `![a, b, c]` and `rfl` · closes `![a, b, c] i = x` when `x` is entry `i`
`![a, b, c]` is the function `Fin 3 → α` with `0 ↦ a`, `1 ↦ b`, `2 ↦ c` (Mathlib's vector literal,
`Matrix.vecCons`). Lean computes an entry by unfolding, so `rfl` closes the goal. -/
example {α : Type} (a b c : α) : ![a, b, c] 2 = c := by
  rfl

/-! ### R2. `fin_cases i` · context loses `i : Fin 3`; goal → one goal per value of `i`
`(fun i => i) ⟨0, ⋯⟩` is how Lean prints the index `0`: `⟨k, ⋯⟩` is `k` packed with its proof `k < 3`. -/
example (P : Fin 3 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (i : Fin 3) : P i := by
  fin_cases i
  exacts [h0, h1, h2]

/-! ## Evaluating one case with `simp` -/

/-! ### R3. Unfold a definition: `simp only [D]` · goal: the name `D` → its body
`simp [D, …]` does the same and keeps simplifying. -/
def g : Fin 3 → ℕ := ![2, 4, 6]
example (P : (Fin 3 → ℕ) → Prop) (h : P ![2, 4, 6]) : P g := by
  simp only [g]
  exact h

/-! ### R4. `simp` (`Fin.reduceFinMk`, `Fin.isValue`) · goal: the printed index `(fun i => i) ⟨2, ⋯⟩` → `2`
`simp` beta-reduces `(fun i => i) x` to `x`, then a *simproc* (a built-in `simp` procedure that computes
instead of rewriting with a stated lemma) turns `⟨2, ⋯⟩` into the numeral `2`. For `0` and `1` the
lemmas `Fin.zero_eta` and `Fin.mk_one` do it. -/
example (P : Fin 3 → Prop) (h : P 2) : P ((fun i => i) ⟨2, by norm_num⟩) := by
  simp
  exact h

/-! ### R5. `simp` (`Matrix.cons_val_zero`, `Matrix.cons_val_one`, …) · goal: `![a, b, c] 2` → `c` -/
example {α : Type} (a b c : α) (P : α → Prop) (h : P c) : P (![a, b, c] 2) := by
  simp
  exact h

/-! ### R6. `simp` · closes a comparison of `ℕ` numerals (`≥`, `<`, `^`, `+`, `*`) -/
example : (9 : ℕ) ≥ 5 := by
  simp

example : (3 : ℕ) ^ 2 < 10 := by
  simp

/-! ## Using a hypothesis -/

/-! ### R7. `simp [D] at h` · context: `h` is simplified; if `h` becomes `False`, the goal is closed -/
example (n : ℕ) (P : ℕ → Prop) (h : g 1 = n) (hp : P 4) : P n := by
  simp [g] at h
  exact h ▸ hp

example (G : Prop) (h : g 0 = 4) : G := by
  simp [g] at h

/-! ### R8. `simp_all [D]` · simplifies every hypothesis and the goal, each with the others; closes -/
example (n : ℕ) (P : ℕ → Prop) (h : g 1 = n) (hp : P 4) : P n := by
  simp_all [g]

/-! ## Casts `Fin n → ℕ` -/

/-! ### R9. `simp` (projection, as in `Fin.val_mk`) · goal: `↑((fun i => i) ⟨3, ⋯⟩)` → `3`
`↑i` is `Fin.val i : ℕ`, the number behind `i : Fin n`; `(i : ℕ)` in a statement prints as `↑i`.
`Fin.val ⟨k, h⟩` reduces to `k` by definition (stated as `Fin.val_mk`); `simp` does this by itself. -/
example (P : ℕ → Prop) (h : P 3) : P (((fun i => i) ⟨3, by norm_num⟩ : Fin 4) : ℕ) := by
  simp
  exact h

/-! ## `ZMod n`: integers modulo `n` -/

/-! ### R10. `fin_cases x` for `x : ZMod 3` · goal → one goal per residue `0, 1, 2`
For `n ≥ 1`, `ZMod n` is defined as `Fin n`, so `fin_cases` lists its elements. -/
example (P : ZMod 3 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (x : ZMod 3) : P x := by
  fin_cases x
  exacts [h0, h1, h2]

/-! ### R11. `rfl` · closes an equation of closed `ZMod n` arithmetic: Lean computes both sides
`3 * 4 = 12 = 2 + 2 * 5`, so `(3 : ZMod 5) * 4 = 2`. `simp` does not compute this (Traps). -/
example : (3 : ZMod 5) * 4 = 2 := by
  rfl

example : (fun i => i) (⟨4, by norm_num⟩ : Fin 5) + 1 = (0 : ZMod 5) := by
  rfl

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `fin_cases` + `simp [name]`: R2, then R3–R6 in each case -/
example (i : Fin 3) : g i ≤ 6 := by
  fin_cases i
  all_goals simp [g]

/-! ### W2. A hypothesis that is false in all cases but one: R2, then R8 -/
example (i : Fin 3) (h : g i = 6) : (i : ℕ) = 2 := by
  fin_cases i
  all_goals simp_all [g]

/-! ### W3. A cast to `ℕ`: R2, then R9 and R6 in one `simp` -/
example (i : Fin 3) : (i : ℕ) * 3 < 7 := by
  fin_cases i
  all_goals simp

/-! ### W4. A polynomial identity in `ZMod 2`: R10, then R11 -/
example (x : ZMod 2) : x * (x + 1) = 0 := by
  fin_cases x
  all_goals rfl

end E072Guide
