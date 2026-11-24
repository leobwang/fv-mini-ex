/- Guide for H059 (Convergence of a 2-state chain).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other matrices, the sequence `(1/2)ⁿ`).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Filter Topology

namespace H059Guide

/-! # Part R · Reference entries -/

/-! ## Matrix equations → entries (MILESTONES 1 and 2) -/

/-! ### R1. `ext i j` (lemma `Matrix.ext`) · goal `M = N` → context gains `i j`, goal is one entry -/
example {α : Type} (M N : Matrix (Fin 2) (Fin 2) α) (h : ∀ i j, M i j = N i j) : M = N := by
  ext i j
  exact h i j

/-! ### R2. `fin_cases i` · context loses `i : Fin 2`; goal → one goal per value of `i`
`(fun i => i) ⟨0, ⋯⟩` is how Lean prints the index `0`. -/
example (P : Fin 2 → Prop) (h0 : P 0) (h1 : P 1) (i : Fin 2) : P i := by
  fin_cases i
  exact h0
  exact h1

/-! ### R3. Unfold a definition with parameters: `simp only [Q]` · goal: `Q c` → its body at `c` -/
def Q (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![c, 1; 0, c]
example (c : ℝ) (P : Matrix (Fin 2) (Fin 2) ℝ → Prop) (h : P !![c, 1; 0, c]) : P (Q c) := by
  simp only [Q]
  exact h

/-! ### R4. Entry of a literal `!![a, b; c, d] i j` (`Matrix.of_apply`, `Matrix.cons_val_…`) · goal -/
example {α : Type} (a b c d : α) (P : α → Prop) (h : P c) : P (!![a, b; c, d] 1 0) := by
  simp
  exact h

/-! ### R5. `Matrix.mul_apply` · goal: entry of a product → a sum over the middle index -/
example {α : Type} [Mul α] [AddCommMonoid α] (M N : Matrix (Fin 2) (Fin 2) α) (i k : Fin 2)
    (P : α → Prop) (h : P (∑ j, M i j * N j k)) : P ((M * N) i k) := by
  rw [Matrix.mul_apply]
  exact h

/-! ### R6. `Fin.sum_univ_two` · goal: a sum over `Fin 2` → two terms -/
example {β : Type} [AddCommMonoid β] (f : Fin 2 → β) (P : β → Prop) (h : P (f 0 + f 1)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ### R7. `field_simp` · goal: an equation with denominators → one without
It needs each denominator `≠ 0` in the context (here `hc`). -/
example (x y c : ℝ) (hc : c ≠ 0) (h : x * c + y = x * c) : x + y / c = x := by
  field_simp
  exact h

/-! ### R8. `ring` · closes an identity of commutative rings (no hypotheses used) -/
example (x y : ℝ) : x * (1 - y + y) = x := by
  ring

/-! ### R9. `mul_sub` · `a * (b - c) = a * b - a * c` · goal: distribute `*` over `-` -/
example {α : Type} [Ring α] (a b c : α) (P : α → Prop) (h : P (a * b - a * c)) : P (a * (b - c)) := by
  rw [mul_sub]
  exact h

/-! ### R10. `mul_one` · `a * 1 = a` · goal -/
example {α : Type} [Ring α] (a : α) (P : α → Prop) (h : P a) : P (a * 1) := by
  rw [mul_one]
  exact h

/-! ### R11. `Matrix.sub_apply` · goal: entry of `M - N` → difference of the entries -/
example (M N : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) (P : ℝ → Prop) (h : P (M i j - N i j)) :
    P ((M - N) i j) := by
  rw [Matrix.sub_apply]
  exact h

/-! ### R12. `Matrix.one_apply_eq`, `Matrix.one_apply_ne` · goal: entries of the identity `1` -/
example (P : ℝ → Prop) (h1 : P 1) (h0 : P 0) :
    P ((1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0) ∧ P ((1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1) := by
  simp
  exact ⟨h1, h0⟩

/-! ### R13. `Matrix.smul_apply`, `smul_eq_mul` · goal: entry of `s • M` → `s * (entry of M)` -/
example (s : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) (P : ℝ → Prop) (h : P (s * M i j)) :
    P ((s • M) i j) := by
  rw [Matrix.smul_apply]
  rw [smul_eq_mul]
  exact h

/-! ## Absolute value (MILESTONE 3) -/

/-! ### R14. `abs_lt` · `|a| < b ↔ -b < a ∧ a < b` · goal -/
example (x r : ℝ) (h : -r < x ∧ x < r) : |x| < r := by
  rw [abs_lt]
  exact h

/-! ### R15. `linarith` · closes a linear (in)equality that follows from the hypotheses -/
example (x y : ℝ) (h : 0 < x + y) : 1 - x - y < 1 := by
  linarith

/-! ## Matrix powers by induction (`pow_formula`) -/

/-! ### R16. `induction n with` · goal list: `P n` → `P 0` and `P (n + 1)` with `ih : P n`
`?_` leaves the `succ` goal open, so the next line works on it. -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) (n : ℕ) : P n := by
  induction n with
    | zero => exact h0
    | succ n ih => ?_
  exact hs n ih

/-! ### R17. `pow_zero` · `a ^ 0 = 1` · goal (`simp` uses it by itself) -/
example (A : Matrix (Fin 2) (Fin 2) ℝ) (P : Matrix (Fin 2) (Fin 2) ℝ → Prop) (h : P 1) :
    P (A ^ 0) := by
  rw [pow_zero]
  exact h

/-! ### R18. `one_smul` · `1 • M = M` · goal (`simp` uses it by itself) -/
example (M : Matrix (Fin 2) (Fin 2) ℝ) (P : Matrix (Fin 2) (Fin 2) ℝ → Prop) (h : P M) :
    P ((1 : ℝ) • M) := by
  rw [one_smul]
  exact h

/-! ### R19. `add_sub_cancel` · `a + (b - a) = b` · goal (`simp` uses it by itself) -/
example {α : Type} [AddCommGroup α] (a b : α) (P : α → Prop) (h : P b) : P (a + (b - a)) := by
  rw [add_sub_cancel]
  exact h

/-! ### R20. `pow_succ'` · `a ^ (n + 1) = a * a ^ n` · goal: peel one factor off on the LEFT -/
example (A : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) (P : Matrix (Fin 2) (Fin 2) ℝ → Prop)
    (h : P (A * A ^ n)) : P (A ^ (n + 1)) := by
  rw [pow_succ']
  exact h

/-! ### R21. `mul_add` · `a * (b + c) = a * b + a * c` · goal -/
example {α : Type} [Ring α] (a b c : α) (P : α → Prop) (h : P (a * b + a * c)) : P (a * (b + c)) := by
  rw [mul_add]
  exact h

/-! ### R22. `mul_smul_comm` · `A * s • B = s • (A * B)` · goal: move a scalar out of a product -/
example (s : ℝ) (A B : Matrix (Fin 2) (Fin 2) ℝ) (P : Matrix (Fin 2) (Fin 2) ℝ → Prop)
    (h : P (s • (A * B))) : P (A * s • B) := by
  rw [mul_smul_comm]
  exact h

/-! ### R23. `smul_smul` · `r • s • M = (r * s) • M` · goal: merge two scalars -/
example (r s : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) (P : Matrix (Fin 2) (Fin 2) ℝ → Prop)
    (h : P ((r * s) • M)) : P (r • s • M) := by
  rw [smul_smul]
  exact h

/-! ### R24. `pow_succ` · `a ^ (n + 1) = a ^ n * a` · goal: one factor on the RIGHT
Used right to left (`rw [← pow_succ]`) it folds `r ^ n * r` into `r ^ (n + 1)`. -/
example (r : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (r ^ n * r)) : P (r ^ (n + 1)) := by
  rw [pow_succ]
  exact h

/-! ## Limits (`converges`) -/

/-! ### R25. `tendsto_pow_atTop_nhds_zero_of_abs_lt_one` · `|r| < 1 → rⁿ → 0` · context gains it -/
example (r : ℝ) (hr : |r| < 1) (G : Prop) (g : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) → G) : G := by
  have h0 := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr
  exact g h0

/-! ### R26. `hx.ne'` (`LT.lt.ne'`) · from `hx : 0 < x` get `x ≠ 0` · context -/
example (x : ℝ) (hx : 0 < x) (G : Prop) (g : x ≠ 0 → G) : G := by
  have hne : x ≠ 0 := hx.ne'
  exact g hne

/-! ### R27. `simp_rw [h]` · goal: rewrite UNDER `fun n => …` (plain `rw` cannot) -/
example (A B : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (hAB : ∀ n, A n = B n) (i j : Fin 2)
    (P : (ℕ → ℝ) → Prop) (h : P (fun n => B n i j)) : P (fun n => A n i j) := by
  simp_rw [hAB]
  exact h

/-! ### R28. `Matrix.add_apply` · goal: entry of `M + N` → sum of the entries -/
example (M N : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) (P : ℝ → Prop) (h : P (M i j + N i j)) :
    P ((M + N) i j) := by
  rw [Matrix.add_apply]
  exact h

/-! ### R29. `tendsto_const_nhds` · a constant sequence tends to its value · context gains it -/
example (c : ℝ) (G : Prop) (g : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) → G) : G := by
  have hc : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
  exact g hc

/-! ### R30. `Filter.Tendsto.add` · `f → x`, `g → y` ⟹ `f + g → x + y` · context -/
example (f g : ℕ → ℝ) (x y : ℝ) (hf : Tendsto f atTop (𝓝 x)) (hg : Tendsto g atTop (𝓝 y))
    (G : Prop) (k : Tendsto (fun n => f n + g n) atTop (𝓝 (x + y)) → G) : G := by
  have h := hf.add hg
  exact k h

/-! ### R31. `Filter.Tendsto.mul` · `f → x`, `g → y` ⟹ `f * g → x * y` · context -/
example (f g : ℕ → ℝ) (x y : ℝ) (hf : Tendsto f atTop (𝓝 x)) (hg : Tendsto g atTop (𝓝 y))
    (G : Prop) (k : Tendsto (fun n => f n * g n) atTop (𝓝 (x * y)) → G) : G := by
  have h := hf.mul hg
  exact k h

/-! ### R32. `rw [zero_mul, add_zero] at h` · context: rewrite a hypothesis, not the goal -/
example (f : ℕ → ℝ) (x y : ℝ) (h : Tendsto f atTop (𝓝 (x + 0 * y))) : Tendsto f atTop (𝓝 x) := by
  rw [zero_mul, add_zero] at h
  exact h

/-! ### R33. `convert h using 2` · goal: close it with `h` up to the parts that differ → those equations
`using 2` lets `convert` look two levels deep: past `Tendsto f atTop` and past `𝓝`. -/
example (f : ℕ → ℝ) (x y : ℝ) (h : Tendsto f atTop (𝓝 y)) (hxy : x - y = 0) :
    Tendsto f atTop (𝓝 x) := by
  convert h using 2
  linarith

/-! ### R34. Entry of a vector literal `![x, y] i` (`Matrix.cons_val_…`) · goal (`simp` does it) -/
example {α : Type} (x y : α) (P : α → Prop) (h : P y) : P (![x, y] 1) := by
  simp
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Entry-by-entry matrix identity with a denominator: R1, R2, R3, R5, R6, then R7 -/
def S (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![c, 0; 0, c]
example (c : ℝ) (hc : c ≠ 0) : S c * !![1 / c, 0; 0, 1 / c] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [S, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp

/-! ### W2. A power identity by induction: R16, R17, R20, then `mul_assoc` and the hypotheses -/
example (A E : Matrix (Fin 2) (Fin 2) ℝ) (hA : A * E = E) (n : ℕ) : A ^ n * E = E := by
  induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_assoc, ih, hA]

/-! ### W3. A limit `c + (1/2)ⁿ · d → c`: R14, R25, R29, R30, R31, R32 -/
example (c d : ℝ) : Tendsto (fun n : ℕ => c + (1 / 2 : ℝ) ^ n * d) atTop (𝓝 c) := by
  have hr : |(1 / 2 : ℝ)| < 1 := by
    rw [abs_lt]
    constructor <;> norm_num
  have h0 := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr
  have h := (tendsto_const_nhds (x := c)).add (h0.mul (tendsto_const_nhds (x := d)))
  rw [zero_mul, add_zero] at h
  exact h

end H059Guide
