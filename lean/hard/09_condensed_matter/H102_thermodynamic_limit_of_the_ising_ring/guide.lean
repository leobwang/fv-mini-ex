/- Guide for H102 (Thermodynamic limit of the Ising ring).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders, in the order the skeletons use them. Put the cursor before and after the step to see
the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
A goal `G` with a hypothesis `k : … → G` is an entry that changes the context: the new fact is `h`.
Part W: worked combinations on objects that are NOT the exercise's (other matrices, other limits).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Real Filter Topology

namespace H102Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · Powers of a 2×2 matrix (`trace_pow`) -/

/-! ### R1. `induction n with` · goal list: the case `0` and the step `n + 1` with `ih` for `n` -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) (n : ℕ) : P n := by
  induction n with
    | zero => exact h0
    | succ n ih => exact hs n ih

/-- The same split, unfolded so the infoview shows the two goals. `rename_i n ih` gives the new
variables the names `| succ n ih =>` would (otherwise they print as `n✝`, `a✝`). -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) (n : ℕ) : P n := by
  induction n
  case zero => exact h0
  rename_i n ih
  exact hs n ih

/-! ### R2. `pow_zero` · `x ^ 0 = 1` · goal (`simp` applies it by itself) -/
example {α : Type} [Monoid α] (x : α) (P : α → Prop) (h : P 1) : P (x ^ 0) := by
  rw [pow_zero]
  exact h

/-! ### R3. `Matrix.one_apply_eq`, `Matrix.one_apply_ne` · goal: entries of the identity matrix `1`
(`simp` applies them by itself) -/
example (P : ℝ → Prop) (h1 : P 1) (h0 : P 0) :
    P ((1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0) ∧ P ((1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1) := by
  simp
  exact ⟨h1, h0⟩

/-! ### R4. Entry of a literal `!![a, b; c, d] i j` (`Matrix.of_apply`, `Matrix.cons_val_…`) · goal
(`simp` applies them by itself) -/
example {α : Type} (a b c d : α) (P : α → Prop) (h : P b) : P (!![a, b; c, d] 0 1) := by
  simp
  exact h

/-! ### R5. `pow_succ` · `a ^ (n + 1) = a ^ n * a` · goal -/
example {α : Type} [Monoid α] (a : α) (n : ℕ) (P : α → Prop) (h : P (a ^ n * a)) :
    P (a ^ (n + 1)) := by
  rw [pow_succ]
  exact h

/-! ### R6. `Matrix.mul_apply` · goal: entry of a product → a sum over the middle index -/
example {α : Type} [Mul α] [AddCommMonoid α] (M N : Matrix (Fin 2) (Fin 2) α) (i k : Fin 2)
    (P : α → Prop) (h : P (∑ j, M i j * N j k)) : P ((M * N) i k) := by
  rw [Matrix.mul_apply]
  exact h

/-! ### R7. `Fin.sum_univ_two` · goal: a sum over `Fin 2` → two terms -/
example {β : Type} [AddCommMonoid β] (f : Fin 2 → β) (P : β → Prop) (h : P (f 0 + f 1)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ### R8. `Real.cosh_eq`, `Real.sinh_eq` · goal: `cosh x`, `sinh x` → exponentials -/
example (x : ℝ) (P : ℝ → ℝ → Prop) (h : P ((exp x + exp (-x)) / 2) ((exp x - exp (-x)) / 2)) :
    P (cosh x) (sinh x) := by
  rw [Real.cosh_eq]
  rw [Real.sinh_eq]
  exact h

/-! ### R9. `Matrix.trace`, `Matrix.diag_apply` · goal: the trace → the sum of the diagonal -/
example {α : Type} [AddCommMonoid α] (M : Matrix (Fin 2) (Fin 2) α) (P : α → Prop)
    (h : P (∑ i, M i i)) : P (Matrix.trace M) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  exact h

/-! ## Part 2 · The dominant eigenvalue (`abs_lam_minus_lt`) -/

/-! ### R10. `abs_mul` · `|a * b| = |a| * |b|` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (|a| * |b|)) : P |a * b| := by
  rw [abs_mul]
  exact h

/-! ### R11. `abs_two` · `|2| = 2` · goal -/
example (P : ℝ → Prop) (h : P 2) : P |2| := by
  rw [abs_two]
  exact h

/-! ### R12. `Real.cosh_sq` · `cosh x ^ 2 = sinh x ^ 2 + 1` · context gains it -/
example (x : ℝ) (G : Prop) (k : cosh x ^ 2 = sinh x ^ 2 + 1 → G) : G := by
  have h := Real.cosh_sq x
  exact k h

/-! ### R13. `Real.cosh_pos` · `0 < cosh x` · context gains it -/
example (x : ℝ) (G : Prop) (k : 0 < cosh x → G) : G := by
  have hc := Real.cosh_pos x
  exact k hc

/-! ### R14. `abs_nonneg`, `sq_abs` · `0 ≤ |a|` and `|a| ^ 2 = a ^ 2` · context gains them -/
example (a : ℝ) (G : Prop) (k : 0 ≤ |a| → |a| ^ 2 = a ^ 2 → G) : G := by
  have h1 := abs_nonneg a
  have h2 := sq_abs a
  exact k h1 h2

/-! ### R15. `nlinarith [t₁, t₂]` · closes a polynomial inequality; it adds the facts `tᵢ`, then
multiplies pairs of hypotheses together and searches for a linear combination -/
example (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) : a ^ 2 < b ^ 2 := by
  nlinarith [mul_self_nonneg (b - a)]

/-! ## Part 3 · The limit (`limit_lemma`) -/

/-! ### R16. `set r := e with hr` · context gains `r := e` and `hr : r = e`; goal: `e` → `r` -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (a / b)) : P (a / b) := by
  set r := a / b with hr
  exact h

/-! ### R17. `abs_div` · `|a / b| = |a| / |b|` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (|a| / |b|)) : P |a / b| := by
  rw [abs_div]
  exact h

/-! ### R18. `abs_of_pos` · `0 < a → |a| = a` · goal -/
example (a : ℝ) (ha : 0 < a) (P : ℝ → Prop) (h : P a) : P |a| := by
  rw [abs_of_pos ha]
  exact h

/-! ### R19. `div_lt_one` · `0 < b → (a / b < 1 ↔ a < b)` · goal -/
example (a b : ℝ) (hb : 0 < b) (h : a < b) : a / b < 1 := by
  rw [div_lt_one hb]
  exact h

/-! ### R20. `rcases N with _ | N` · goal list: the case `0` and the case `N + 1` -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ N, P (N + 1)) (N : ℕ) : P N := by
  rcases N with _ | N
  · exact h0
  · exact hs N

/-! ### R21. `pow_lt_one₀` · `0 ≤ a → a < 1 → n ≠ 0 → a ^ n < 1` · context gains it -/
example (a : ℝ) (n : ℕ) (h0 : 0 ≤ a) (h1 : a < 1) (hn : n ≠ 0) (G : Prop) (k : a ^ n < 1 → G) :
    G := by
  have h := pow_lt_one₀ h0 h1 hn
  exact k h

/-! ### R22. `omega` · closes linear goals over `ℕ` and `ℤ`, such as `n + 1 ≠ 0` -/
example (n : ℕ) : n + 1 ≠ 0 := by
  omega

/-! ### R23. `neg_abs_le` · `-|a| ≤ a` · context gains it -/
example (a : ℝ) (G : Prop) (k : -|a| ≤ a → G) : G := by
  have h := neg_abs_le a
  exact k h

/-! ### R24. `rw [abs_pow] at h` · `|a ^ n| = |a| ^ n` · context: `h` is rewritten -/
example (a : ℝ) (n : ℕ) (h : -|a ^ n| ≤ a ^ n) (G : Prop) (k : -|a| ^ n ≤ a ^ n → G) : G := by
  rw [abs_pow] at h
  exact k h

/-- The same lemma on the goal (without `at h`), so the infoview shows the rewrite. -/
example (a : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (|a| ^ n)) : P |a ^ n| := by
  rw [abs_pow]
  exact h

/-! ### R25. `linarith` · closes a linear (in)equality that follows from the hypotheses by adding
them up with nonnegative coefficients; nonlinear pieces such as `|a| ^ n` count as unknowns -/
example (x y : ℝ) (h1 : x < 1) (h2 : -x ≤ y) : 0 < 1 + y := by
  linarith

/-! ### R26. `div_pow` · `(a / b) ^ n = a ^ n / b ^ n` · goal -/
example (a b : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (a ^ n / b ^ n)) : P ((a / b) ^ n) := by
  rw [div_pow]
  exact h

/-! ### R27. `field_simp` · goal: multiplies out the denominators it can prove nonzero (from the
hypotheses, or numerals) and normalises; often closes the goal -/
example (a b : ℝ) (hb : b ≠ 0) (P : ℝ → Prop) (h : P (b + a)) : P (b * (1 + a / b)) := by
  field_simp
  exact h

/-! ### R28. `tendsto_pow_atTop_nhds_zero_of_abs_lt_one` · `|r| < 1 → rⁿ → 0` · context gains it -/
example (r : ℝ) (hr : |r| < 1) (G : Prop) (k : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) → G) :
    G := by
  have h := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr
  exact k h

/-! ### R29. `Filter.Tendsto.const_add` · from `f n → a` get `b + f n → b + a` · context -/
example (f : ℕ → ℝ) (a b : ℝ) (hf : Tendsto f atTop (𝓝 a)) (G : Prop)
    (k : Tendsto (fun n => b + f n) atTop (𝓝 (b + a)) → G) : G := by
  have h := hf.const_add b
  exact k h

/-! ### R30. `Filter.Tendsto.log` · from `f n → x` and `x ≠ 0` get `log (f n) → log x` · context -/
example (f : ℕ → ℝ) (x : ℝ) (hf : Tendsto f atTop (𝓝 x)) (hx : x ≠ 0) (G : Prop)
    (k : Tendsto (fun n => Real.log (f n)) atTop (𝓝 (Real.log x)) → G) : G := by
  have h := hf.log hx
  exact k h

/-! ### R31. `simpa using e` · closes the goal when `simp` brings the type of `e` and the goal to the
same form. Here it turns `log 1` into `0` -/
example (f : ℕ → ℝ) (h : Tendsto (fun n => Real.log (f n)) atTop (𝓝 (Real.log 1))) :
    Tendsto (fun n => Real.log (f n)) atTop (𝓝 0) := by
  simpa using h

/-! ### R32. `tendsto_natCast_atTop_atTop` · `(n : ℝ) → ∞` as `n → ∞` · context gains it -/
example (G : Prop) (k : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop → G) : G := by
  have h := tendsto_natCast_atTop_atTop (R := ℝ)
  exact k h

/-! ### R33. `Filter.Tendsto.div_atTop` · from `f n → a` and `g n → ∞` get `f n / g n → 0` · context -/
example (f g : ℕ → ℝ) (a : ℝ) (hf : Tendsto f atTop (𝓝 a)) (hg : Tendsto g atTop atTop) (G : Prop)
    (k : Tendsto (fun n => f n / g n) atTop (𝓝 0) → G) : G := by
  have h := hf.div_atTop hg
  exact k h

/-! ### R34. `refine h.congr' ?_` (`Filter.Tendsto.congr'`) · goal: a limit of `g` → "`f` and `g`
agree for all large `n`", given the limit `h` of `f` -/
example (f g : ℕ → ℝ) (a : ℝ) (hf : Tendsto f atTop (𝓝 a)) (e : f =ᶠ[atTop] g) :
    Tendsto g atTop (𝓝 a) := by
  refine hf.congr' ?_
  exact e

/-! ### R35. `filter_upwards [eventually_ge_atTop 1] with N hN` · goal: "eventually" → one `N`,
with context gaining `N` and `hN : 1 ≤ N` -/
example (f g : ℕ → ℝ) (e : ∀ N, 1 ≤ N → f N = g N) : f =ᶠ[atTop] g := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact e N hN

/-! ### R36. `positivity` · closes `0 < e`, `0 ≤ e` or `e ≠ 0` built from `+`, `*`, `^`, `exp`,
`cosh`, casts, and hypotheses `0 < x`, `1 ≤ x` about the variables -/
example (N : ℕ) (hN : 1 ≤ N) : (N : ℝ) ≠ 0 := by
  positivity

/-- More shapes `positivity` closes: a power of a positive variable, and `cosh`. -/
example (x : ℝ) (hx : 0 < x) (N : ℕ) : x ^ N ≠ 0 ∧ 0 < 2 * cosh x :=
  ⟨by positivity, by positivity⟩

/-! ### R37. `Real.log_mul` · `x ≠ 0 → y ≠ 0 → log (x * y) = log x + log y` · goal -/
example (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (P : ℝ → Prop) (h : P (Real.log x + Real.log y)) :
    P (Real.log (x * y)) := by
  rw [Real.log_mul hx hy]
  exact h

/-! ### R38. `h.ne'` (`LT.lt.ne'`) · from `h : 0 < a` get `a ≠ 0` (`h.ne` gives `0 ≠ a`) · context -/
example (a : ℝ) (ha : 0 < a) (G : Prop) (k : a ≠ 0 → G) : G := by
  have h := ha.ne'
  exact k h

/-! ### R39. `Real.log_pow` · `log (x ^ n) = n * log x` · goal -/
example (x : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (n * Real.log x)) : P (Real.log (x ^ n)) := by
  rw [Real.log_pow]
  exact h

/-! ## Part 4 · The main theorem (`free_energy_per_spin`) -/

/-! ### R40. `simp_rw [e]` · goal: rewrites with `e` also under `fun N =>`, where `rw` fails -/
example (u v : ℕ → ℝ) (e : ∀ n, u n = v n) (P : (ℕ → ℝ) → Prop) (h : P fun N => v N / N) :
    P fun N => u N / N := by
  simp_rw [e]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A closed form for the powers of another matrix: R1, R5, `ext`, `fin_cases`, R2–R4, R6, R7,
then `ring` for what `simp` leaves (`1 + ↑n = ↑n + 1`) -/
example (n : ℕ) : !![(1 : ℝ), 1; 0, 1] ^ n = !![1, (n : ℝ); 0, 1] := by
  induction n
  case zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  rename_i n ih
  rw [pow_succ, ih]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-! ### W2. The trace of a literal 2×2 matrix: R9, R7 -/
example (a b c d : ℝ) : Matrix.trace !![a, b; c, d] = a + d := by
  simp [Matrix.trace, Fin.sum_univ_two]

/-! ### W3. `log (3 + (1/2)ⁿ) / n → 0`: R28 → R29 → R30 → R31, then R33 with R32 -/
example : Tendsto (fun N : ℕ => Real.log (3 + (1 / 2 : ℝ) ^ N) / N) atTop (𝓝 0) := by
  have h1 : |(1 / 2 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have h2 := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one h1).const_add 3
  have h3 : Tendsto (fun N : ℕ => Real.log (3 + (1 / 2 : ℝ) ^ N)) atTop (𝓝 (Real.log 3)) := by
    simpa using h2.log (by norm_num)
  exact h3.div_atTop tendsto_natCast_atTop_atTop

/-! ### W4. A junk value at `N = 0`: `N / N → 1`, although `0 / 0 = 0` in Lean. R34, R35, R36, R27 -/
example : Tendsto (fun N : ℕ => (N : ℝ) / N) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (N : ℝ) ≠ 0 := by positivity
  field_simp

end H102Guide
