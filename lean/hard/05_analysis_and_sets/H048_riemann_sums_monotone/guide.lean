/- Guide for H048 (Riemann sums of monotone functions).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` or `k` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other functions, other intervals).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace H048Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 (`piece`): one piece of the interval -/

/-! ### R1. `gcongr` · goal `x / c ≤ y / c` → `x ≤ y` (the side goal `0 ≤ c` is found from `hc`) -/
example (x c : ℝ) (hc : 0 < c) : x / c ≤ (x + 1) / c := by
  gcongr
  linarith

/-! ### R2. `linarith` · closes a linear (in)equality that follows from the hypotheses -/
example (a b c : ℝ) (h1 : a ≤ b) (h2 : b < c) : a < c := by
  linarith

/-! ### R3. `field_simp` · goal: clears denominators it can prove nonzero (here from `hc`) -/
example (x c : ℝ) (hc : 0 < c) : (x + 2) / c - x / c = 2 / c := by
  field_simp
  ring

/-! ### R4. `intervalIntegral.integral_mono_on` · goal `∫ f ≤ ∫ g` → its four hypotheses (goal list)
`a ≤ b`, both functions integrable, and `f ≤ g` on `[a, b]`. In the exercise it is used forward:
`have h := intervalIntegral.integral_mono_on hab hf hg hfg` adds `h : ∫ f ≤ ∫ g` to the context. -/
example (f g : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hg : IntervalIntegrable g MeasureTheory.volume a b) (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
    (∫ x in a..b, f x) ≤ ∫ x in a..b, g x := by
  apply intervalIntegral.integral_mono_on
  exacts [hab, hf, hg, hfg]

/-! ### R5. `intervalIntegrable_const` · closes `IntervalIntegrable (fun _ => c) volume a b`
Inside a longer term Lean cannot guess the measure: write `(μ := MeasureTheory.volume)`. -/
example (a b c : ℝ) : IntervalIntegrable (fun _ => c) MeasureTheory.volume a b := by
  exact intervalIntegrable_const (μ := MeasureTheory.volume)

/-! ### R6. `Monotone.intervalIntegrable` · closes `IntervalIntegrable u volume a b` from `hu : Monotone u` -/
example (u : ℝ → ℝ) (hu : Monotone u) (a b : ℝ) : IntervalIntegrable u MeasureTheory.volume a b := by
  exact hu.intervalIntegrable

/-! ### R7. `hx.1`, `hx.2` · `hx : x ∈ Set.Icc a b` is the pair `a ≤ x ∧ x ≤ b` · context gains a part -/
example (a b x : ℝ) (hx : x ∈ Set.Icc a b) (G : Prop) (k : a ≤ x → G) : G := by
  have h1 : a ≤ x := hx.1
  exact k h1

/-! ### R8. `hu h` · `hu : Monotone u` is a function: `h : a ≤ b` ↦ `hu h : u a ≤ u b` -/
example (u : ℝ → ℝ) (hu : Monotone u) (a b : ℝ) (h : a ≤ b) (G : Prop) (k : u a ≤ u b → G) : G := by
  have hab := hu h
  exact k hab

/-! ### R9. `intervalIntegral.integral_const` · `∫ x in a..b, c = (b - a) • c` · goal (or `at h`) -/
example (a b c : ℝ) (P : ℝ → Prop) (h : P ((b - a) • c)) : P (∫ _ in a..b, c) := by
  rw [intervalIntegral.integral_const]
  exact h

/-! ### R10. `smul_eq_mul` · `a • b = a * b` when both are numbers of the same type · context (`at h`) -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (a • b)) : P (a * b) := by
  rw [smul_eq_mul] at h
  exact h

/-! ### R11. `linarith [show T by tac]` · `linarith` with one extra fact `T` that it cannot find itself -/
example (a b : ℝ) (ha : 0 ≤ a) : 0 ≤ a + b ^ 2 := by
  linarith [show (0 : ℝ) ≤ b ^ 2 by positivity]

/-! ## Part 2 (`split_integral`): cutting `[0, 1]` into pieces -/

/-! ### R12. `positivity` · closes `0 < e`, `0 ≤ e` or `e ≠ 0` when `e` is built from casts, numerals, `+`, `*`, `/`, `^` -/
example (n : ℕ) : (2 * n + 3 : ℝ) ≠ 0 := by
  positivity

/-! ### R13. `intervalIntegral.sum_integral_adjacent_intervals` · goal: the sum of the integrals over
`[a k, a (k + 1)]` equals the integral over `[a 0, a m]` → integrability on each piece.
In the exercise it is used forward, `have h := …`, choosing the cut points `a` and their number with
named arguments `(a := fun k : ℕ => …) (n := …)` (W4). -/
example (g : ℝ → ℝ) (a : ℕ → ℝ) (m : ℕ)
    (hint : ∀ k < m, IntervalIntegrable g MeasureTheory.volume (a k) (a (k + 1))) :
    (∑ k ∈ Finset.range m, ∫ x in a k..a (k + 1), g x) = ∫ x in a 0..a m, g x := by
  apply intervalIntegral.sum_integral_adjacent_intervals
  exact hint

/-! ### R14. `Nat.cast_add`, `Nat.cast_one` · `↑(m + 1)` → `↑m + 1` (move the cast `ℕ → ℝ` inward) -/
example (m : ℕ) (P : ℝ → Prop) (h : P ((m : ℝ) + 1)) : P ((m + 1 : ℕ) : ℝ) := by
  simp only [Nat.cast_add, Nat.cast_one]
  exact h

/-! ### R15. `Nat.cast_zero`, `zero_div` · `↑0 / c` → `0` -/
example (c : ℝ) (P : ℝ → Prop) (h : P 0) : P (((0 : ℕ) : ℝ) / c) := by
  simp only [Nat.cast_zero, zero_div]
  exact h

/-! ### R16. `div_self hc` · `c / c` → `1`, given `hc : c ≠ 0` -/
example (c : ℝ) (hc : c ≠ 0) (P : ℝ → Prop) (h : P 1) : P (c / c) := by
  simp only [div_self hc]
  exact h

/-! ### R17. `h.symm` · turns `h : a = b` into `b = a` -/
example (a b : ℝ) (h : a = b) : b = a := by
  exact h.symm

/-! ## Part 3 (`upper_sum`): telescoping -/

/-! ### R18. `Finset.sum_range_sub` · `∑ i ∈ range m, (u (i + 1) - u i) = u m - u 0` (telescoping) · goal
In the exercise it is used forward: `have tel := Finset.sum_range_sub (fun k : ℕ => …) (n + 1)`. -/
example (u : ℕ → ℝ) (m : ℕ) (P : ℝ → Prop) (h : P (u m - u 0)) :
    P (∑ i ∈ Finset.range m, (u (i + 1) - u i)) := by
  rw [Finset.sum_range_sub]
  exact h

/-! ### R19. `Finset.sum_sub_distrib` · `∑ (f i - g i) = ∑ f i - ∑ g i` · goal (or `at tel`) -/
example (u v : ℕ → ℝ) (m : ℕ) (P : ℝ → Prop)
    (h : P (∑ i ∈ Finset.range m, u i - ∑ i ∈ Finset.range m, v i)) :
    P (∑ i ∈ Finset.range m, (u i - v i)) := by
  rw [Finset.sum_sub_distrib]
  exact h

/-! ### R20. `unfold D` · goal: the defined name `D` → its body -/
noncomputable def avg (u : ℕ → ℝ) (m : ℕ) : ℝ := (∑ i ∈ Finset.range m, u i) / m

example (u : ℕ → ℝ) (m : ℕ) (P : ℝ → Prop) (h : P ((∑ i ∈ Finset.range m, u i) / m)) :
    P (avg u m) := by
  unfold avg
  exact h

/-! ### R21. `Finset.sum_div` · `(∑ i ∈ s, f i) / c = ∑ i ∈ s, f i / c` · goal; `rw [← Finset.sum_div]` goes back -/
example (u : ℕ → ℝ) (m : ℕ) (c : ℝ) (P : ℝ → Prop) (h : P (∑ i ∈ Finset.range m, u i / c)) :
    P ((∑ i ∈ Finset.range m, u i) / c) := by
  rw [Finset.sum_div]
  exact h

/-! ### R22. `add_div` · `(a + b) / c = a / c + b / c`; used right to left: `rw [← add_div]` -/
example (a b c : ℝ) (P : ℝ → Prop) (h : P ((a + b) / c)) : P (a / c + b / c) := by
  rw [← add_div]
  exact h

/-! ### R23. `congr 1` · goal `x / c = y / c` → `x = y` (strips one function application on both sides) -/
example (x y c : ℝ) (h : x - y = 0) : x / c = y / c := by
  congr 1
  linarith

/-! ## Part 4 (`sandwich`): summing the piece bounds -/

/-! ### R24. `Finset.sum_le_sum` · goal `∑ f ≤ ∑ g` → `∀ i ∈ s, f i ≤ g i`
In a term: `Finset.sum_le_sum fun i _ => …`; `(h i).1` and `(h i).2` take the parts of an `∧`. -/
example (u v : ℕ → ℝ) (m : ℕ) (huv : ∀ i, u i ≤ v i) :
    ∑ i ∈ Finset.range m, u i ≤ ∑ i ∈ Finset.range m, v i := by
  apply Finset.sum_le_sum
  exact fun i _ => huv i

/-! ## Part 5 (`riemann_monotone`): epsilon–N -/

/-! ### R25. `intro ε hε` · through a definition whose body is `∀ ε > 0, …`; context gains `ε`, `hε : ε > 0` -/
def Small (u : ℕ → ℝ) : Prop := ∀ ε > 0, ∃ N : ℕ, u N < ε

example (u : ℕ → ℝ) (Q : ℝ → Prop) (hQ : ∀ ε > 0, Q ε) (k : ∀ ε, Q ε → ∃ N : ℕ, u N < ε) :
    Small u := by
  intro ε hε
  exact k ε (hQ ε hε)

/-! ### R26. `obtain ⟨N, hN⟩ := exists_nat_gt x` · context gains `N : ℕ`, `hN : x < ↑N` (ℝ is Archimedean) -/
example (x : ℝ) (P : ℕ → Prop) (k : ∀ N : ℕ, x < N → P N) : ∃ N : ℕ, P N := by
  obtain ⟨N, hN⟩ := exists_nat_gt x
  exact ⟨N, k N hN⟩

/-! ### R27. `refine ⟨N, fun n hn => ?_⟩` · goal `∃ N, ∀ n ≥ N, Q n` → `n, hn : n ≥ N ⊢ Q n` -/
example (Q : ℕ → Prop) (N : ℕ) (k : ∀ n, n ≥ N → Q n) : ∃ M : ℕ, ∀ n ≥ M, Q n := by
  refine ⟨N, fun n hn => ?_⟩
  exact k n hn

/-! ### R28. `obtain ⟨h1, h2⟩ := h` · context: `h : A ∧ B` → `h1 : A`, `h2 : B` -/
example (A B G : Prop) (h : A ∧ B) (k : A → B → G) : G := by
  obtain ⟨h1, h2⟩ := h
  exact k h1 h2

/-! ### R29. `sub_nonneg` · `0 ≤ a - b ↔ b ≤ a`; `sub_nonneg.mpr h` · context gains `0 ≤ a - b` -/
example (u : ℝ → ℝ) (hu : Monotone u) (G : Prop) (k : 0 ≤ u 2 - u 1 → G) : G := by
  have hd := sub_nonneg.mpr (hu (show (1 : ℝ) ≤ 2 by norm_num))
  exact k hd

/-! ### R30. `exact_mod_cast` · closes a goal about casts `↑m` from the same fact on `ℕ` -/
example (m n : ℕ) (h : m ≤ n) : (m : ℝ) ≤ n := by
  exact_mod_cast h

/-! ### R31. `div_lt_iff₀ hc` · `0 < c → (b / c < a ↔ b < a * c)` · goal, or `at h` for a hypothesis -/
example (a b c : ℝ) (hc : 0 < c) (h : b < a * c) : b / c < a := by
  rw [div_lt_iff₀ hc]
  exact h

/-! ### R32. `nlinarith` · like `linarith`, but also multiplies hypotheses together (products of terms) -/
example (a b c : ℝ) (ha : 0 ≤ a) (hbc : b ≤ c) : a * b ≤ a * c := by
  nlinarith

/-! ### R33. `abs_sub_lt_iff` · `|a - b| < c ↔ a - b < c ∧ b - a < c` · goal: absolute value → two inequalities -/
example (a b c : ℝ) (h1 : a - b < c) (h2 : b - a < c) : |a - b| < c := by
  rw [abs_sub_lt_iff]
  exact ⟨h1, h2⟩

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Integral of a constant: R9, R10, then `norm_num` -/
example : (∫ _ in (1 : ℝ)..3, (5 : ℝ)) = 10 := by
  rw [intervalIntegral.integral_const]
  rw [smul_eq_mul]
  norm_num

/-! ### W2. Compare `x ↦ x` with the constant `1` on `[0, 1]`: R4 with R6, R5, R7, then R9, R10, R2 -/
example : (∫ x in (0 : ℝ)..1, x) ≤ 1 := by
  have h : (∫ x in (0 : ℝ)..1, x) ≤ ∫ _ in (0 : ℝ)..1, (1 : ℝ) :=
    intervalIntegral.integral_mono_on zero_le_one monotone_id.intervalIntegrable
      intervalIntegrable_const (fun x hx => hx.2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith

/-! ### W3. Telescoping a sum: R18, then clean the casts with R14, R15 -/
example (m : ℕ) : ∑ i ∈ Finset.range m, (((i : ℝ) + 1) * 2 - (i : ℝ) * 2) = (m : ℝ) * 2 := by
  have tel := Finset.sum_range_sub (fun i : ℕ => (i : ℝ) * 2) m
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, sub_zero] at tel
  exact tel

/-! ### W4. `[0, 2]` cut into 4 pieces of width `1/2`: R13 with named arguments, then R14, R15, `norm_num` -/
example (g : ℝ → ℝ) (hg : Monotone g) :
    ∑ k ∈ Finset.range 4, ∫ x in (k / 2 : ℝ)..((k + 1) / 2 : ℝ), g x = ∫ x in (0 : ℝ)..2, g x := by
  have h := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := MeasureTheory.volume)
    (a := fun k : ℕ => (k : ℝ) / 2) (n := 4) (fun k _ => hg.intervalIntegrable)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div] at h
  norm_num at h
  exact h

/-! ### W5. `c / (n + 2) < ε` for all large `n`: R25, R26, R27, R30, R31 (goal, side goal by R12, and `at hN`), R32 -/
example (c : ℝ) (hc : 0 ≤ c) : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, c / ((n : ℝ) + 2) < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (c / ε)
  refine ⟨N, fun n hn => ?_⟩
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hε] at hN
  nlinarith

end H048Guide
