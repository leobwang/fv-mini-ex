/- Guide for M123 (Backward Euler is A-stable).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on an object that is NOT the exercise's (the sequence `geo` below).
Assumed: Lean basics.
-/
import Mathlib
open Filter Topology

namespace M123Guide

/-- A geometric sequence defined by recursion: `geo q y₀ n = qⁿ · y₀`. Used by R1, R3 and Part W. -/
def geo (q y₀ : ℝ) : ℕ → ℝ
  | 0 => y₀
  | n + 1 => q * geo q y₀ n

/-! # Part R · Reference entries -/

/-! ## Recursive definitions, denominators, induction -/

/-! ### R1. `simp only [f]` · goal: `f (n + 1)` → the `n + 1` line of `f`'s definition
`rw [f]` does the same. `simp only [f]` at a variable `n` (not `0`, not `n + 1`) changes nothing. -/
example (q y₀ : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (q * geo q y₀ n)) : P (geo q y₀ (n + 1)) := by
  simp only [geo]
  exact h

/-! ### R2. `field_simp` · goal: an equation with denominators → one without
It multiplies out every denominator it can prove `≠ 0`; put `hb : b ≠ 0` in the context first. -/
example (a b c d : ℝ) (hb : b ≠ 0) (h : a = b * c + a * d) : a / b = c + d * (a / b) := by
  field_simp
  exact h

/-! ### R3. `induction n with` · goal list: `P n` → `P 0` and `P (k + 1)`; context gains `k`, `ih`
Usually each `=> ?_` below is a tactic block that proves its case. -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) (n : ℕ) : P n := by
  induction n with
    | zero => ?_
    | succ k ih => ?_
  exact h0
  exact hs k ih

/-! ### R4. `pow_succ` · `a ^ (n + 1) = a ^ n * a` · goal -/
example {M : Type} [Monoid M] (a : M) (n : ℕ) (P : M → Prop) (h : P (a ^ n * a)) :
    P (a ^ (n + 1)) := by
  rw [pow_succ]
  exact h

/-! ## Inequalities between real numbers -/

/-! ### R5. `nlinarith` · closes an inequality that needs a product of two hypotheses
Here it multiplies `hx` and `hy` to get `0 ≤ x * y`; `linarith` alone fails. -/
example (x y : ℝ) (hx : x ≤ 0) (hy : y ≤ 0) : 2 ≤ 2 + x * y := by
  nlinarith

/-! ### R6. `linarith` · closes a linear inequality that follows from the hypotheses -/
example (x : ℝ) (h1 : 1 ≤ x) : 0 < x := by
  linarith

/-! ### R7. `abs_mul` · `|a * b| = |a| * |b|` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (|a| * |b|)) : P |a * b| := by
  rw [abs_mul]
  exact h

/-! ### R8. `abs_pow` · `|a ^ n| = |a| ^ n` · goal -/
example (a : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (|a| ^ n)) : P |a ^ n| := by
  rw [abs_pow]
  exact h

/-! ### R9. `abs_inv` · `|a⁻¹| = |a|⁻¹` · goal -/
example (a : ℝ) (P : ℝ → Prop) (h : P |a|⁻¹) : P |a⁻¹| := by
  rw [abs_inv]
  exact h

/-! ### R10. `abs_of_pos` · `0 < a → |a| = a` · goal rewritten, plus side goal `0 < a`
Write `rw [abs_of_pos (by linarith)]` to close the side goal on the spot. -/
example (a : ℝ) (P : ℝ → Prop) (h : P a) (ha : 0 < a) : P |a| := by
  rw [abs_of_pos]
  exact h
  exact ha

/-! ### R11. `inv_le_one_of_one_le₀` · `1 ≤ a → a⁻¹ ≤ 1` · goal `a⁻¹ ≤ 1` → `1 ≤ a` -/
example (a : ℝ) (h1 : 1 ≤ a) : a⁻¹ ≤ 1 := by
  apply inv_le_one_of_one_le₀
  exact h1

/-! ### R12. `calc` · closes `a ≤ c` by a chain of steps `a ≤ b`, `b = c`, each with its own proof -/
example (a b c : ℝ) (hab : a ≤ b) (hbc : b = c) : a ≤ c := by
  calc a ≤ b := hab
    _ = c := hbc

/-! ### R13. `gcongr` · goal `x * c ≤ y * c` → `x ≤ y`
It proves the side condition `0 ≤ c` by itself (here `0 ≤ |z|`), and closes `x ≤ y` too if that is a
hypothesis. -/
example (f : ℝ → ℝ) (hf : ∀ t, f t ≤ 1) (a z : ℝ) : f a * |z| ≤ 1 * |z| := by
  gcongr
  exact hf a

/-! ### R14. `pow_le_one₀` · `0 ≤ a → a ≤ 1 → a ^ n ≤ 1` · goal `a ^ n ≤ 1` → two goals -/
example (a : ℝ) (n : ℕ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : a ^ n ≤ 1 := by
  apply pow_le_one₀
  exact h0
  exact h1

/-! ### R15. `abs_nonneg` · `0 ≤ |a|` · closes the goal -/
example (a : ℝ) : 0 ≤ |a| := by
  exact abs_nonneg a

/-! ### R16. `one_mul` · `1 * a = a` · goal -/
example (a : ℝ) (P : ℝ → Prop) (h : P a) : P (1 * a) := by
  rw [one_mul]
  exact h

/-! ### R17. `positivity` · closes `0 ≤ e` or `0 < e` from the shape of `e`
It also reads hypotheses `c < x` (numeral `c ≥ 0`) about the atoms of `e`, as `hx` here. -/
example (x : ℝ) (hx : 2 < x) : 0 ≤ x⁻¹ := by
  positivity

/-! ### R18. `inv_lt_one_of_one_lt₀` · `1 < a → a⁻¹ < 1` · goal `a⁻¹ < 1` → `1 < a` -/
example (a : ℝ) (h1 : 1 < a) : a⁻¹ < 1 := by
  apply inv_lt_one_of_one_lt₀
  exact h1

/-! ## Limits of sequences (`Tendsto`) -/

/-! ### R19. `tendsto_pow_atTop_nhds_zero_of_lt_one` · `0 ≤ r → r < 1 → rⁿ → 0` · context gains it
`Tendsto u atTop (𝓝 L)` means `u n → L` as `n → ∞`. -/
example (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) (G : Prop)
    (g : Tendsto (fun n => r ^ n) atTop (𝓝 0) → G) : G := by
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  exact g hlim

/-! ### R20. `Filter.Tendsto.mul_const` · `f → a` gives `(fun x => f x * c) → a * c` · context -/
example (f : ℕ → ℝ) (a c : ℝ) (hf : Tendsto f atTop (𝓝 a)) (G : Prop)
    (g : Tendsto (fun x => f x * c) atTop (𝓝 (a * c)) → G) : G := by
  have h2 := hf.mul_const c
  exact g h2

/-! ### R21. `rw [zero_mul] at h` · `0 * a = 0` · context: hypothesis `h` is rewritten -/
example (Q : ℝ → Prop) (c : ℝ) (h : Q (0 * c)) : Q 0 := by
  rw [zero_mul] at h
  exact h

/-! ### R22. `Filter.Tendsto.congr` · `(∀ x, f₁ x = f₂ x) → f₁ → L → f₂ → L` · goal
`h.congr ?_` keeps the limit and asks you to show the two sequences agree pointwise. -/
example (f₁ f₂ : ℕ → ℝ) (L : ℝ) (h : Tendsto f₁ atTop (𝓝 L)) (hfg : ∀ x, f₁ x = f₂ x) :
    Tendsto f₂ atTop (𝓝 L) := by
  refine h.congr ?_
  exact hfg

/-! ### R23. `Eq.symm`, written `e.symm` · turns `e : a = b` into `b = a` · closes the goal -/
example {α : Type} (f g : ℕ → α) (e : ∀ n, g n = f n) (n : ℕ) : f n = g n := by
  exact (e n).symm

/-! # Part W · Worked combinations (on `geo`, not the exercise's sequence) -/

/-! ### W1. Closed form by induction: R3, then R1 (`simp [geo]` for `0`), R1 → `rw [ih]` → R4 → `ring` -/
theorem geo_closed (q y₀ : ℝ) (n : ℕ) : geo q y₀ n = q ^ n * y₀ := by
  induction n with
    | zero => simp [geo]
    | succ k ih => rw [geo, ih, pow_succ]; ring

/-! ### W2. A limit through the closed form: R19 → R20 → R21 → R22 with R23 -/
example : Tendsto (geo (1 / 2) 5) atTop (𝓝 0) := by
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).mul_const 5
  rw [zero_mul] at hlim
  exact hlim.congr fun n => (geo_closed (1 / 2) 5 n).symm

end M123Guide
