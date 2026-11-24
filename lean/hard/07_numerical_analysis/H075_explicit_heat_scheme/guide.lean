/- Guide for H075 (Explicit heat scheme: stability, instability, convergence).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (the upwind scheme
`uⱼ ← (1 − c)·uⱼ + c·uⱼ₋₁` for transport, the sequence `(-3) ^ n`, the iterate of `x ↦ x + 2`).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Filter

namespace H075Guide

/-- A stand-in stencil for the unfolding entries (the upwind scheme; not the exercise's scheme). -/
def upwind (c : ℝ) (v : ℤ → ℝ) : ℤ → ℝ := fun j => (1 - c) * v j + c * v (j - 1)

/-! # Part R · Reference entries -/

/-! ## Part 1 · one step is an average (`step_bound`) -/

/-! ### R1. `have h1 := hu x` · context gains the instance `h1 : Q x` of `hu : ∀ y, Q y` -/
example (Q : ℤ → Prop) (hu : ∀ y, Q y) (x : ℤ) : Q (x - 1) := by
  have h1 := hu (x - 1)
  exact h1

/-! ### R2. `linarith` · closes a linear (in)equality that follows from the hypotheses -/
example (r : ℝ) (hr : r ≤ 1 / 3) : 0 ≤ 1 - 3 * r := by
  linarith

/-! ### R3. `unfold D` · goal: the defined name `D` applied to arguments → its body -/
example (c : ℝ) (v : ℤ → ℝ) (j : ℤ) (P : ℝ → Prop) (h : P ((1 - c) * v j + c * v (j - 1))) :
    P (upwind c v j) := by
  unfold upwind
  exact h

/-! ### R4. `calc a ≤ b := ?_ … _ ≤ c := ?_` · goal list: `a ≤ c` → one goal per link
Each link may be `≤`, `<` or `=`; give its proof after `:=` (a term, `by tac`, or `?_` for later). -/
example {α : Type} [LinearOrder α] (a b c : α) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  calc a ≤ b := ?_
    _ ≤ c := ?_
  exact h1
  exact h2

/-! ### R5. `abs_add_three` · `|a + b + c| ≤ |a| + |b| + |c|` (closes the first `calc` link) -/
example (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
  exact abs_add_three a b c

/-! ### R6. `abs_mul` · `|a * b| = |a| * |b|` · `rw [abs_mul]` rewrites the first match -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (|a| * |b|)) : P |a * b| := by
  rw [abs_mul]
  exact h

/-! ### R7. `abs_of_nonneg` · `0 ≤ a → |a| = a` -/
example (a : ℝ) (ha : 0 ≤ a) (P : ℝ → Prop) (h : P a) : P |a| := by
  rw [abs_of_nonneg ha]
  exact h

/-! ### R8. `gcongr` · goal list: `r * x + s * y ≤ r * M + s * M` → the differing parts `x ≤ M`, …
Side goals `0 ≤ r`, `0 ≤ s` and main goals that are already hypotheses (`hy`) are closed for you. -/
example (r s x y M : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hy : y ≤ M) (hx : x + 1 ≤ M + 1) :
    r * x + s * y ≤ r * M + s * M := by
  gcongr
  linarith

/-! ## Part 2 · the checkerboard is an eigenvector (`checkerboard`) -/

/-! ### R9. `Function.iterate_zero`, `id_eq` · goal: `f^[0] x` → `x`
`f^[n]` is `f` applied `n` times. `exact` and `simp` also see `f^[0] x` as `x` by themselves. -/
example (f : ℝ → ℝ) (x : ℝ) (P : ℝ → Prop) (h : P x) : P (f^[0] x) := by
  simp only [Function.iterate_zero, id_eq]
  exact h

/-! ### R10. `Function.iterate_succ_apply'` · `f^[n.succ] x = f (f^[n] x)`: peel the LAST application -/
example (f : ℝ → ℝ) (x : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (f (f^[n] x))) : P (f^[n + 1] x) := by
  rw [Function.iterate_succ_apply']
  exact h

/-! ### R11. `simp only [D]` · goal: `D` → its body, and `(fun j => …) k` is beta-reduced -/
example (c : ℝ) (P : ℝ → Prop) (h : P ((1 - c) * 1 + c * 1)) :
    P (upwind c (fun _ => 1) 0) := by
  simp only [upwind]
  exact h

/-! ### R12. `zpow_sub_one₀` · `a ≠ 0 → a ^ (n - 1) = a ^ n * a⁻¹` for an integer exponent `n : ℤ` -/
example (a : ℝ) (ha : a ≠ 0) (n : ℤ) (P : ℝ → Prop) (h : P (a ^ n * a⁻¹)) : P (a ^ (n - 1)) := by
  rw [zpow_sub_one₀ ha]
  exact h

/-! ### R13. `zpow_add_one₀` · `a ≠ 0 → a ^ (n + 1) = a ^ n * a` for `n : ℤ` -/
example (a : ℝ) (ha : a ≠ 0) (n : ℤ) (P : ℝ → Prop) (h : P (a ^ n * a)) : P (a ^ (n + 1)) := by
  rw [zpow_add_one₀ ha]
  exact h

/-! ### R14. `pow_succ` · `a ^ (n + 1) = a ^ n * a` for a natural exponent `n : ℕ` -/
example {α : Type} [Monoid α] (a : α) (n : ℕ) (P : α → Prop) (h : P (a ^ n * a)) :
    P (a ^ (n + 1)) := by
  rw [pow_succ]
  exact h

/-! ### R15. `ring` · closes a field identity; `(-1)⁻¹` is evaluated, `x ^ j` with `j : ℤ` is an unknown -/
example (s a : ℝ) (j : ℤ) : s * ((-1 : ℝ) ^ j * (-1)⁻¹ * a) = -(s * ((-1 : ℝ) ^ j * a)) := by
  ring

/-! ## Part 4 · induction on the number of steps (`heat_stable`) -/

/-! ### R16. `induction n generalizing j` · goal list: one goal per constructor; the IH is `∀ j`
Without `generalizing j` the IH holds only at the one `j` of the goal. In the `with` form,
`| succ n ih => …` names the `n✝ a✝` below `n ih`; here `case succ n ih => …` does the same. -/
example (Q : ℕ → ℤ → Prop) (h0 : ∀ j, Q 0 j) (hs : ∀ n, (∀ j, Q n j) → ∀ j, Q (n + 1) j)
    (n : ℕ) (j : ℤ) : Q n j := by
  induction n generalizing j
  case zero => exact h0 j
  case succ n ih => exact hs n ih j

/-! ### R17. `have hb := lem _ ih` · context gains `hb`; Lean solves the `_` from `ih`
`lem` wants `∀ j, |u j| ≤ 1`; `ih` says `∀ j, |f j - g j| ≤ 1`, so Lean takes `u := fun j => f j - g j`. -/
example (f g : ℤ → ℝ) (L : (ℤ → ℝ) → Prop) (lem : ∀ u : ℤ → ℝ, (∀ j, |u j| ≤ 1) → L u)
    (ih : ∀ j, |f j - g j| ≤ 1) : L (fun k => f k - g k) := by
  have hb := lem _ ih
  exact hb

/-! ## Part 5 · blow-up (`heat_unstable`) -/

/-! ### R18. `abs_of_neg` · `a < 0 → |a| = -a` -/
example (a : ℝ) (ha : a < 0) (P : ℝ → Prop) (h : P (-a)) : P |a| := by
  rw [abs_of_neg ha]
  exact h

/-! ### R19. `simp_rw [l]` · goal: rewrites with `l` also under `fun n => …` (where `rw` fails) -/
example (g : ℕ → ℝ) (P : (ℕ → ℝ) → Prop) (h : P fun n => |g n| * |(2 : ℝ)|) :
    P fun n => |g n * 2| := by
  simp_rw [abs_mul]
  exact h

/-! ### R20. `zpow_zero` · `a ^ (0 : ℤ) = 1` -/
example (a : ℝ) (P : ℝ → Prop) (h : P 1) : P (a ^ (0 : ℤ)) := by
  rw [zpow_zero]
  exact h

/-! ### R21. `one_mul` · `1 * a = a` -/
example {α : Type} [Monoid α] (a : α) (P : α → Prop) (h : P a) : P (1 * a) := by
  rw [one_mul]
  exact h

/-! ### R22. `abs_pow` · `|a ^ n| = |a| ^ n` -/
example (a : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (|a| ^ n)) : P |a ^ n| := by
  rw [abs_pow]
  exact h

/-! ### R23. `tendsto_pow_atTop_atTop_of_one_lt` · closes `aⁿ → +∞` from `1 < a`
`Tendsto f atTop atTop` reads "f n → +∞ as n → ∞" (`atTop` is the filter of large values). -/
example (a : ℝ) (ha : 1 < a) : Tendsto (fun n : ℕ => a ^ n) atTop atTop := by
  exact tendsto_pow_atTop_atTop_of_one_lt ha

/-! ### R24. `Tendsto.atTop_mul_const` · closes `f n * c → +∞` from `0 < c` and `f n → +∞`
Dot notation: `hf.atTop_mul_const hc` with `hf : Tendsto f atTop atTop`. -/
example (f : ℕ → ℝ) (c : ℝ) (hc : 0 < c) (hf : Tendsto f atTop atTop) :
    Tendsto (fun n => f n * c) atTop atTop := by
  exact hf.atTop_mul_const hc

/-! ### R25. `abs_pos` · `0 < |a| ↔ a ≠ 0`; `abs_pos.mpr ha` uses it right to left -/
example (a : ℝ) (ha : a ≠ 0) : 0 < |a| := by
  exact abs_pos.mpr ha

/-! ## Part 6 · Lax: local errors add up (`heat_lax`) -/

/-! ### R26. `simp` · closes `|x - x| ≤ ↑0 * τ` (`sub_self`, `abs_zero`, `Nat.cast_zero`, `zero_mul`) -/
example (x τ : ℝ) : |x - x| ≤ ((0 : ℕ) : ℝ) * τ := by
  simp

/-! ### R27. `set V := e` · context gains `V := e`; every `e` in the goal and context becomes `V` -/
example (e : ℤ → ℝ) (P Q : (ℤ → ℝ) → Prop) (ih : Q e) (h : ∀ V, Q V → P V) : P e := by
  set V := e
  exact h V ih

/-! ### R28. `ring_nf` · closes `|a - c| = |a - b + (b - c)|`: both sides get the same normal form -/
example (a b c : ℝ) : |a - c| = |a - b + (b - c)| := by
  ring_nf

/-! ### R29. `abs_add_le` · `|a + b| ≤ |a| + |b|` (the triangle inequality) -/
example (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  exact abs_add_le a b

/-! ### R30. `push_cast` · goal: `↑(n + 1)` (a sum cast from `ℕ` to `ℝ`) → `↑n + 1` -/
example (n : ℕ) (P : ℝ → Prop) (h : P (n + 1)) : P ((n + 1 : ℕ) : ℝ) := by
  push_cast
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The upwind step is an average for `0 ≤ c ≤ 1`: R1, R2, R3, R4 with R29, R6, R7, R8, `ring` -/
example (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (v : ℤ → ℝ) (B : ℝ) (hv : ∀ k, |v k| ≤ B) (k : ℤ) :
    |upwind c v k| ≤ B := by
  have h1 := hv k
  have h2 := hv (k - 1)
  have hm : 0 ≤ 1 - c := by linarith
  unfold upwind
  calc |(1 - c) * v k + c * v (k - 1)|
      ≤ |(1 - c) * v k| + |c * v (k - 1)| := abs_add_le _ _
    _ = (1 - c) * |v k| + c * |v (k - 1)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hm, abs_of_nonneg hc0]
    _ ≤ (1 - c) * B + c * B := by gcongr
    _ = B := by ring

/-! ### W2. One upwind step on the checkerboard `(-1) ^ j`: `funext`, R11, R12, R15 -/
example (c : ℝ) : upwind c (fun j => (-1 : ℝ) ^ j) = fun j => (1 - 2 * c) * (-1 : ℝ) ^ j := by
  funext j
  simp only [upwind]
  rw [zpow_sub_one₀ (by norm_num)]
  ring

/-! ### W3. `|(-3) ^ n * 2| → +∞`: R19 with R6, R22, then R23, R24 -/
example : Tendsto (fun n : ℕ => |(-3 : ℝ) ^ n * 2|) atTop atTop := by
  simp_rw [abs_mul, abs_pow]
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)).atTop_mul_const (by norm_num)

/-! ### W4. Induction over an iterate: R16 (`with` form), R10, R30, `ring` -/
example (n : ℕ) : (fun x : ℝ => x + 2)^[n] 0 = 2 * n := by
  induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      push_cast
      ring

end H075Guide
