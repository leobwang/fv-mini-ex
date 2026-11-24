/- Guide for H064 (Heron's method converges).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`G : Prop` is an arbitrary goal; it only exists so that a new hypothesis can be shown.
Part W: worked combinations on objects that are NOT the exercise's (another step map, another
recursion).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Filter Topology

namespace H064Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · Algebra of one step: unfold, clear denominators, nonlinear arithmetic -/

/-! ### R1. `unfold f` · goal: the defined name `f` → its body -/
noncomputable def step (x : ℝ) : ℝ := x / 2 + 1 / x

example (x : ℝ) (P : ℝ → Prop) (h : P (x / 2 + 1 / x)) : P (step x) := by
  unfold step
  exact h

/-! ### R2. `Real.sq_sqrt` · `0 ≤ x → √x ^ 2 = x` · context, with `have hs := Real.sq_sqrt hx` -/
example (x : ℝ) (hx : 0 ≤ x) (G : Prop) (hG : √x ^ 2 = x → G) : G := by
  have hs := Real.sq_sqrt hx
  exact hG hs

/-! ### R3. `field_simp` · goal: denominators cleared (it proves `x ≠ 0` from `hx : 0 < x`) -/
example (a b c x : ℝ) (hx : 0 < x) (h : a + x * b = x * c) : a / x + b = c := by
  field_simp
  exact h

/-! ### R4. `nlinarith [t₁, t₂]` · closes a polynomial (in)equality; also multiplies hypotheses
and the hint terms `tᵢ` in pairs, which `linarith` does not -/
example (s x : ℝ) (hs : 0 ≤ s) (h : s ≤ x) : s * s ≤ x * x := by
  nlinarith [hs, h]

/-! ## Part 2 · Signs -/

/-! ### R5. `positivity` · closes `0 ≤ e` or `0 < e` built from squares, `+`, `*`, `/` and atoms
whose sign is a hypothesis -/
example (x y : ℝ) (hy : 0 < y) : 0 ≤ (x - 1) ^ 2 / (3 * y) := by
  positivity

/-! ### R6. `linarith` · closes a linear (in)equality from the hypotheses; a nonlinear piece such as
`(x - 1) ^ 2 / y` counts as one unknown -/
example (a b c : ℝ) (h₁ : a - b = c) (h₂ : 0 ≤ c) : b ≤ a := by
  linarith

/-! ## Part 3 · Dividing out an inequality -/

/-! ### R7. `div_le_iff₀` · `0 < c → (a / c ≤ b ↔ a ≤ b * c)` · goal -/
example (a b c : ℝ) (hc : 0 < c) (h : a ≤ b * c) : a / c ≤ b := by
  rw [div_le_iff₀ hc]
  exact h

/-! ### R8. `Real.sqrt_nonneg` · `0 ≤ √x` for every real `x` · context -/
example (x : ℝ) (G : Prop) (hG : 0 ≤ √x → G) : G := by
  have h := Real.sqrt_nonneg x
  exact hG h

/-! ## Part 4 · Induction along the iteration -/

/-! ### R9. `induction n with | zero => ?_ | succ n ih => ?_` · goal list: base case and step -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ k, P k → P (k + 1)) (n : ℕ) : P n := by
  induction n with | zero => ?_ | succ n ih => ?_
  exacts [h0, hs n ih]

/-! ### R10. A recursive `def` computes by definition · `show` (or `exact`) sees `s (n + 1)` as the body -/
noncomputable def seq (x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => step (seq x₀ n)

example (x₀ : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (step (seq x₀ n))) : P (seq x₀ (n + 1)) := by
  show P (step (seq x₀ n))
  exact h

/-! ### R11. `hab.le` (`LT.lt.le`) · `a < b → a ≤ b` · context -/
example (a b : ℝ) (hab : a < b) (G : Prop) (hG : a ≤ b → G) : G := by
  have h := hab.le
  exact hG h

/-! ### R12. `lt_of_lt_of_le` · `a < b → b ≤ c → a < c` · goal, with `apply` -/
example (a b c : ℝ) (hab : a < b) (hbc : b ≤ c) : a < c := by
  apply lt_of_lt_of_le hab
  exact hbc

/-! ### R13. `Real.sqrt_pos` · `0 < √x ↔ 0 < x` · goal; as a term: `Real.sqrt_pos.mpr hx : 0 < √x` -/
example (x : ℝ) (hx : 0 < x) : 0 < √x := by
  rw [Real.sqrt_pos]
  exact hx

/-! ## Part 5 · The fixed-point equation -/

/-! ### R14. `unfold f at h` · context: the name `f` in `h` → its body -/
example (x : ℝ) (G : Prop) (h : step x = x) (hG : x / 2 + 1 / x = x → G) : G := by
  unfold step at h
  exact hG h

/-! ### R15. `field_simp at h` · context: denominators of `h` cleared -/
example (x : ℝ) (hx : 0 < x) (G : Prop) (h : (x + 3 / x) / 4 = x) (hG : x ^ 2 + 3 = x ^ 2 * 4 → G) :
    G := by
  field_simp at h
  exact hG h

/-! ### R16. `Real.sqrt_sq` · `0 ≤ x → √(x ^ 2) = x` · goal -/
example (x : ℝ) (hx : 0 ≤ x) (P : ℝ → Prop) (h : P x) : P √(x ^ 2) := by
  rw [Real.sqrt_sq hx]
  exact h

/-! ## Part 6 · Limits: monotone convergence and identifying the limit -/

/-! ### R17. `set g := e with hg` · context gains `g := e` and `hg : g = e`; `e` → `g` everywhere -/
example (u : ℕ → ℝ) (P : (ℕ → ℝ) → Prop) (h : P (fun n => u (n + 1))) :
    P (fun n => u (n + 1)) := by
  set g := fun n => u (n + 1) with hg
  exact h

/-! ### R18. `antitone_nat_of_succ_le` · `(∀ n, f (n + 1) ≤ f n) → Antitone f` · goal, with `apply` -/
example (f : ℕ → ℝ) (h : ∀ n, f (n + 1) ≤ f n) : Antitone f := by
  apply antitone_nat_of_succ_le
  exact h

/-! ### R19. `refine ⟨c, ?_⟩` on `BddBelow s` · goal: "some lower bound exists" → "`c` is one" -/
example (f : ℕ → ℝ) (c : ℝ) (h : c ∈ lowerBounds (Set.range f)) : BddBelow (Set.range f) := by
  refine ⟨c, ?_⟩
  exact h

/-! ### R20. `rintro _ ⟨n, rfl⟩` · goal `c ∈ lowerBounds (Set.range f)` → `c ≤ f n` for a new `n` -/
example (f : ℕ → ℝ) (c : ℝ) (h : ∀ n, c ≤ f n) : c ∈ lowerBounds (Set.range f) := by
  rintro _ ⟨n, rfl⟩
  exact h n

/-! ### R21. `tendsto_atTop_ciInf` · `Antitone f → BddBelow (Set.range f) → Tendsto f atTop (𝓝 (⨅ i, f i))`
(monotone convergence) · goal list, with `apply` -/
example (f : ℕ → ℝ) (h₁ : Antitone f) (h₂ : BddBelow (Set.range f)) :
    Tendsto f atTop (𝓝 (⨅ i, f i)) := by
  apply tendsto_atTop_ciInf
  exacts [h₁, h₂]

/-! ### R22. `le_ciInf` · `(∀ i, c ≤ f i) → c ≤ ⨅ i, f i` · goal, with `apply` -/
example (f : ℕ → ℝ) (c : ℝ) (h : ∀ i, c ≤ f i) : c ≤ ⨅ i, f i := by
  apply le_ciInf
  exact h

/-! ### R23. `hx.ne'` (`LT.lt.ne'`) · `0 < x → x ≠ 0` · context -/
example (x : ℝ) (hx : 0 < x) (G : Prop) (hG : x ≠ 0 → G) : G := by
  have h := hx.ne'
  exact hG h

/-! ### R24. `fun_prop (disch := exact h)` · closes `ContinuousAt (fun x => …) L`; `disch` proves the
side goals it cannot (here `L ≠ 0`, for the division by `x`) -/
example (L : ℝ) (hL : L ≠ 0) : ContinuousAt (fun x => x / 2 + 1 / x) L := by
  fun_prop (disch := exact hL)

/-! ### R25. `ContinuousAt.tendsto` · `ContinuousAt f x → Tendsto f (𝓝 x) (𝓝 (f x))` · context -/
example (f : ℝ → ℝ) (x : ℝ) (hf : ContinuousAt f x) (G : Prop)
    (hG : Tendsto f (𝓝 x) (𝓝 (f x)) → G) : G := by
  have t := hf.tendsto
  exact hG t

/-! ### R26. `Tendsto.comp` · `Tendsto g l₂ l₃ → Tendsto u l₁ l₂ → Tendsto (g ∘ u) l₁ l₃` · context
Written `hg.comp hu`. `(g ∘ u) n` is by definition `g (u n)`, so a `have` may state it as
`Tendsto (fun n => g (u n)) …`. -/
example (g : ℝ → ℝ) (u : ℕ → ℝ) (L : ℝ) (hg : Tendsto g (𝓝 L) (𝓝 (g L)))
    (hu : Tendsto u atTop (𝓝 L)) (G : Prop) (hG : Tendsto (g ∘ u) atTop (𝓝 (g L)) → G) : G := by
  have t := hg.comp hu
  exact hG t

/-! ### R27. `tendsto_add_atTop_nat` · `Tendsto (fun n => n + k) atTop atTop` · context
Composing with it (R26) turns `u n → L` into `u (n + k) → L`. -/
example (G : Prop) (hG : Tendsto (fun n : ℕ => n + 1) atTop atTop → G) : G := by
  have t := tendsto_add_atTop_nat 1
  exact hG t

/-! ### R28. `tendsto_nhds_unique` · `Tendsto u l (𝓝 a) → Tendsto u l (𝓝 b) → a = b` · context -/
example (u : ℕ → ℝ) (a b : ℝ) (h₁ : Tendsto u atTop (𝓝 a)) (h₂ : Tendsto u atTop (𝓝 b))
    (G : Prop) (hG : a = b → G) : G := by
  have e := tendsto_nhds_unique h₁ h₂
  exact hG e

/-! ### R29. `tendsto_add_atTop_iff_nat` · `Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f atTop l`
· goal, right to left: `rw [← tendsto_add_atTop_iff_nat 1]` -/
example (f : ℕ → ℝ) (l : Filter ℝ) (h : Tendsto (fun n => f (n + 1)) atTop l) :
    Tendsto f atTop l := by
  rw [← tendsto_add_atTop_iff_nat 1]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A named map is continuous: unfold it first (R1), then R24 -/
example (L : ℝ) (hL : 0 < L) : ContinuousAt step L := by
  unfold step
  fun_prop (disch := exact hL.ne')

/-! ### W2. Monotone convergence for any decreasing sequence `u ≥ 0`: R21, R18, R19, R20, then R22 -/
example (u : ℕ → ℝ) (hdec : ∀ n, u (n + 1) ≤ u n) (hlow : ∀ n, 0 ≤ u n) :
    Tendsto u atTop (𝓝 (⨅ n, u n)) ∧ 0 ≤ ⨅ n, u n := by
  constructor
  · apply tendsto_atTop_ciInf
    · exact antitone_nat_of_succ_le hdec
    · refine ⟨0, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact hlow n
  · exact le_ciInf hlow

/-! ### W3. Identifying a limit for `w (n + 1) = w n / 2 + 1`: R24, R25, R26, R27, R28, R6
The same sequence has the limit `L / 2 + 1` (continuity) and `L` (shift), so `L = 2`. -/
noncomputable def half (x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => half x₀ n / 2 + 1

example (x₀ L : ℝ) (h : Tendsto (half x₀) atTop (𝓝 L)) : L = 2 := by
  have hc : ContinuousAt (fun x : ℝ => x / 2 + 1) L := by fun_prop
  have t₁ : Tendsto (fun n => half x₀ n / 2 + 1) atTop (𝓝 (L / 2 + 1)) := hc.tendsto.comp h
  have t₂ : Tendsto (fun n => half x₀ (n + 1)) atTop (𝓝 L) := h.comp (tendsto_add_atTop_nat 1)
  have e : L / 2 + 1 = L := tendsto_nhds_unique t₁ t₂
  linarith

end H064Guide
