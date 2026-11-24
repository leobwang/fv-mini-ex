/- Guide for H062 (Bisection finds a root).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (another iteration, `3 ^ n`).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Filter Topology

namespace H062Guide

/-! # Part R · Reference entries -/

/-! ## Parts 1–2 · Loop invariants by induction (milestones `bisect_invariant`, `bisect_nested`) -/

/-! ### R1. `induction n with | zero => ?_ | succ k ih => ?_` · goal list: `P n` → `P 0`, `P (k + 1)`
The second goal has the induction hypothesis `ih : P k` in its context. -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) (n : ℕ) : P n := by
  induction n with
    | zero => ?_
    | succ k ih => ?_
  exact h0
  exact hs k ih

/-- `iter g x n` applies `g` to `x`, `n` times: a definition by recursion on `n`, like `bisect`. -/
def iter {α : Type} (g : α → α) (x : α) : ℕ → α
  | 0 => x
  | n + 1 => g (iter g x n)

/-! ### R2. `obtain ⟨h1, h2, h3⟩ := h` · context: a conjunction `h` → its three parts -/
example (A B C G : Prop) (h : A ∧ B ∧ C) (k : A → B → C → G) : G := by
  obtain ⟨h1, h2, h3⟩ := h
  exact k h1 h2 h3

/-! ### R3. `simp only [iter]` · goal: one recursion step of a definition is unfolded
`simp only [D₁, D₂]` with several names unfolds all of them (a recursive call and then the step). -/
example {α : Type} (g : α → α) (x : α) (n : ℕ) (P : α → Prop) (h : P (g (iter g x n))) :
    P (iter g x (n + 1)) := by
  simp only [iter]
  exact h

/-! ### R4. `split_ifs with hm` · goal list: `P (if c then x else y)` → `P x` with `hm : c`,
and `P y` with `hm : ¬c` -/
example (c : Prop) [Decidable c] (x y : ℝ × ℝ) (P : ℝ × ℝ → Prop) (h1 : c → P x)
    (h2 : ¬c → P y) : P (if c then x else y) := by
  split_ifs with hm
  exact h1 hm
  exact h2 hm

/-! ### R5. `simp only` (no lemmas) · goal: projections of a literal pair, `(x, y).1` → `x` -/
example (x y : ℝ) (P : ℝ → ℝ → Prop) (h : P x y) : P (x, y).1 (x, y).2 := by
  simp only
  exact h

/-! ### R6. `pow_succ` · `a ^ (n + 1) = a ^ n * a` -/
example {M : Type} [Monoid M] (a : M) (n : ℕ) (P : M → Prop) (h : P (a ^ n * a)) :
    P (a ^ (n + 1)) := by
  rw [pow_succ]
  exact h

/-! ### R7. `div_div` · `a / b / c = a / (b * c)`; used right to left: `rw [← div_div]` -/
example {α : Type} [DivisionCommMonoid α] (a b c : α) (P : α → Prop) (h : P (a / b / c)) :
    P (a / (b * c)) := by
  rw [← div_div]
  exact h

/-! ### R8. `linarith` · closes a linear (in)equality that follows from the hypotheses
It reads `¬ x ≤ 0` as `0 < x`, so the `else` branch of `split_ifs` is usable directly. -/
example (x y : ℝ) (hm : ¬x ≤ 0) (hy : y ≤ x) : y ≤ 2 * x := by
  linarith

/-! ### R9. `ring` · closes an identity of commutative rings; division by a numeral is fine -/
example (x y : ℝ) : y - (x + y) / 2 = (y - x) / 2 := by
  ring

/-! ## Part 3 · Monotone sequences and `max` (milestone `lo_le_hi`) -/

/-! ### R10. `monotone_nat_of_le_succ` · goal `Monotone u` → one step `u n ≤ u (n + 1)` -/
example (u : ℕ → ℝ) (h : ∀ n, u n ≤ u (n + 1)) : Monotone u := by
  apply monotone_nat_of_le_succ
  exact h

/-! ### R11. `antitone_nat_of_succ_le` · goal `Antitone v` → one step `v (n + 1) ≤ v n` -/
example (v : ℕ → ℝ) (h : ∀ n, v (n + 1) ≤ v n) : Antitone v := by
  apply antitone_nat_of_succ_le
  exact h

/-! ### R12. `div_nonneg` · `0 ≤ a → 0 ≤ b → 0 ≤ a / b` · goal → two goals -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by
  apply div_nonneg
  exact ha
  exact hb

/-! ### R13. `positivity` · closes `0 ≤ e` or `0 < e` when `e` is visibly nonnegative (`2 ^ k`, squares, …) -/
example (k : ℕ) : (0 : ℝ) < 2 ^ k := by
  positivity

/-! ### R14. `calc` · proves `x ≤ z` as a chain `x ≤ y`, `y ≤ z`, one proof term per link -/
example (x y z : ℝ) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  calc x ≤ y := h1
    _ ≤ z := h2

/-! ### R15. Using `hu : Monotone u` / `hv : Antitone v` · context gains the inequality at `m ≤ n`
`Monotone u` is `∀ ⦃a b⦄, a ≤ b → u a ≤ u b`: apply it to a proof of `m ≤ n`. -/
example (u v : ℕ → ℝ) (hu : Monotone u) (hv : Antitone v) (m n : ℕ) (hmn : m ≤ n) (G : Prop)
    (k : u m ≤ u n → v n ≤ v m → G) : G := by
  have h1 := hu hmn
  have h2 := hv hmn
  exact k h1 h2

/-! ### R16. `le_max_left`, `le_max_right` · context gains `m ≤ max m n`, `n ≤ max m n` -/
example (m n : ℕ) (G : Prop) (k : m ≤ max m n → n ≤ max m n → G) : G := by
  have h1 := le_max_left m n
  have h2 := le_max_right m n
  exact k h1 h2

/-! ## Part 4 · A geometric sequence tends to 0 (milestone `gap_tendsto`) -/

/-! ### R17. `simp_rw [div_eq_mul_inv]` · goal: `c / u n` → `c * (u n)⁻¹`, also under `fun n =>`
`rw` cannot rewrite a term that mentions the bound variable `n`; `simp_rw` can. -/
example (c : ℝ) (u : ℕ → ℝ) (P : (ℕ → ℝ) → Prop) (h : P fun n => c * (u n)⁻¹) :
    P fun n => c / u n := by
  simp_rw [div_eq_mul_inv]
  exact h

/-! ### R18. `inv_pow` · `a⁻¹ ^ n = (a ^ n)⁻¹`; right to left under a binder: `simp_rw [← inv_pow]` -/
example (c x : ℝ) (P : (ℕ → ℝ) → Prop) (h : P fun n => c * x⁻¹ ^ n) :
    P fun n => c * (x ^ n)⁻¹ := by
  simp_rw [← inv_pow]
  exact h

/-! ### R19. `tendsto_pow_atTop_nhds_zero_of_lt_one` · `0 ≤ r → r < 1 → rⁿ → 0` · context gains the limit -/
example (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) (G : Prop)
    (k : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) → G) : G := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  exact k h

/-! ### R20. `Tendsto.const_mul` · from `u n → L` get `c * u n → c * L` · context -/
example (u : ℕ → ℝ) (L c : ℝ) (hu : Tendsto u atTop (𝓝 L)) (G : Prop)
    (k : Tendsto (fun n => c * u n) atTop (𝓝 (c * L)) → G) : G := by
  have h := hu.const_mul c
  exact k h

/-! ### R21. `simpa using e` · closes the goal when `simp` brings `e` and the goal to the same form
Here `simp` turns `c * 0` into `0`. -/
example (u : ℕ → ℝ) (c : ℝ) (h : Tendsto (fun n => c * u n) atTop (𝓝 (c * 0))) :
    Tendsto (fun n => c * u n) atTop (𝓝 0) := by
  simpa using h

/-! ## Part 5 · The supremum and the limits (`bisection_finds_root`) -/

/-! ### R22. `set s := e with hs` · context gains `s := e` and `hs : s = e`; goal: `e` → `s` -/
example (u : ℕ → ℝ) (P : ℝ → Prop) (h : P (⨆ n, u n)) : P (⨆ n, u n) := by
  set s := ⨆ n, u n with hs
  exact h

/-! ### R23. `refine ⟨b, ?_⟩` on `BddAbove S` · goal: "some upper bound" → "`b` is an upper bound" -/
example (u : ℕ → ℝ) (b : ℝ) (h : b ∈ upperBounds (Set.range u)) : BddAbove (Set.range u) := by
  refine ⟨b, ?_⟩
  exact h

/-! ### R24. `rintro _ ⟨m, rfl⟩` · goal `b ∈ upperBounds (Set.range u)` → `u m ≤ b` for a new `m` -/
example (u : ℕ → ℝ) (b : ℝ) (h : ∀ n, u n ≤ b) : b ∈ upperBounds (Set.range u) := by
  rintro _ ⟨m, rfl⟩
  exact h m

/-! ### R25. `le_ciSup` · `BddAbove (Set.range u) → ∀ n, u n ≤ ⨆ i, u i` · context -/
example (u : ℕ → ℝ) (hb : BddAbove (Set.range u)) (n : ℕ) (G : Prop)
    (k : u n ≤ ⨆ i, u i → G) : G := by
  have h := le_ciSup hb n
  exact k h

/-! ### R26. `ciSup_le` · `(∀ i, u i ≤ c) → ⨆ i, u i ≤ c` · goal: a bound on the sup → a bound on each term -/
example (u : ℕ → ℝ) (c : ℝ) (h : ∀ i, u i ≤ c) : ⨆ i, u i ≤ c := by
  apply ciSup_le
  exact h

/-! ### R27. `tendsto_atTop_ciSup` · monotone and bounded above → `u n → ⨆ i, u i` · closes the goal -/
example (u : ℕ → ℝ) (hm : Monotone u) (hb : BddAbove (Set.range u)) :
    Tendsto u atTop (𝓝 (⨆ i, u i)) := by
  exact tendsto_atTop_ciSup hm hb

/-! ### R28. `funext n` · goal: equality of functions → equality at a new point `n` -/
example (u v : ℕ → ℝ) (h : ∀ n, u n = v n + 0) : u = fun n => v n + 0 := by
  funext n
  exact h n

/-! ### R29. `simp only [v] at h` · context: unfold a `set` name `v` inside the hypothesis `h` -/
example (u : ℕ → ℝ) (c : ℝ) (hc : ∀ n, u n + 1 ≤ c) : u 0 + 1 ≤ c := by
  set v := fun n => u n + 1 with hv
  have h : v 0 ≤ c := hc 0
  simp only [v] at h
  exact h

/-! ### R30. `Tendsto.add` · `u n → L`, `v n → M` give `u n + v n → L + M` · context -/
example (u v : ℕ → ℝ) (L M : ℝ) (hu : Tendsto u atTop (𝓝 L)) (hv : Tendsto v atTop (𝓝 M))
    (G : Prop) (k : Tendsto (fun n => u n + v n) atTop (𝓝 (L + M)) → G) : G := by
  have h := hu.add hv
  exact k h

/-! ### R31. `Continuous.tendsto` · `g` continuous → `g y → g x` as `y → x` · context -/
example (g : ℝ → ℝ) (hg : Continuous g) (x : ℝ) (G : Prop)
    (k : Tendsto g (𝓝 x) (𝓝 (g x)) → G) : G := by
  have h := hg.tendsto x
  exact k h

/-! ### R32. `Tendsto.comp` · `g y → g L` as `y → L`, and `u n → L`, give `g (u n) → g L` · context
`(g ∘ u) n` is `g (u n)` by definition, so lemmas accept `∀ n, g (u n) ≤ 0` for it. -/
example (g : ℝ → ℝ) (u : ℕ → ℝ) (L : ℝ) (hg : Tendsto g (𝓝 L) (𝓝 (g L)))
    (hu : Tendsto u atTop (𝓝 L)) (G : Prop) (k : Tendsto (g ∘ u) atTop (𝓝 (g L)) → G) : G := by
  have h := hg.comp hu
  exact k h

/-! ### R33. `le_of_tendsto'` · `u n → L` and `∀ n, u n ≤ b` give `L ≤ b` · goal → the bound on each term -/
example (u : ℕ → ℝ) (L b : ℝ) (hu : Tendsto u atTop (𝓝 L)) (h : ∀ n, u n ≤ b) : L ≤ b := by
  apply le_of_tendsto' hu
  exact h

/-! ### R34. `ge_of_tendsto'` · `u n → L` and `∀ n, b ≤ u n` give `b ≤ L` · goal → the bound on each term -/
example (u : ℕ → ℝ) (L b : ℝ) (hu : Tendsto u atTop (𝓝 L)) (h : ∀ n, b ≤ u n) : b ≤ L := by
  apply ge_of_tendsto' hu
  exact h

/-! ### R35. `le_antisymm` · `x ≤ y → y ≤ x → x = y` · goal → two goals -/
example (x y : ℝ) (h1 : x ≤ y) (h2 : y ≤ x) : x = y := by
  apply le_antisymm
  exact h1
  exact h2

/-! ### R36. `abs_le` · `|a| ≤ b ↔ -b ≤ a ∧ a ≤ b` · goal: an absolute-value bound → two inequalities -/
example (x c d : ℝ) (h : -d ≤ x - c ∧ x - c ≤ d) : |x - c| ≤ d := by
  rw [abs_le]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-- a different interval step: halve whichever end is chosen by the sign of the left end -/
noncomputable def shrink (I : ℝ × ℝ) : ℝ × ℝ :=
  if I.1 ≤ 0 then (I.1 / 2, I.2) else (I.1, I.2 / 2)

/-! ### W1. An invariant of an iteration: R1, R3, R4, R5, R8 -/
example (I : ℝ × ℝ) (h : 0 ≤ I.2) (n : ℕ) : 0 ≤ (iter shrink I n).2 := by
  induction n with
    | zero => ?_
    | succ k ih => ?_
  simpa [iter] using h
  simp only [iter, shrink]
  split_ifs with hm
  · simp only
    linarith
  · simp only
    linarith

/-! ### W2. Monotone and bounded: the sup is a limit and an upper bound (R10, R23, R24, R27, R25) -/
example (u : ℕ → ℝ) (hu : ∀ n, u n ≤ u (n + 1)) (hb : ∀ n, u n ≤ 1) :
    Tendsto u atTop (𝓝 (⨆ n, u n)) ∧ ∀ n, u n ≤ ⨆ i, u i := by
  have hbdd : BddAbove (Set.range u) := ⟨1, by rintro _ ⟨m, rfl⟩; exact hb m⟩
  exact ⟨tendsto_atTop_ciSup (monotone_nat_of_le_succ hu) hbdd, fun n => le_ciSup hbdd n⟩

/-! ### W3. A sign passes to the limit through a continuous `g`: R31 → R32 → R33 -/
example (g : ℝ → ℝ) (hg : Continuous g) (u : ℕ → ℝ) (L : ℝ) (hu : Tendsto u atTop (𝓝 L))
    (hneg : ∀ n, g (u n) ≤ 0) : g L ≤ 0 := by
  exact le_of_tendsto' ((hg.tendsto L).comp hu) hneg

/-! ### W4. `c / 3 ^ n → 0`: R17, R18, then R19 → R20 → R21 -/
example (c : ℝ) : Tendsto (fun n : ℕ => c / 3 ^ n) atTop (𝓝 0) := by
  simp_rw [div_eq_mul_inv]
  simp_rw [← inv_pow]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3⁻¹)
    (by norm_num)).const_mul c

/-! ### W5. Squeezed between `l` and `h` → within `h - l` of `l`: R36, `constructor`, R8 -/
example (x l h : ℝ) (h1 : l ≤ x) (h2 : x ≤ h) : |x - l| ≤ h - l := by
  rw [abs_le]
  constructor
  · linarith
  · linarith

end H062Guide
