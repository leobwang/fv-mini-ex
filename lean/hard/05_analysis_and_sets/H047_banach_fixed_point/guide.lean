/- Guide for H047 (Banach fixed-point theorem).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`X` is any metric space (`[MetricSpace X]`), `u : ℕ → X` a sequence in it, `g : X → X` a map.
Part W: worked combinations on objects that are NOT the exercise's (real sequences `u (n+1) ≤ r * u n`,
the sequence `(1/2)^n`, a sequence with `u (n+1) = c * u n`).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Filter Topology Finset

namespace H047Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · one step of the iteration: induction on `n` -/

/-! ### R1. `induction n with` · goal list: `P n` → `P 0` and `P (n + 1)` with `ih : P n`
`?_` leaves a case open for the next tactic; in a proof write the case's tactics after `=>`. -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) (n : ℕ) : P n := by
  induction n with
    | zero => ?_
    | succ n ih => ?_
  exact h0
  exact hs n ih

/-! ### R2. `Function.iterate_zero`, `Function.iterate_one` · goal: `g^[0] x` → `x`, `g^[0 + 1] x` → `g x`
`g^[n]` is `g` composed with itself `n` times; `g^[0] = id`, `g^[1] = g`. Plain `simp` uses both. -/
example {X : Type} (g : X → X) (x : X) (P : X → X → Prop) (h : P x (g x)) :
    P (g^[0] x) (g^[0 + 1] x) := by
  simp only [zero_add, Function.iterate_zero, id_eq, Function.iterate_one]
  exact h

/-! ### R3. `pow_zero`, `one_mul` · goal: `k ^ 0 * a` → `a` (`simp` uses both) -/
example (k a : ℝ) (P : ℝ → Prop) (h : P a) : P (k ^ 0 * a) := by
  rw [pow_zero, one_mul]
  exact h

/-! ### R4. `calc` · goal `a ≤ d` → one goal per step `a = b`, `b ≤ c`, `c = d`
Each step is `_ rel rhs := proof`; `_` is the previous right-hand side. Mixing `=`, `≤`, `<` is fine. -/
example (a b c d : ℝ) (h1 : a = b) (h2 : b ≤ c) (h3 : c = d) : a ≤ d := by
  calc a = b := h1
    _ ≤ c := h2
    _ = d := h3

/-! ### R5. `Function.iterate_succ_apply'` · `g^[n.succ] x = g (g^[n] x)` · goal: peel the last `g` -/
example {X : Type} (g : X → X) (n : ℕ) (x : X) (P : X → Prop) (h : P (g (g^[n] x))) :
    P (g^[n + 1] x) := by
  rw [Function.iterate_succ_apply']
  exact h

/-! ### R6. `have h := hf a b` · context gains the instance of a `∀` hypothesis at `a`, `b` -/
example {X : Type} [MetricSpace X] (g : X → X) (k : ℝ) (a b : X)
    (hf : ∀ x y, dist (g x) (g y) ≤ k * dist x y) : dist (g a) (g b) ≤ k * dist a b := by
  have h := hf a b
  exact h

/-! ### R7. `gcongr` · goal `a * c ≤ b * c` → `a ≤ b` (the side goal `0 ≤ c` is found in the context)
It strips the common shape of both sides, here `· * c`, and leaves the part that differs. It closes
that goal too when a hypothesis states it (as `ih` does in the induction step). -/
example (a b c : ℝ) (hc : 0 ≤ c) (h : b = a + 1) : a * c ≤ b * c := by
  gcongr
  linarith

/-! ## Part 2 · from steps to a distance bound: telescoping and the geometric sum -/

/-! ### R8. `dist_le_Ico_sum_dist u hmn` · closes the triangle inequality along `u m, u (m+1), …, u n`
`Ico m n` is the finite set `{m, m+1, …, n-1}` (`Finset.Ico`). In a `calc` it is the first step. -/
example {X : Type} [MetricSpace X] (u : ℕ → X) (m n : ℕ) (hmn : m ≤ n) :
    dist (u m) (u n) ≤ ∑ i ∈ Ico m n, dist (u i) (u (i + 1)) := by
  exact dist_le_Ico_sum_dist u hmn

/-! ### R9. `Finset.sum_le_sum` · goal: `∑ f ≤ ∑ g` → termwise `∀ i ∈ s, f i ≤ g i` -/
example (s : Finset ℕ) (f g : ℕ → ℝ) (h : ∀ i ∈ s, f i ≤ g i) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i := by
  apply Finset.sum_le_sum
  exact h

/-! ### R10. `Finset.sum_mul` · `(∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a` · goal: pull a factor into a sum -/
example (s : Finset ℕ) (f : ℕ → ℝ) (a : ℝ) (P : ℝ → Prop) (h : P (∑ i ∈ s, f i * a)) :
    P ((∑ i ∈ s, f i) * a) := by
  rw [Finset.sum_mul]
  exact h

/-! ### R11. `geom_sum_Ico_le_of_lt_one` · `0 ≤ x → x < 1 → ∑ i ∈ Ico m n, x ^ i ≤ x ^ m / (1 - x)`
The tail of a geometric series is at most the infinite tail `x^m + x^(m+1) + … = x^m / (1 - x)`. -/
example (x : ℝ) (m n : ℕ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∑ i ∈ Ico m n, x ^ i ≤ x ^ m / (1 - x) := by
  exact geom_sum_Ico_le_of_lt_one hx0 hx1

/-! ## Part 3 · Cauchy: ε-N form and limits of bounds -/

/-! ### R12. `Metric.cauchySeq_iff'` · goal: `CauchySeq u` → `∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) (u N) < ε` -/
example {X : Type} [MetricSpace X] (u : ℕ → X)
    (h : ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) (u N) < ε) : CauchySeq u := by
  rw [Metric.cauchySeq_iff']
  exact h

/-! ### R13. `tendsto_pow_atTop_nhds_zero_of_lt_one` · `0 ≤ r → r < 1 → r ^ n → 0`
`Tendsto v atTop (𝓝 L)` reads "`v n → L` as `n → ∞`". -/
example (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (P : Prop)
    (hP : Tendsto (fun n => r ^ n) atTop (𝓝 0) → P) : P := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  exact hP h

/-! ### R14. `Filter.Tendsto.mul_const` · `v → a` gives `v n * b → a * b` · context -/
example (v : ℕ → ℝ) (a b : ℝ) (hv : Tendsto v atTop (𝓝 a)) (P : Prop)
    (hP : Tendsto (fun n => v n * b) atTop (𝓝 (a * b)) → P) : P := by
  have h := hv.mul_const b
  exact hP h

/-! ### R15. `Filter.Tendsto.div_const` · `v → a` gives `v n / b → a / b` · context -/
example (v : ℕ → ℝ) (a b : ℝ) (hv : Tendsto v atTop (𝓝 a)) (P : Prop)
    (hP : Tendsto (fun n => v n / b) atTop (𝓝 (a / b)) → P) : P := by
  have h := hv.div_const b
  exact hP h

/-! ### R16. `simpa using e` · closes the goal with `e` after `simp` cleans both: here `0 * b` → `0` -/
example (v : ℕ → ℝ) (b : ℝ) (e : Tendsto (fun n => v n * b) atTop (𝓝 (0 * b))) :
    Tendsto (fun n => v n * b) atTop (𝓝 0) := by
  simpa using e

/-! ### R17. `apply hv.eventually (p := fun y => y < ε)` (lemma `Filter.Tendsto.eventually`)
· goal: "eventually `v n < ε`" → "eventually `y < ε` for `y` near the limit `0`".
`∀ᶠ n in atTop, Q n` reads "`Q n` for all large `n`"; `∀ᶠ y in 𝓝 0, Q y`: "`Q y` for all `y` near 0".
`(p := …)` names the property; plain `apply hv.eventually` cannot guess it. Then
`gt_mem_nhds : b < a → ∀ᶠ x in 𝓝 b, x < a` (values near `b` stay below `a`) closes the new goal.
In one term: `hv.eventually (gt_mem_nhds hε) : ∀ᶠ n in atTop, v n < ε`. -/
example (v : ℕ → ℝ) (ε : ℝ) (hv : Tendsto v atTop (𝓝 0)) (hε : 0 < ε) :
    ∀ᶠ n in atTop, v n < ε := by
  apply hv.eventually (p := fun y => y < ε)
  exact gt_mem_nhds hε

/-! ### R18. `Filter.Eventually.exists_forall_of_atTop` · goal `∃ N, ∀ n ≥ N, Q n` → `∀ᶠ n in atTop, Q n`
Term form: `hQ.exists_forall_of_atTop : ∃ N, ∀ n ≥ N, Q n` for `hQ : ∀ᶠ n in atTop, Q n`. -/
example (Q : ℕ → Prop) (hQ : ∀ᶠ n in atTop, Q n) : ∃ N, ∀ n ≥ N, Q n := by
  apply Filter.Eventually.exists_forall_of_atTop
  exact hQ

/-! ### R19. `refine ⟨N, fun n hn => ?_⟩` · goal `∃ N, ∀ n ≥ N, Q n N` → context gains `n`, `hn`; goal `Q n N` -/
example (Q : ℕ → ℕ → Prop) (N : ℕ) (h : ∀ n, N ≤ n → Q n N) : ∃ M, ∀ n ≥ M, Q n M := by
  refine ⟨N, fun n hn => ?_⟩
  exact h n hn

/-! ### R20. `dist_comm` · `dist x y = dist y x` · goal: swap the arguments of `dist` -/
example {X : Type} [MetricSpace X] (x y : X) (P : ℝ → Prop) (h : P (dist y x)) : P (dist x y) := by
  rw [dist_comm]
  exact h

/-! ### R21. `h1.trans_lt h2` (lemma `LE.le.trans_lt`) · `a ≤ b → b < c → a < c` · closes the goal -/
example (a b c : ℝ) (h1 : a ≤ b) (h2 : b < c) : a < c := by
  exact h1.trans_lt h2

/-! ## Part 4 · two fixed points coincide -/

/-! ### R22. `rw [ha, hb] at h` · context: rewrite inside the hypothesis `h`, not the goal -/
example {X : Type} [MetricSpace X] (g : X → X) (a b : X) (k : ℝ) (ha : g a = b) (hb : g b = a)
    (h : dist (g a) (g b) ≤ k) : dist b a ≤ k := by
  rw [ha, hb] at h
  exact h

/-! ### R23. `dist_nonneg` · `0 ≤ dist x y` (implicit `x y`: write `dist_nonneg (x := a) (y := b)`) -/
example {X : Type} [MetricSpace X] (a b : X) (P : Prop) (hP : 0 ≤ dist a b → P) : P := by
  have h := dist_nonneg (x := a) (y := b)
  exact hP h

/-! ### R24. `nlinarith [t₁, …]` · closes a (non)linear inequality over `ℝ` from the context plus the
hint terms `tᵢ`; it multiplies pairs of hypotheses, so give it the sign facts it needs. -/
example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-! ### R25. `dist_le_zero` · `dist x y ≤ 0 ↔ x = y` · goal `x = y` → `dist x y ≤ 0` -/
example {X : Type} [MetricSpace X] (a b : X) (h : dist a b ≤ 0) : a = b := by
  apply dist_le_zero.mp
  exact h

/-! ## Part 5 · the theorem: limit of the iterates -/

/-! ### R26. `obtain ⟨x0⟩ := ‹Nonempty X›` · context gains a point `x0 : X`
`‹T›` is "the hypothesis of type `T`", here the instance `[Nonempty X]`. -/
example {X : Type} [Nonempty X] (P : Prop) (h : X → P) : P := by
  obtain ⟨x0⟩ := ‹Nonempty X›
  exact h x0

/-! ### R27. `cauchySeq_tendsto_of_complete` · `CauchySeq u → ∃ L, Tendsto u atTop (𝓝 L)` (needs `[CompleteSpace X]`) -/
example {X : Type} [MetricSpace X] [CompleteSpace X] (u : ℕ → X) (hu : CauchySeq u) (P : Prop)
    (hP : ∀ L, Tendsto u atTop (𝓝 L) → P) : P := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hu
  exact hP L hL

/-! ### R28. `tendsto_iff_dist_tendsto_zero` · `Tendsto u l (𝓝 a) ↔ Tendsto (fun n => dist (u n) a) l (𝓝 0)`
`rw [...] at hL ⊢` rewrites the hypothesis `hL` and the goal in one go. -/
example {X : Type} [MetricSpace X] (u w : ℕ → X) (a b : X) (hL : Tendsto u atTop (𝓝 a))
    (h : Tendsto (fun n => dist (u n) a) atTop (𝓝 0) → Tendsto (fun n => dist (w n) b) atTop (𝓝 0)) :
    Tendsto w atTop (𝓝 b) := by
  rw [tendsto_iff_dist_tendsto_zero] at hL ⊢
  exact h hL

/-! ### R29. `squeeze_zero` · goal `v → 0` → `0 ≤ v n`, `v n ≤ w n`, `w → 0` (sandwich, all in `ℝ`)
`(g := w)` names the upper sequence; it can be left out when the second argument already fixes it. -/
example (v w : ℕ → ℝ) (h0 : ∀ n, 0 ≤ v n) (h1 : ∀ n, v n ≤ w n) (hw : Tendsto w atTop (𝓝 0)) :
    Tendsto v atTop (𝓝 0) := by
  refine squeeze_zero (g := w) (fun n => ?_) (fun n => ?_) ?_
  exacts [h0 n, h1 n, hw]

/-! ### R30. `Filter.Tendsto.const_mul` · `v → a` gives `b * v n → b * a` · context -/
example (v : ℕ → ℝ) (a b : ℝ) (hv : Tendsto v atTop (𝓝 a)) (P : Prop)
    (hP : Tendsto (fun n => b * v n) atTop (𝓝 (b * a)) → P) : P := by
  have h := hv.const_mul b
  exact hP h

/-! ### R31. `simp only [← Function.iterate_succ_apply' g]` · goal: `g (g^[n] x)` → `g^[n.succ] x`,
also under a `fun n => …`, where `rw` cannot reach (R5 read right to left). `n.succ` is `n + 1`
by definition, so `exact` accepts a term about `g^[n + 1] x`. -/
example {X : Type} (g : X → X) (x : X) (Q : (ℕ → X) → Prop) (h : Q (fun n => g^[n + 1] x)) :
    Q (fun n => g (g^[n] x)) := by
  simp only [← Function.iterate_succ_apply' g]
  exact h

/-! ### R32. `tendsto_add_atTop_iff_nat` · `Tendsto (fun n => u (n + k)) atTop l ↔ Tendsto u atTop l`
· goal: the shifted sequence `u (n + 1)` → the sequence `u` (`apply (…).mpr` uses `←` of the `↔`).
Name the sequence with `(f := u)`: when the goal shows `g^[n.succ] x` instead of a literal `u (n + 1)`,
`apply` cannot guess `u`. (`exact (tendsto_add_atTop_iff_nat 1).mpr h` also works: `h` fixes `u`.) -/
example {X : Type} [MetricSpace X] (u : ℕ → X) (a : X) (h : Tendsto u atTop (𝓝 a)) :
    Tendsto (fun n => u (n + 1)) atTop (𝓝 a) := by
  apply (tendsto_add_atTop_iff_nat (f := u) 1).mpr
  exact h

/-! ### R33. `tendsto_nhds_unique` · `Tendsto v l (𝓝 a) → Tendsto v l (𝓝 b) → a = b` (limits are unique) -/
example {X : Type} [MetricSpace X] (u : ℕ → X) (a b : X) (ha : Tendsto u atTop (𝓝 a))
    (hb : Tendsto u atTop (𝓝 b)) : a = b := by
  exact tendsto_nhds_unique ha hb

/-! ### R34. `refine ⟨a, ha, fun y hy => ?_⟩` · goal `∃! x, Q x` → context gains `y`, `hy`; goal `y = a`
`∃! x, Q x` unfolds to `∃ x, Q x ∧ ∀ y, Q y → y = x`: a witness, its property, uniqueness.
`hy` prints as `(fun x => Q x) y`, which is `Q y` by definition (β-reduction). -/
example {X : Type} (Q : X → Prop) (a : X) (ha : Q a) (h : ∀ y, Q y → y = a) : ∃! x, Q x := by
  refine ⟨a, ha, fun y hy => ?_⟩
  exact h y hy

/-! # Part W · Worked combinations (real sequences, not the exercise's objects) -/

/-! ### W1. Induction + `calc` + `gcongr`: `u (n+1) ≤ r * u n` gives `u n ≤ r ^ n * u 0` (R1, R4, R7, R3) -/
example (u : ℕ → ℝ) (r : ℝ) (hr : 0 ≤ r) (hu : ∀ n, u (n + 1) ≤ r * u n) (n : ℕ) :
    u n ≤ r ^ n * u 0 := by
  induction n with
    | zero => simp
    | succ n ih =>
      calc u (n + 1) ≤ r * u n := hu n
        _ ≤ r * (r ^ n * u 0) := by gcongr
        _ = r ^ (n + 1) * u 0 := by ring

/-! ### W2. A bound that tends to 0, then ε-N (R13, R14, R16, R17, R18) -/
example (ε : ℝ) (hε : 0 < ε) : ∃ N, ∀ n ≥ N, (1 / 2 : ℝ) ^ n * 5 < ε := by
  have hlim : Tendsto (fun n => (1 / 2 : ℝ) ^ n * 5) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).mul_const 5
  exact (hlim.eventually (gt_mem_nhds hε)).exists_forall_of_atTop

/-! ### W3. Two limits of one sequence: `u (n+1) = c * u n` and `u → a` give `a = c * a` (R32, R30, R16, R33) -/
example (u : ℕ → ℝ) (a c : ℝ) (hu : ∀ n, u (n + 1) = c * u n) (ha : Tendsto u atTop (𝓝 a)) :
    a = c * a := by
  have h1 : Tendsto (fun n => u (n + 1)) atTop (𝓝 a) := (tendsto_add_atTop_iff_nat 1).mpr ha
  have h2 : Tendsto (fun n => u (n + 1)) atTop (𝓝 (c * a)) := by
    simp only [hu]
    exact ha.const_mul c
  exact tendsto_nhds_unique h1 h2

end H047Guide
