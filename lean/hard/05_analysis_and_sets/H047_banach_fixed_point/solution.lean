/- H047 | Banach fixed-point theorem | 1-1.5 h | metric spaces, Cauchy sequences, geometric series, Filter.Tendsto, mathlib
GOAL
  A contraction `f` (`dist (f x) (f y) ≤ k * dist x y` with `0 ≤ k < 1`) on a nonempty complete
  metric space `X` has exactly one fixed point. Iterate `f` from any `x0`: the iterates are Cauchy
  (geometric bound), their limit is fixed, and two fixed points would satisfy `d ≤ k * d`.
BANNED: ContractingWith.exists_fixedPoint, ContractingWith.fixedPoint, ContractingWith.efixedPoint, ContractingWith.fixedPoint_unique, ContractingWith.fixedPoint_isFixedPt, ContractingWith.tendsto_iterate_fixedPoint, ContractingWith, LipschitzWith, cauchySeq_of_le_geometric, cauchySeq_of_le_geometric_two, cauchySeq_of_edist_le_geometric, cauchySeq_of_edist_le_geometric_two, dist_le_of_le_geometric_of_tendsto, dist_le_of_le_geometric_of_tendsto₀, dist_le_of_le_geometric_two_of_tendsto, dist_le_of_le_geometric_two_of_tendsto₀, aux_hasSum_of_le_geometric, cauchy_series_of_le_geometric, LipschitzWith.dist_iterate_succ_le_geometric, LipschitzWith.edist_iterate_succ_le_geometric, isFixedPt_of_tendsto_iterate, cauchySeq_of_dist_le_of_summable, cauchySeq_of_summable_dist, cauchySeq_of_edist_le_of_summable

GUIDE
  Entries R1–R34: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H047

open Filter Topology Finset

/- SKELETON · iterate_step   (MILESTONE: prove it first; used by iterate_dist, step b)
  1. Induction on `n`:                                                          R1
  2. zero: `f^[0] x0`, `f^[0 + 1] x0` and `k ^ 0 * d` simplify away:              simp (R2, R3)
  3. succ: a `calc` from `dist (f^[n + 1] x0) (f^[n + 1 + 1] x0)`:              R4
       = the same with the outer `f` peeled off both iterates                   R5
         (as `simp only [...]`: it rewrites both sides fully; `rw` stops halfway)
       ≤ `k *` the previous distance                                            R6 (`hf _ _`)
       ≤ `k * (k ^ n * dist x0 (f x0))`  (needs `ih`, `hk0`)                     R7
       = `k ^ (n + 1) * dist x0 (f x0)`                                         ring
-/
-- MILESTONE (optional: change or delete)
theorem iterate_step {X : Type*} [MetricSpace X] (f : X → X) (k : ℝ) (hk0 : 0 ≤ k)
    (hf : ∀ x y, dist (f x) (f y) ≤ k * dist x y) (x0 : X) (n : ℕ) :
    dist (f^[n] x0) (f^[n + 1] x0) ≤ k ^ n * dist x0 (f x0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc dist (f^[n + 1] x0) (f^[n + 1 + 1] x0) = dist (f (f^[n] x0)) (f (f^[n + 1] x0)) := by
          simp only [Function.iterate_succ_apply']
      _ ≤ k * dist (f^[n] x0) (f^[n + 1] x0) := hf _ _
      _ ≤ k * (k ^ n * dist x0 (f x0)) := by gcongr
      _ = k ^ (n + 1) * dist x0 (f x0) := by ring

/- SKELETON · iterate_dist   (MILESTONE: uses iterate_step; used by iterate_cauchy, step 5)
  Write `d0` for `dist x0 (f x0)`. One `calc` from `dist (f^[m] x0) (f^[n] x0)`:  R4
    a. ≤ the sum over `Ico m n` of consecutive distances                        R8 (`u := fun i => f^[i] x0`)
    b. ≤ `∑ i ∈ Ico m n, k ^ i * d0`                                             R9, then iterate_step at `i`
    c. = `(∑ i ∈ Ico m n, k ^ i) * d0`                                           R10
    d. ≤ `k ^ m / (1 - k) * d0`                                                  R7, then R11
    e. = the goal's right-hand side                                             ring
-/
-- MILESTONE (optional: change or delete)
theorem iterate_dist {X : Type*} [MetricSpace X] (f : X → X) (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hf : ∀ x y, dist (f x) (f y) ≤ k * dist x y) (x0 : X) {m n : ℕ} (hmn : m ≤ n) :
    dist (f^[m] x0) (f^[n] x0) ≤ k ^ m * dist x0 (f x0) / (1 - k) := by
  calc dist (f^[m] x0) (f^[n] x0)
      ≤ ∑ i ∈ Ico m n, dist (f^[i] x0) (f^[i + 1] x0) := dist_le_Ico_sum_dist (fun i => f^[i] x0) hmn
    _ ≤ ∑ i ∈ Ico m n, k ^ i * dist x0 (f x0) :=
        sum_le_sum fun i _ => iterate_step f k hk0 hf x0 i
    _ = (∑ i ∈ Ico m n, k ^ i) * dist x0 (f x0) := by rw [sum_mul]
    _ ≤ k ^ m / (1 - k) * dist x0 (f x0) := by
        gcongr
        exact geom_sum_Ico_le_of_lt_one hk0 hk1
    _ = k ^ m * dist x0 (f x0) / (1 - k) := by ring

/- SKELETON · iterate_cauchy   (MILESTONE: uses iterate_dist; used by banach_fixed_point, step 2)
  1. Go to ε-N form, then `intro ε hε`:                                         R12
  2. Fact first: `hlim : Tendsto (fun m => k ^ m * dist x0 (f x0) / (1 - k)) atTop (𝓝 0)`
       proof: R13 → R14 → R15 → R16
  3. `obtain ⟨N, hN⟩` from `hlim` and `hε`: "eventually below ε" → an explicit N: R17 → R18
  4. Witness `N`, introduce `n hn`:                                             R19
  5. Swap the distance, then iterate_dist at `hn`, then `hN` at `N`:             R20, R21
-/
-- MILESTONE (optional: change or delete)
theorem iterate_cauchy {X : Type*} [MetricSpace X] (f : X → X) (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hf : ∀ x y, dist (f x) (f y) ≤ k * dist x y) (x0 : X) :
    CauchySeq (fun n => f^[n] x0) := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have hlim : Tendsto (fun m => k ^ m * dist x0 (f x0) / (1 - k)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hk0 hk1).mul_const
      (dist x0 (f x0))).div_const (1 - k)
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_comm]
  exact (iterate_dist f k hk0 hk1 hf x0 hn).trans_lt (hN N le_rfl)

/- SKELETON · fixed_unique   (MILESTONE: used by banach_fixed_point, step 6)
  1. Instantiate the contraction at the two points:                             R6
  2. Rewrite with `hx`, `hy` inside it: `h : dist x y ≤ k * dist x y`:          R22
  3. Fact: `dist x y ≤ 0`, by nonlinear arithmetic with a sign hint:            R24 with R23
  4. Distance ≤ 0 → equal:                                                      R25
-/
-- MILESTONE (optional: change or delete)
theorem fixed_unique {X : Type*} [MetricSpace X] (f : X → X) (k : ℝ) (hk1 : k < 1)
    (hf : ∀ x y, dist (f x) (f y) ≤ k * dist x y) (x y : X) (hx : f x = x) (hy : f y = y) :
    x = y := by
  have h := hf x y
  rw [hx, hy] at h
  -- WHY: `d ≤ k * d` with `k < 1` forces `d ≤ 0`; `nlinarith` needs `0 ≤ d` as a hint.
  have : dist x y ≤ 0 := by nlinarith [dist_nonneg (x := x) (y := y)]
  exact dist_le_zero.mp this

/- SKELETON · banach_fixed_point
  Prove the MILESTONES first: iterate_step → iterate_dist → iterate_cauchy, and fixed_unique.
  1. A starting point `x0`:                                                     R26
  2. The iterates converge: `obtain ⟨L, hL⟩` from iterate_cauchy:               R27
  3. Fact `hfL : Tendsto (fun n => f (f^[n] x0)) atTop (𝓝 (f L))`:
       distances (R28), sandwich (R29; its first two arguments are R23 and R6), and
       the upper bound `k * dist (f^[n] x0) L → k * 0` (R30 → R16)
  4. Fact `hshift : Tendsto (fun n => f (f^[n] x0)) atTop (𝓝 L)`:               R31 → R32
       (after R31, give R32 the sequence: `(f := fun n => f^[n] x0)`, or pass `hL` to `.mpr`)
  5. `hfix : f L = L`: one sequence, two limits:                                R33
  6. Package `∃!` with fixed_unique for uniqueness:                             R34
-/
-- BEGIN SPEC
theorem banach_fixed_point {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (f : X → X) (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hf : ∀ x y, dist (f x) (f y) ≤ k * dist x y) : ∃! x, f x = x :=
-- END SPEC
  by
    obtain ⟨x0⟩ := ‹Nonempty X›
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (iterate_cauchy f k hk0 hk1 hf x0)
    have hfL : Tendsto (fun n => f (f^[n] x0)) atTop (𝓝 (f L)) := by
      rw [tendsto_iff_dist_tendsto_zero] at hL ⊢
      refine squeeze_zero (fun n => dist_nonneg) (fun n => hf _ L) ?_
      simpa using hL.const_mul k
    have hshift : Tendsto (fun n => f (f^[n] x0)) atTop (𝓝 L) := by
      simp only [← Function.iterate_succ_apply' f]
      exact (tendsto_add_atTop_iff_nat 1).mpr hL
    have hfix : f L = L := tendsto_nhds_unique hfL hshift
    exact ⟨L, hfix, fun y hy => fixed_unique f k hk1 hf y L hy hfix⟩

end H047

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Fix `x0` (`obtain ⟨x0⟩ := ‹Nonempty X›`, R26) and study `x n = f^[n] x0`. Consecutive distances
    shrink like `k ^ n` (iterate_step); the triangle inequality plus a geometric sum bounds
    `dist (x m) (x n)` by `k ^ m * d0 / (1 - k)` (iterate_dist), and that bound tends to `0`.
H2. iterate_step: `induction n`, then a `calc` that peels the outer `f` with
    `Function.iterate_succ_apply'` (R5), applies `hf`, and finishes with `gcongr` and `ring`.
    The limit `L` exists by completeness (R27). `f (x n) → f L` by `squeeze_zero` with `hf (x n) L`
    after `rw [tendsto_iff_dist_tendsto_zero] at hL ⊢` (R28, R29); `f (x n) = x (n + 1) → L` by
    `tendsto_add_atTop_iff_nat 1` (R31, R32); `tendsto_nhds_unique` gives `f L = L` (R33).
H3. iterate_dist: `calc dist (x m) (x n) ≤ ∑ i ∈ Ico m n, dist (x i) (x (i + 1)) := dist_le_Ico_sum_dist _ hmn`,
    `_ ≤ ∑ i ∈ Ico m n, k ^ i * d0 := sum_le_sum fun i _ => iterate_step ..`, `_ = (∑ i ∈ Ico m n, k ^ i) * d0`
    by `rw [sum_mul]`, `_ ≤ k ^ m / (1 - k) * d0` by `gcongr; exact geom_sum_Ico_le_of_lt_one hk0 hk1`.
    The bound tends to 0 by `simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hk0 hk1).mul_const d0).div_const (1 - k)`;
    then `obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hε)).exists_forall_of_atTop`.
    fixed_unique: `nlinarith [dist_nonneg (x := x) (y := y)]` gives `dist x y ≤ 0`.
    For `∃!`: `exact ⟨L, hfix, fun y hy => fixed_unique ..⟩`.
-/
