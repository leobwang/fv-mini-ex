/- H047 | Banach fixed-point theorem | 1-1.5 h | metric spaces, Cauchy sequences, geometric series, Filter.Tendsto, mathlib
GOAL
  A contraction `f` (`dist (f x) (f y) ≤ k * dist x y` with `0 ≤ k < 1`) on a nonempty complete
  metric space `X` has exactly one fixed point. Iterate `f` from any `x0`: the iterates are Cauchy
  (geometric bound), their limit is fixed, and two fixed points would satisfy `d ≤ k * d`.

REFERENCE
  -- `f^[n] x0`: `f` applied `n` times; `Tendsto u atTop (𝓝 L)`: `u n → L`; `Ico m n = {m, …, n-1}`; `∃! x, P x`: exactly one `x`
  #check Function.iterate_succ_apply'   -- f^[n.succ] x = f (f^[n] x)
  #check dist_le_Ico_sum_dist           -- m ≤ n → dist (u m) (u n) ≤ ∑ i ∈ Ico m n, dist (u i) (u (i + 1))
  #check geom_sum_Ico_le_of_lt_one      -- 0 ≤ x → x < 1 → ∑ i ∈ Ico m n, x ^ i ≤ x ^ m / (1 - x)
  #check Metric.cauchySeq_iff'          -- CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) (u N) < ε
  #check cauchySeq_tendsto_of_complete  -- CauchySeq u → ∃ L, Tendsto u atTop (𝓝 L)
  #check tendsto_pow_atTop_nhds_zero_of_lt_one  -- 0 ≤ r → r < 1 → Tendsto (fun n => r ^ n) atTop (𝓝 0)
  #check tendsto_iff_dist_tendsto_zero  -- Tendsto u l (𝓝 a) ↔ Tendsto (fun n => dist (u n) a) l (𝓝 0)
  #check squeeze_zero                   -- (∀ t, 0 ≤ g t) → (∀ t, g t ≤ h t) → Tendsto h l (𝓝 0) → Tendsto g l (𝓝 0)
  #check tendsto_add_atTop_iff_nat      -- (k : ℕ) : Tendsto (fun n => u (n + k)) atTop l ↔ Tendsto u atTop l
  #check tendsto_nhds_unique            -- Tendsto u l (𝓝 a) → Tendsto u l (𝓝 b) → a = b
  example (u : ℕ → ℝ) (h : Tendsto u atTop (𝓝 0)) (ε : ℝ) (hε : 0 < ε) : ∃ N, ∀ n ≥ N, u n < ε := (h.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
BANNED: ContractingWith.exists_fixedPoint, ContractingWith.fixedPoint, ContractingWith.efixedPoint, ContractingWith.fixedPoint_unique, ContractingWith.fixedPoint_isFixedPt, ContractingWith.tendsto_iterate_fixedPoint, ContractingWith, LipschitzWith, cauchySeq_of_le_geometric, cauchySeq_of_le_geometric_two, cauchySeq_of_edist_le_geometric, cauchySeq_of_edist_le_geometric_two, dist_le_of_le_geometric_of_tendsto, dist_le_of_le_geometric_of_tendsto₀, dist_le_of_le_geometric_two_of_tendsto, dist_le_of_le_geometric_two_of_tendsto₀, aux_hasSum_of_le_geometric, cauchy_series_of_le_geometric, LipschitzWith.dist_iterate_succ_le_geometric, LipschitzWith.edist_iterate_succ_le_geometric, isFixedPt_of_tendsto_iterate, cauchySeq_of_dist_le_of_summable, cauchySeq_of_summable_dist, cauchySeq_of_edist_le_of_summable
-/
import Mathlib

namespace H047

open Filter Topology Finset

-- MILESTONE (optional: change or delete)
theorem iterate_step {X : Type*} [MetricSpace X] (f : X → X) (k : ℝ) (hk0 : 0 ≤ k)
    (hf : ∀ x y, dist (f x) (f y) ≤ k * dist x y) (x0 : X) (n : ℕ) :
    dist (f^[n] x0) (f^[n + 1] x0) ≤ k ^ n * dist x0 (f x0) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem iterate_dist {X : Type*} [MetricSpace X] (f : X → X) (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hf : ∀ x y, dist (f x) (f y) ≤ k * dist x y) (x0 : X) {m n : ℕ} (hmn : m ≤ n) :
    dist (f^[m] x0) (f^[n] x0) ≤ k ^ m * dist x0 (f x0) / (1 - k) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem iterate_cauchy {X : Type*} [MetricSpace X] (f : X → X) (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hf : ∀ x y, dist (f x) (f y) ≤ k * dist x y) (x0 : X) :
    CauchySeq (fun n => f^[n] x0) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem fixed_unique {X : Type*} [MetricSpace X] (f : X → X) (k : ℝ) (hk1 : k < 1)
    (hf : ∀ x y, dist (f x) (f y) ≤ k * dist x y) (x y : X) (hx : f x = x) (hy : f y = y) :
    x = y := by
  sorry

-- BEGIN SPEC
theorem banach_fixed_point {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (f : X → X) (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hf : ∀ x y, dist (f x) (f y) ≤ k * dist x y) : ∃! x, f x = x :=
-- END SPEC
  sorry

end H047

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Fix `x0` (`obtain ⟨x0⟩ := ‹Nonempty X›`) and study `x n = f^[n] x0`. Consecutive distances shrink like `k ^ n`; summing a geometric series bounds `dist (x m) (x n)` by `k ^ m * d0 / (1 - k)`, which tends to `0`.
H2. Step bound by `induction n` (rewrite `f^[n + 2] x0 = f (f^[n + 1] x0)` with `Function.iterate_succ_apply'`, apply `hf`, then `gcongr`). The limit `L` exists by completeness; `f (x n) → f L` by `squeeze_zero` with `hf (x n) L`, and `f (x n) = x (n + 1) → L` by `tendsto_add_atTop_iff_nat 1`; uniqueness of limits gives `f L = L`.
H3. Distance bound: `calc dist (x m) (x n) ≤ ∑ i ∈ Ico m n, dist (x i) (x (i + 1)) := dist_le_Ico_sum_dist _ hmn; _ ≤ ∑ i ∈ Ico m n, k ^ i * d0 := sum_le_sum fun i _ => iterate_step ..; _ = (∑ i ∈ Ico m n, k ^ i) * d0 := by rw [sum_mul]; _ ≤ k ^ m / (1 - k) * d0 := by gcongr; exact geom_sum_Ico_le_of_lt_one hk0 hk1`. The bound tends to 0 by `((tendsto_pow_atTop_nhds_zero_of_lt_one hk0 hk1).mul_const d0).div_const (1 - k)`. For `∃!`: `refine ⟨L, hfix, fun y hy => fixed_unique ..⟩`.
-/
