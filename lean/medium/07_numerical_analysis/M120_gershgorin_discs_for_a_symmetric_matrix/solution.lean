/- M120 | Gershgorin discs for a symmetric matrix | 5-10 min | Matrix, eigenvalue, Gershgorin, fin_cases, mathlib
GOAL
  Use the Gershgorin circle theorem to show that every eigenvalue `μ` of the symmetric matrix `A`
  below lies in `[2, 6]` (so 0 is not an eigenvalue and `A` is invertible).

REFERENCE
  #check eigenvalue_mem_ball     -- HasEigenvalue (toLin' A) μ → ∃ k, μ ∈ closedBall (A k k) (∑ j ∈ univ.erase k, ‖A k j‖)
  #check Metric.mem_closedBall   -- y ∈ closedBall x r ↔ dist y x ≤ r
  #check Real.dist_eq            -- dist x y = |x - y|
  #check Real.norm_eq_abs        -- ‖r‖ = |r|   (on ℝ the norm in the radius is the absolute value)
  #check abs_le                  -- |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
  #check Finset.sum_erase_eq_sub -- a ∈ s → ∑ x ∈ s.erase a, f x = ∑ x ∈ s, f x - f a
  #check Fin.sum_univ_succ       -- ∑ i : Fin (n + 1), f i = f 0 + ∑ i : Fin n, f i.succ
  example : (!![4, 1; 1, 4] : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 1 := rfl  -- `!![…; …]` lists rows; entry `A i j`
  `fin_cases k` splits `k : Fin 3` into the cases `k = 0, 1, 2`; `simp [A, …] at hk` then evaluates entries.
NOTE: `Matrix.toLin' A` is `x ↦ A *ᵥ x`; `HasEigenvalue f μ`: some `v ≠ 0` has `f v = μ • v`. `A` is symmetric, so every eigenvalue is real.
-/
import Mathlib

namespace M120

-- BEGIN SPEC
def A : Matrix (Fin 3) (Fin 3) ℝ := !![4, 1, 0; 1, 4, 1; 0, 1, 5]
-- END SPEC

-- BEGIN SPEC
theorem eigenvalue_bounds (μ : ℝ) (hμ : Module.End.HasEigenvalue (Matrix.toLin' A) μ) :
    2 ≤ μ ∧ μ ≤ 6 :=
-- END SPEC
  by
    obtain ⟨k, hk⟩ := eigenvalue_mem_ball hμ
    rw [Metric.mem_closedBall, Real.dist_eq] at hk
    -- the three discs: |μ - 4| ≤ 1, |μ - 4| ≤ 2, |μ - 5| ≤ 1
    fin_cases k <;> simp [A, Finset.sum_erase_eq_sub, Fin.sum_univ_succ] at hk <;>
      constructor <;> linarith [abs_le.mp hk]

end M120

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Gershgorin hands you one row `k` whose disc (center `A k k`, radius = sum of the other `|A k j|`) contains `μ`.
H2. `obtain ⟨k, hk⟩ := eigenvalue_mem_ball hμ`, rewrite `hk` to `|μ - A k k| ≤ radius`, then check the three rows separately.
H3. After `fin_cases k`, `simp [A, …] at hk` with the two sum lemmas from the card leaves the three discs `|μ - 4| ≤ 1`, `|μ - 4| ≤ 2` (maybe unnormalised), `|μ - 5| ≤ 1`; `abs_le` turns each into two linear facts.
-/
