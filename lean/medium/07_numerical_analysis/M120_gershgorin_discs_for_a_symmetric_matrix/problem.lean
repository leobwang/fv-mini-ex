/- M120 | Gershgorin discs for a symmetric matrix | 5-10 min | Matrix, eigenvalue, Gershgorin, fin_cases, mathlib
GOAL
  Use the Gershgorin circle theorem to show that every eigenvalue `μ` of the symmetric matrix `A`
  below lies in `[2, 6]` (so 0 is not an eigenvalue and `A` is invertible).

GUIDE
  Entries R1–R10: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M120

-- BEGIN SPEC
def A : Matrix (Fin 3) (Fin 3) ℝ := !![4, 1, 0; 1, 4, 1; 0, 1, 5]
-- END SPEC

/- SKELETON · eigenvalue_bounds
  1. Gershgorin: get the row `k` whose disc contains `μ`:                   R1
       hk : μ ∈ Metric.closedBall (A k k) (∑ j ∈ Finset.univ.erase k, ‖A k j‖)
  2. Disc → inequality, once, before splitting:                             R2, R3 (one `rw … at hk`)
       hk : |μ - A k k| ≤ ∑ j ∈ Finset.univ.erase k, ‖A k j‖
  3. One goal per row, chained with `<;>`:                                  R4
  4. Evaluate center and radius to numbers in each `hk`
     (one `simp … at hk`; R6, R7 are automatic, R8 must be named):          R5 → R6 → R7 → R8
  5. Split `2 ≤ μ ∧ μ ≤ 6`:                                                 constructor
  6. Each bound from that row's `|μ - c| ≤ r`:                              R9 → R10
-/
-- BEGIN SPEC
theorem eigenvalue_bounds (μ : ℝ) (hμ : Module.End.HasEigenvalue (Matrix.toLin' A) μ) :
    2 ≤ μ ∧ μ ≤ 6 :=
-- END SPEC
  sorry

end M120

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Gershgorin hands you one row `k` whose disc (center `A k k`, radius = the sum of the other `|A k j|`)
    contains `μ`. Each of the three rows' discs lies inside `[2, 6]`, so check the rows one by one.
H2. `obtain ⟨k, hk⟩ := eigenvalue_mem_ball hμ`, then `rw [Metric.mem_closedBall, Real.dist_eq] at hk`
    gives `|μ - A k k| ≤ radius`. Then `fin_cases k`, evaluate `hk` with `simp`, split the goal, and get
    each bound from `abs_le`.
H3. `fin_cases k <;> simp [A, Fin.sum_univ_succ] at hk` leaves the three discs `|μ - 4| ≤ 1`,
    `|μ - 4| ≤ 2` (printed unnormalised as `1 + (4 + 1) - 4`), `|μ - 5| ≤ 1`. After `constructor`, each
    half is `linarith [abs_le.mp hk]`.
-/
