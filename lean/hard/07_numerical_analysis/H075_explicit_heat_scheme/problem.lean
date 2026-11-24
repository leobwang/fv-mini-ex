/- H075 | Explicit heat scheme: stability, instability, convergence | 45-75 min | finite differences, PDE, maximum principle, Function.iterate, zpow, Lax, mathlib
GOAL
  The explicit (FTCS) scheme for u_t = u_xx on the grid ℤ is uⱼ ← r·uⱼ₋₁ + (1−2r)·uⱼ + r·uⱼ₊₁, with
  r = Δt/Δx². (1) If 0 ≤ r ≤ 1/2, a bound |u| ≤ M holds forever (discrete maximum principle). (2) If
  r > 1/2, the checkerboard (−1)ʲε blows up. (3) Lax: local error ≤ τ per step ⇒ global error ≤ n·τ.

GUIDE
  Entries R1–R30: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib
open Filter

namespace H075

-- BEGIN SPEC
/-- one step of the explicit heat scheme on the infinite grid ℤ, with r = Δt/Δx² -/
def heatStep (r : ℝ) (u : ℤ → ℝ) : ℤ → ℝ :=
  fun j => r * u (j - 1) + (1 - 2 * r) * u j + r * u (j + 1)
-- END SPEC

/- SKELETON · step_bound   (milestone; prove it FIRST: heat_stable and heat_lax both use it)
  1. The bound at the three stencil points j - 1, j, j + 1:                           R1 (three times)
  2. The middle weight is nonnegative, hm : 0 ≤ 1 - 2 * r:                            R2
  3. Unfold the step:                                                                 R3
  4. A four-link chain |r·u₋ + (1−2r)·u₀ + r·u₊| ≤ … ≤ M, where u₋ = u (j - 1),
     u₀ = u j, u₊ = u (j + 1):                                                       R4
       ≤ |r·u₋| + |(1−2r)·u₀| + |r·u₊|            (triangle inequality)              R5
       = r·|u₋| + (1−2r)·|u₀| + r·|u₊|           (three abs_mul, then hr0, hm)       R6, R7
       ≤ r·M + (1−2r)·M + r·M                    (h1 h2 h3 hr0 hm are in context)    R8
       = M                                                                            ring
-/
-- MILESTONE (optional: change or delete)
theorem step_bound (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (u : ℤ → ℝ) (M : ℝ)
    (hu : ∀ j, |u j| ≤ M) (j : ℤ) : |heatStep r u j| ≤ M := by
  sorry

/- SKELETON · checkerboard   (milestone; heat_unstable uses it)
  1. Induction on n (a statement about whole functions: nothing to generalize):       R16
  2. zero: both sides at n = 0 are the start vector:                                  simp (R9)
  3. succ: peel the last step, then use the IH:                                       R10, rw [ih]
  4. Compare the two functions pointwise and unfold the step:                         funext j, R11
  5. Write the zpows at j - 1 and j + 1 through (-1) ^ j, each with the side
     fact (-1 : ℝ) ≠ 0 given as (by norm_num); split (1 - 4r)^(n+1):                  R12, R13, R14
  6. Close the identity (ring evaluates (-1)⁻¹):                                      R15
-/
-- MILESTONE (optional: change or delete)
theorem checkerboard (r ε : ℝ) (n : ℕ) :
    (heatStep r)^[n] (fun j => (-1 : ℝ) ^ j * ε) = fun j => (1 - 4 * r) ^ n * ((-1 : ℝ) ^ j * ε) := by
  sorry

/- SKELETON · step_sub   (milestone; heat_lax uses it: the step is linear)
  1. Unfold the step on both sides:                                                   R11
  2. Close the identity:                                                              ring
-/
-- MILESTONE (optional: change or delete)
theorem step_sub (r : ℝ) (u v : ℤ → ℝ) (j : ℤ) :
    heatStep r u j - heatStep r v j = heatStep r (fun k => u k - v k) j := by
  sorry

/- SKELETON · heat_stable
  0. Prove the milestone step_bound first (used in step 3).
  1. Induction on n, with an IH for every grid point j:                               R16
  2. zero: `(heatStep r)^[0] u j` is `u j` definitionally:                            R9, exact hu j
  3. succ: peel the last step; apply step_bound, letting Lean find its `u`
     from the IH (`_` in place of `u`):                                               R10, R17
-/
-- BEGIN SPEC
theorem heat_stable (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (u : ℤ → ℝ) (M : ℝ)
    (hu : ∀ j, |u j| ≤ M) (n : ℕ) (j : ℤ) : |(heatStep r)^[n] u j| ≤ M :=
-- END SPEC
  sorry

/- SKELETON · heat_unstable
  0. Prove the milestone checkerboard first (used in step 2).
  1. The growth factor, h1 : 1 < |1 - 4 * r|: drop the |·| using 1 - 4r < 0
     (from hr, proved inline as (by linarith)), then the linear bound:               R18, R2
  2. Inside `fun n => …`: rewrite with checkerboard, evaluate (-1) ^ 0, split |·|;
     the goal becomes Tendsto (fun n => |1 - 4 * r| ^ n * |ε|) atTop atTop:            R19 with checkerboard, R20, R21, R6, R22
  3. |1 - 4r| ^ n → +∞, then times the positive constant |ε|:                         R23 (h1), R24 with R25 (hε)
-/
-- BEGIN SPEC
theorem heat_unstable (r : ℝ) (hr : 1 / 2 < r) (ε : ℝ) (hε : ε ≠ 0) :
    Tendsto (fun n => |(heatStep r)^[n] (fun j => (-1 : ℝ) ^ j * ε) 0|) atTop atTop :=
-- END SPEC
  sorry

/- SKELETON · heat_lax
  0. Prove the milestones step_bound and step_sub first (used in steps 4 and 5).
  1. Induction on n, with an IH for every grid point j:                               R16
  2. zero: the goal |U 0 j - (heatStep r)^[0] (U 0) j| ≤ ↑0 * τ is |x - x| ≤ ↑0 * τ
     once f^[0] x = x:                                                               R26 (with R9)
  3. succ: peel the last step and name the scheme's value V := (heatStep r)^[n] (U 0);
     ih becomes ∀ j, |U n j - V j| ≤ ↑n * τ:                                          R10, R27
  4. Stability carries the old error: hb from step_bound with M := ↑n * τ and ih,
     u inferred as fun j => U n j - V j:                                             R17
  5. Write S = heatStep r. A four-link chain for |U (n + 1) j - S V j|:                R4
       = |(U (n+1) j − S(U n) j) + (S(U n) j − S V j)|                               R28
       ≤ |U (n+1) j − S(U n) j| + |S(U n) j − S V j|                                  R29
       ≤ τ + ↑n * τ        rw [step_sub] turns the second term into hb's; then         R8, exact hU n j
       = ↑(n + 1) * τ                                                                 R30, ring
-/
-- BEGIN SPEC
theorem heat_lax (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (U : ℕ → ℤ → ℝ) (τ : ℝ)
    (hU : ∀ n j, |U (n + 1) j - heatStep r (U n) j| ≤ τ) (n : ℕ) (j : ℤ) :
    |U n j - (heatStep r)^[n] (U 0) j| ≤ n * τ :=
-- END SPEC
  sorry

end H075

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. For 0 ≤ r ≤ 1/2 the weights r, 1 − 2r, r are ≥ 0 and sum to 1: one step is an average and cannot
    raise the sup (`step_bound`, R5–R8). For r > 1/2 the checkerboard (−1)ʲ is an eigenvector of the step
    with eigenvalue 1 − 4r < −1, so |1 − 4r|ⁿ → ∞. Lax: the error after n + 1 steps is the new local error
    (≤ τ) plus the old error pushed through one step, and a step does not increase a sup (`step_bound` again).
H2. `heat_stable` and `heat_lax`: `induction n generalizing j` (R16), peel the last step with
    `rw [Function.iterate_succ_apply']` (R10), then `step_bound` on the IH (R17). `checkerboard`: induction,
    `rw [Function.iterate_succ_apply', ih]`, `funext j`, `simp only [heatStep]`, rewrite `(-1) ^ (j ∓ 1)`
    with R12, R13, `pow_succ`, `ring`. `heat_unstable`: `simp_rw` (R19) down to `|1 - 4 * r| ^ n * |ε|`,
    then R23, R24. `heat_lax` succ: `set V := (heatStep r)^[n] (U 0)` (R27) and split
    U(n+1) − S V = [U(n+1) − S(U n)] + [S(U n) − S V] with S = `heatStep r`.
H3. `step_bound`: `calc` with `abs_add_three _ _ _`, then
    `rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hr0, abs_of_nonneg hm]`, `gcongr`, `ring`.
    `checkerboard` succ: `rw [zpow_sub_one₀ (by norm_num), zpow_add_one₀ (by norm_num), pow_succ]; ring`.
    `heat_unstable`: `h1 : 1 < |1 - 4 * r|` by `rw [abs_of_neg (by linarith)]; linarith`; then
    `simp_rw [checkerboard, zpow_zero, one_mul, abs_mul, abs_pow]` and
    `exact (tendsto_pow_atTop_atTop_of_one_lt h1).atTop_mul_const (abs_pos.mpr hε)`.
    `heat_lax` succ: `have hb := step_bound r hr0 hr _ (n * τ) ih j`; the `≤ τ + n * τ` link is
    `by rw [step_sub]; gcongr; exact hU n j`; the last link is `by push_cast; ring`.
-/
