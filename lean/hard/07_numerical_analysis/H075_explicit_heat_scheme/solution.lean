/- H075 | Explicit heat scheme: stability, instability, convergence | 45-75 min | finite differences, PDE, maximum principle, Function.iterate, zpow, Lax, mathlib
GOAL
  The explicit (FTCS) scheme for u_t = u_xx on the grid ℤ is uⱼ ← r·uⱼ₋₁ + (1−2r)·uⱼ + r·uⱼ₊₁, with
  r = Δt/Δx². (1) If 0 ≤ r ≤ 1/2, a bound |u| ≤ M holds forever (discrete maximum principle). (2) If
  r > 1/2, the checkerboard (−1)ʲε blows up. (3) Lax: local error ≤ τ per step ⇒ global error ≤ n·τ.

REFERENCE
  #check abs_add_three                     -- |a + b + c| ≤ |a| + |b| + |c|
  #check abs_mul                           -- |a * b| = |a| * |b|     (also abs_of_nonneg, abs_of_neg, abs_pow)
  #check Function.iterate_succ_apply'      -- f^[n.succ] x = f (f^[n] x);  `f^[n]` is f applied n times
  #check zpow_add_one₀                     -- a ≠ 0 → a ^ (n + 1) = a ^ n * a  (n : ℤ; also zpow_sub_one₀ with a⁻¹)
  #check tendsto_pow_atTop_atTop_of_one_lt -- 1 < r → Tendsto (fun n => r ^ n) atTop atTop, i.e. r ^ n → +∞
  -- (`Tendsto f atTop atTop` means f n → +∞ as n → ∞)
  #check Filter.Tendsto.atTop_mul_const    -- 0 < r → Tendsto f l atTop → Tendsto (fun x => f x * r) l atTop
  example (a b c x y : ℝ) (ha : 0 ≤ a) (h : x ≤ y) : a * x + b ≤ a * y + b := by gcongr
  -- `induction n generalizing j with | zero => .. | succ n ih => ..` gives an IH for every grid point j
NOTE: `(-1 : ℝ) ^ j` with `j : ℤ` is zpow. `U n j` is the exact solution at time step n, grid point j; ℤ has no boundary.
-/
import Mathlib
open Filter

namespace H075

-- BEGIN SPEC
/-- one step of the explicit heat scheme on the infinite grid ℤ, with r = Δt/Δx² -/
def heatStep (r : ℝ) (u : ℤ → ℝ) : ℤ → ℝ :=
  fun j => r * u (j - 1) + (1 - 2 * r) * u j + r * u (j + 1)
-- END SPEC

-- MILESTONE (optional: change or delete)
theorem step_bound (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (u : ℤ → ℝ) (M : ℝ)
    (hu : ∀ j, |u j| ≤ M) (j : ℤ) : |heatStep r u j| ≤ M := by
  have h1 := hu (j - 1)
  have h2 := hu j
  have h3 := hu (j + 1)
  have hm : 0 ≤ 1 - 2 * r := by linarith
  unfold heatStep
  calc |r * u (j - 1) + (1 - 2 * r) * u j + r * u (j + 1)|
      ≤ |r * u (j - 1)| + |(1 - 2 * r) * u j| + |r * u (j + 1)| := abs_add_three _ _ _
    _ = r * |u (j - 1)| + (1 - 2 * r) * |u j| + r * |u (j + 1)| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hr0, abs_of_nonneg hm]
    _ ≤ r * M + (1 - 2 * r) * M + r * M := by gcongr
    _ = M := by ring

-- MILESTONE (optional: change or delete)
theorem checkerboard (r ε : ℝ) (n : ℕ) :
    (heatStep r)^[n] (fun j => (-1 : ℝ) ^ j * ε) = fun j => (1 - 4 * r) ^ n * ((-1 : ℝ) ^ j * ε) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    funext j
    simp only [heatStep]
    rw [zpow_sub_one₀ (by norm_num), zpow_add_one₀ (by norm_num), pow_succ]
    ring

-- MILESTONE (optional: change or delete)
theorem step_sub (r : ℝ) (u v : ℤ → ℝ) (j : ℤ) :
    heatStep r u j - heatStep r v j = heatStep r (fun k => u k - v k) j := by
  simp only [heatStep]
  ring

-- BEGIN SPEC
theorem heat_stable (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (u : ℤ → ℝ) (M : ℝ)
    (hu : ∀ j, |u j| ≤ M) (n : ℕ) (j : ℤ) : |(heatStep r)^[n] u j| ≤ M :=
-- END SPEC
  by
    induction n generalizing j with
    | zero => exact hu j
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact step_bound r hr0 hr _ M ih j

-- BEGIN SPEC
theorem heat_unstable (r : ℝ) (hr : 1 / 2 < r) (ε : ℝ) (hε : ε ≠ 0) :
    Tendsto (fun n => |(heatStep r)^[n] (fun j => (-1 : ℝ) ^ j * ε) 0|) atTop atTop :=
-- END SPEC
  by
    have h1 : 1 < |1 - 4 * r| := by
      rw [abs_of_neg (by linarith)]
      linarith
    simp_rw [checkerboard, zpow_zero, one_mul, abs_mul, abs_pow]
    exact (tendsto_pow_atTop_atTop_of_one_lt h1).atTop_mul_const (abs_pos.mpr hε)

-- BEGIN SPEC
theorem heat_lax (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (U : ℕ → ℤ → ℝ) (τ : ℝ)
    (hU : ∀ n j, |U (n + 1) j - heatStep r (U n) j| ≤ τ) (n : ℕ) (j : ℤ) :
    |U n j - (heatStep r)^[n] (U 0) j| ≤ n * τ :=
-- END SPEC
  by
    induction n generalizing j with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      set V := (heatStep r)^[n] (U 0)
      -- WHY: stability (step_bound with M := n * τ) carries the old error; consistency adds τ.
      have hb := step_bound r hr0 hr _ (n * τ) ih j
      calc |U (n + 1) j - heatStep r V j|
          = |(U (n + 1) j - heatStep r (U n) j) + (heatStep r (U n) j - heatStep r V j)| := by ring_nf
        _ ≤ |U (n + 1) j - heatStep r (U n) j| + |heatStep r (U n) j - heatStep r V j| :=
            abs_add_le _ _
        _ ≤ τ + n * τ := by rw [step_sub]; gcongr; exact hU n j
        _ = (n + 1 : ℕ) * τ := by push_cast; ring

end H075

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. For 0 ≤ r ≤ 1/2 the three weights r, 1 − 2r, r are ≥ 0 and sum to 1: one step is an average, so it cannot raise the sup (`step_bound`). For r > 1/2 the checkerboard is an eigenvector of the step with eigenvalue 1 − 4r < −1.
H2. `heat_stable`: `induction n generalizing j`, `rw [Function.iterate_succ_apply']`, then `step_bound` applied to the IH. `checkerboard`: induction on n, `funext j`, unfold `heatStep`, rewrite the zpows at j ± 1 in terms of `(-1) ^ j`, `ring`. `heat_lax`: induction on n; split the error at step n+1 as [U(n+1) − S(Uₙ)] + [S(Uₙ) − S(Sⁿ U₀)], where S = `heatStep r`.
H3. `step_bound`: `calc` with `abs_add_three`, then `rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hr0, abs_of_nonneg hm]` (hm : 0 ≤ 1 − 2r), `gcongr`, `ring`. `heat_unstable`: first prove `h1 : 1 < |1 - 4 * r|`; then rewrite with `checkerboard`, evaluate at j = 0 and split the abs, so the sequence becomes `|1 - 4 * r| ^ n * |ε|`; close with `tendsto_pow_atTop_atTop_of_one_lt` and `Tendsto.atTop_mul_const`. `heat_lax`: `abs_add_le`, `step_sub`, and `step_bound` with `M := n * τ`; finish with `push_cast; ring`.
-/
