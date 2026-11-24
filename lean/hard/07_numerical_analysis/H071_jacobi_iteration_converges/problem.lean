/- H071 | Jacobi iteration converges | 1-1.5 h | Matrix, sup norm, contraction, Function.iterate, Filter.Tendsto, squeeze_zero, mathlib
GOAL
  Jacobi's method for `A x = b` updates coordinate `i` from row `i`: `xᵢ ← (bᵢ − ∑_{j≠i} aᵢⱼ xⱼ) / aᵢᵢ`.
  If every row has `∑_{j≠i} |aᵢⱼ| ≤ ρ |aᵢᵢ|`, the error shrinks by `ρ` per step: `‖xₖ − x*‖ ≤ ρᵏ ‖x₀ − x*‖`
  for the solution `x*`; with `ρ < 1` (strict diagonal dominance) the iterates converge to `x*` from any start.
  (`f^[k] x`: `f` applied `k` times; `‖v‖` on `Fin n → ℝ` is the sup norm `maxᵢ |vᵢ|`; `univ.erase i`: all j ≠ i;
  `Tendsto u atTop (𝓝 L)`: `u k → L` as `k → ∞`.)

GUIDE
  Entries R1–R37: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Matrix Finset Filter Topology

namespace H071

-- BEGIN SPEC
/-- one Jacobi sweep: every coordinate is recomputed from the old vector `x` -/
noncomputable def jacobiStep {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (b i - ∑ j ∈ univ.erase i, A i j * x j) / A i i
-- END SPEC

-- MILESTONE (optional: change or delete)
-- the exact solution is a fixed point of the sweep
/- SKELETON · jacobi_fixed
  1. Vector equation → coordinate i:                                R1
  2. Row i of hsol as a hypothesis, written out as a sum:           R2, R3
       this : ∑ x, A i x * xs x = b i
  3. Split the diagonal term off that sum (at this):                R4 with R5
       this : A i i * xs i + ∑ x ∈ univ.erase i, A i x * xs x = b i
  4. Unfold the sweep, clear the division by A i i ≠ 0 (hdiag i):   simp only [jacobiStep], R6
  5. What is left is linear in xs i and the two sums:               R7
-/
theorem jacobi_fixed {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b xs : Fin n → ℝ)
    (hdiag : ∀ i, A i i ≠ 0) (hsol : A *ᵥ xs = b) : jacobiStep A b xs = xs := by
  sorry

-- MILESTONE (optional: change or delete)
-- one sweep is a `ρ`-contraction in the sup norm
/- SKELETON · jacobi_contract
  1. Sup norm → every coordinate (side fact 0 ≤ ρ * ‖x - y‖):        R8 with R9, then intro i
  2. hpos : 0 < |A i i|                                             R10
  3. Evaluate coordinate i:  simp only [Pi.sub_apply, jacobiStep, Real.norm_eq_abs]   R11, R12
  4. One fraction, |·| through it, clear |A i i| with hpos:         R13, R14, R15
       goal: |b i - S x - (b i - S y)| ≤ ρ * ‖x - y‖ * |A i i|,  S v = ∑ j ∈ univ.erase i, A i j * v j
  5. e : b i - S x - (b i - S y) = -∑ j ∈ univ.erase i, A i j * (x j - y j)
       proof: R16, R17, then ring;   then rw [e] and R18
  6. calc (R19):
       |∑ j ∈ univ.erase i, A i j * (x j - y j)| ≤ ∑ j ∈ univ.erase i, |A i j| * ‖x - y‖
           triangle inequality, then term by term:                  R20, R21, R22
           per term: R23, R24, then |x j - y j| ≤ ‖x - y‖:          R26 with R25
       _ = (∑ j ∈ univ.erase i, |A i j|) * ‖x - y‖                  R27
       _ ≤ (ρ * |A i i|) * ‖x - y‖                                  R24, then hdom i
       _ = ρ * ‖x - y‖ * |A i i|                                    ring
-/
theorem jacobi_contract {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hdiag : ∀ i, A i i ≠ 0) (hdom : ∀ i, ∑ j ∈ univ.erase i, |A i j| ≤ ρ * |A i i|)
    (x y : Fin n → ℝ) : ‖jacobiStep A b x - jacobiStep A b y‖ ≤ ρ * ‖x - y‖ := by
  sorry

/- SKELETON · jacobi_error
  Prove the MILESTONES jacobi_fixed and jacobi_contract first; both are used in step 3.
  1. Induction on k:                                                R28
  2. zero: simp  (it applies R29, pow_zero, one_mul)
  3. succ k ih:
       peel off the last sweep:                                     R30
       turn the xs on the LEFT into jacobiStep A b xs:              R31 with MILESTONE jacobi_fixed
       calc (R19)  _ ≤ ρ * ‖(jacobiStep A b)^[k] x₀ - xs‖           MILESTONE jacobi_contract
                   _ ≤ ρ * (ρ ^ k * ‖x₀ - xs‖)                      R24 (it closes with ih)
                   _ = ρ ^ (k + 1) * ‖x₀ - xs‖                      ring
-/
-- BEGIN SPEC
theorem jacobi_error {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b xs : Fin n → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hdiag : ∀ i, A i i ≠ 0) (hdom : ∀ i, ∑ j ∈ univ.erase i, |A i j| ≤ ρ * |A i i|)
    (hsol : A *ᵥ xs = b) (x₀ : Fin n → ℝ) (k : ℕ) :
    ‖(jacobiStep A b)^[k] x₀ - xs‖ ≤ ρ ^ k * ‖x₀ - xs‖ :=
-- END SPEC
  sorry

/- SKELETON · jacobi_tendsto
  Uses jacobi_error (above) for every k; no new induction.
  1. Limit of the iterates → limit of their distance to xs:         R32
  2. h0 : Tendsto (fun k : ℕ => ρ ^ k * ‖x₀ - xs‖) atTop (𝓝 0)       R33, R34, R35 (one simpa)
  3. Squeeze ‖xₖ - xs‖ between 0 and ρ ^ k * ‖x₀ - xs‖:              R36 with R37, jacobi_error, h0
-/
-- BEGIN SPEC
theorem jacobi_tendsto {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b xs : Fin n → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hdiag : ∀ i, A i i ≠ 0) (hdom : ∀ i, ∑ j ∈ univ.erase i, |A i j| ≤ ρ * |A i i|)
    (hsol : A *ᵥ xs = b) (x₀ : Fin n → ℝ) :
    Tendsto (fun k => (jacobiStep A b)^[k] x₀) atTop (𝓝 xs) :=
-- END SPEC
  sorry

end H071

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two milestones do all the work: `xs` is a fixed point of `jacobiStep A b` (jacobi_fixed), and one
    sweep multiplies sup-norm distances by at most `ρ` (jacobi_contract). Then `jacobi_error` is an induction
    on `k`, and `jacobi_tendsto` squeezes `‖xₖ − xs‖` between `0` and `ρᵏ ‖x₀ − xs‖ → 0`.
H2. Fixed point: work at one coordinate (R1), take row `i` of `hsol` as a sum (R2, R3), split off the diagonal
    term (R4), clear the division (R6) and finish with `linarith`. Contraction: reduce the sup norm to one
    coordinate (R8), merge the two fractions and clear `|A i i|` (R13–R15); the numerator is
    `−∑_{j≠i} A i j (x j − y j)`. Bound it by the triangle inequality (R20, R22), each `|x j − y j| ≤ ‖x − y‖`
    (R25), factor `‖x − y‖` out (R27) and use `hdom i`. Error: peel off the last sweep (R30), rewrite the
    left `xs` as `jacobiStep A b xs` (R31), then `jacobi_contract` and `ih`.
H3. Coordinate step: `rw [← sub_div, abs_div, div_le_iff₀ (abs_pos.mpr (hdiag i))]` and the identity
    `b i - ∑ A i j * x j - (b i - ∑ A i j * y j) = -∑ j ∈ univ.erase i, A i j * (x j - y j)` (`simp only [mul_sub, sum_sub_distrib]; ring`).
    Induction step: `rw [Function.iterate_succ_apply']; conv_lhs => rw [← jacobi_fixed A b xs hdiag hsol]`, then
    `jacobi_contract` and the IH. Limit: `rw [tendsto_iff_norm_sub_tendsto_zero]`, then
    `have h0 : Tendsto (fun k : ℕ => ρ ^ k * ‖x₀ - xs‖) atTop (𝓝 0) := by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1).mul_const ‖x₀ - xs‖`
    and `exact squeeze_zero (fun _ => norm_nonneg _) (fun k => jacobi_error A b xs ρ hρ hdiag hdom hsol x₀ k) h0`.
-/
