/- H071 | Jacobi iteration converges | 1-1.5 h | Matrix, sup norm, contraction, Function.iterate, Filter.Tendsto, squeeze_zero, mathlib
GOAL
  Jacobi's method for `A x = b` updates coordinate `i` from row `i`: `xᵢ ← (bᵢ − ∑_{j≠i} aᵢⱼ xⱼ) / aᵢᵢ`.
  If every row has `∑_{j≠i} |aᵢⱼ| ≤ ρ |aᵢᵢ|`, the error shrinks by `ρ` per step: `‖xₖ − x*‖ ≤ ρᵏ ‖x₀ − x*‖`
  for the solution `x*`; with `ρ < 1` (strict diagonal dominance) the iterates converge to `x*` from any start.
  (`f^[k] x`: `f` applied `k` times; `‖v‖` on `Fin n → ℝ` is the sup norm `maxᵢ |vᵢ|`; `univ.erase i`: all j ≠ i;
  `Tendsto u atTop (𝓝 L)`: `u k → L` as `k → ∞`.)

REFERENCE
  example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (i : Fin n) : (A *ᵥ v) i = ∑ j, A i j * v j := rfl
  #check pi_norm_le_iff_of_nonneg  -- 0 ≤ r → (‖x‖ ≤ r ↔ ∀ i, ‖x i‖ ≤ r)
  #check norm_le_pi_norm           -- (f : ∀ i, π i) (i) : ‖f i‖ ≤ ‖f‖     (`Real.norm_eq_abs : ‖r‖ = |r|`)
  #check Finset.add_sum_erase      -- a ∈ s → f a + ∑ x ∈ s.erase a, f x = ∑ x ∈ s, f x
  #check Finset.abs_sum_le_sum_abs -- |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i|      (`Finset.sum_mul`, `Finset.sum_sub_distrib`)
  #check div_le_iff₀               -- 0 < c → (b / c ≤ a ↔ b ≤ a * c)     (`abs_div`, `sub_div`, `div_eq_iff`)
  #check Function.iterate_succ_apply'  -- f^[n.succ] x = f (f^[n] x)
  #check tendsto_iff_norm_sub_tendsto_zero  -- Tendsto f l (𝓝 a) ↔ Tendsto (fun e => ‖f e - a‖) l (𝓝 0)
  #check squeeze_zero              -- (∀ t, 0 ≤ f t) → (∀ t, f t ≤ g t) → Tendsto g l (𝓝 0) → Tendsto f l (𝓝 0)
  #check tendsto_pow_atTop_nhds_zero_of_lt_one  -- 0 ≤ r → r < 1 → Tendsto (fun n => r ^ n) atTop (𝓝 0)  (`.mul_const c`: `· * c`)
  `conv_lhs => rw [← h]` rewrites only the left side (e.g. turn `xs` into `jacobiStep A b xs` there).
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
theorem jacobi_fixed {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b xs : Fin n → ℝ)
    (hdiag : ∀ i, A i i ≠ 0) (hsol : A *ᵥ xs = b) : jacobiStep A b xs = xs := by
  sorry

-- MILESTONE (optional: change or delete)
-- one sweep is a `ρ`-contraction in the sup norm
theorem jacobi_contract {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hdiag : ∀ i, A i i ≠ 0) (hdom : ∀ i, ∑ j ∈ univ.erase i, |A i j| ≤ ρ * |A i i|)
    (x y : Fin n → ℝ) : ‖jacobiStep A b x - jacobiStep A b y‖ ≤ ρ * ‖x - y‖ := by
  sorry

-- BEGIN SPEC
theorem jacobi_error {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b xs : Fin n → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hdiag : ∀ i, A i i ≠ 0) (hdom : ∀ i, ∑ j ∈ univ.erase i, |A i j| ≤ ρ * |A i i|)
    (hsol : A *ᵥ xs = b) (x₀ : Fin n → ℝ) (k : ℕ) :
    ‖(jacobiStep A b)^[k] x₀ - xs‖ ≤ ρ ^ k * ‖x₀ - xs‖ :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem jacobi_tendsto {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b xs : Fin n → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hdiag : ∀ i, A i i ≠ 0) (hdom : ∀ i, ∑ j ∈ univ.erase i, |A i j| ≤ ρ * |A i i|)
    (hsol : A *ᵥ xs = b) (x₀ : Fin n → ℝ) :
    Tendsto (fun k => (jacobiStep A b)^[k] x₀) atTop (𝓝 xs) :=
-- END SPEC
  sorry

end H071

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two facts do all the work: `xs` is a fixed point of `jacobiStep A b`, and one step multiplies sup-norm
    distances by at most `ρ`. Then induct on `k`, and for the limit squeeze `‖xₖ − xs‖` under `ρᵏ ‖x₀ − xs‖ → 0`.
H2. Fixed point: `funext i`, take row `i` of `hsol` (`congrFun hsol i`, `simp only [mulVec, dotProduct]`), split off
    the diagonal term with `add_sum_erase`, clear the division with `div_eq_iff`, `linarith`. Contraction: reduce to one
    coordinate with `pi_norm_le_iff_of_nonneg`; there the difference is `−(∑_{j≠i} A i j (x j − y j)) / A i i`.
    Bound each `|x j − y j| ≤ ‖x − y‖` (`norm_le_pi_norm (x - y) j`), pull `‖x − y‖` out with `sum_mul`, use `hdom i`.
H3. Coordinate step: `rw [← sub_div, abs_div, div_le_iff₀ (abs_pos.mpr (hdiag i))]` and the identity
    `b i - ∑ A i j * x j - (b i - ∑ A i j * y j) = -∑ j ∈ univ.erase i, A i j * (x j - y j)` (`simp only [mul_sub, sum_sub_distrib]; ring`).
    Induction step: `rw [Function.iterate_succ_apply']; conv_lhs => rw [← jacobi_fixed A b xs hdiag hsol]`, then
    `jacobi_contract` and the IH. Limit: `rw [tendsto_iff_norm_sub_tendsto_zero]`, then
    `have h0 : Tendsto (fun k : ℕ => ρ ^ k * ‖x₀ - xs‖) atTop (𝓝 0) := by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1).mul_const ‖x₀ - xs‖`
    and `exact squeeze_zero (fun _ => norm_nonneg _) (fun k => jacobi_error A b xs ρ hρ hdiag hdom hsol x₀ k) h0`.
-/
