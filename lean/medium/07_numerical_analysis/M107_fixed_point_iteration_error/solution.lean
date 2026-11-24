/- M107 | Fixed-point iteration error | 15-20 min | Function.iterate, induction, a posteriori bound, Tendsto, squeeze, mathlib
GOAL
  Let `f` be `K`-Lipschitz (`|f x - f y| ≤ K |x - y|`, `0 ≤ K < 1`) with fixed point `p`, iterates `xₙ = fⁿ(x₀)`.
  Prove the a priori bound `|xₙ - p| ≤ Kⁿ |x₀ - p|`, the a posteriori (stopping-test) bound
  `|xₙ₊₁ - p| ≤ K/(1-K) |xₙ₊₁ - xₙ|`, which uses only computable quantities, and `xₙ → p`.

REFERENCE
  -- `f^[n] x` is `f` applied `n` times (`f^[0] x = x`); `Tendsto u atTop (𝓝 L)` means `u n → L`
  #check Function.iterate_succ_apply'  -- f^[n.succ] x = f (f^[n] x)
  #check abs_sub_le                    -- |a - c| ≤ |a - b| + |b - c|      (and `abs_sub_comm`)
  #check le_div_iff₀                   -- 0 < c → (a ≤ b / c ↔ a * c ≤ b)
  #check div_mul_eq_mul_div            -- a / b * c = a * c / b
  #check tendsto_iff_norm_sub_tendsto_zero  -- Tendsto u l (𝓝 b) ↔ Tendsto (fun n => ‖u n - b‖) l (𝓝 0)
  #check squeeze_zero  -- (∀ t, 0 ≤ g t) → (∀ t, g t ≤ h t) → Tendsto h l (𝓝 0) → Tendsto g l (𝓝 0)
  #check tendsto_pow_atTop_nhds_zero_of_lt_one  -- 0 ≤ r → r < 1 → Tendsto (fun n => r ^ n) atTop (𝓝 0)
  example (u : ℕ → ℝ) (h : Tendsto u atTop (𝓝 0)) (c : ℝ) : Tendsto (fun n => u n * c) atTop (𝓝 0) := by
    simpa using h.mul_const c
  `‖x‖` on ℝ is `|x|` (`Real.norm_eq_abs`).
BANNED: ContractingWith, apriori_dist_iterate_fixedPoint_le, aposteriori_dist_iterate_fixedPoint_le, tendsto_iterate_fixedPoint
-/
import Mathlib

namespace M107

-- BEGIN SPEC
open Filter Topology

theorem iterate_error (f : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K) (hf : ∀ x y, |f x - f y| ≤ K * |x - y|)
    (p : ℝ) (hp : f p = p) (x₀ : ℝ) (n : ℕ) :
    |f^[n] x₀ - p| ≤ K ^ n * |x₀ - p| :=
-- END SPEC
  by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc |f (f^[n] x₀) - p| = |f (f^[n] x₀) - f p| := by rw [hp]
        _ ≤ K * |f^[n] x₀ - p| := hf _ _
        _ ≤ K * (K ^ n * |x₀ - p|) := by gcongr
        _ = K ^ (n + 1) * |x₀ - p| := by ring

-- BEGIN SPEC
theorem aposteriori_error (f : ℝ → ℝ) (K : ℝ) (hK0 : 0 ≤ K) (hK : K < 1)
    (hf : ∀ x y, |f x - f y| ≤ K * |x - y|) (p : ℝ) (hp : f p = p) (x₀ : ℝ) (n : ℕ) :
    |f^[n + 1] x₀ - p| ≤ K / (1 - K) * |f^[n + 1] x₀ - f^[n] x₀| :=
-- END SPEC
  by
    set x := f^[n] x₀
    rw [Function.iterate_succ_apply']
    have h1 : |f x - p| ≤ K * |x - p| := by
      calc |f x - p| = |f x - f p| := by rw [hp]
        _ ≤ K * |x - p| := hf x p
    have h2 : |x - p| ≤ |f x - x| + |f x - p| := by
      calc |x - p| ≤ |x - f x| + |f x - p| := abs_sub_le _ _ _
        _ = |f x - x| + |f x - p| := by rw [abs_sub_comm x]
    -- WHY: `(1 - K) e ≤ K d` needs `K ≥ 0` to multiply `h2` by `K`; nlinarith finds that product
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith

-- BEGIN SPEC
theorem iterate_tendsto (f : ℝ → ℝ) (K : ℝ) (hK0 : 0 ≤ K) (hK : K < 1)
    (hf : ∀ x y, |f x - f y| ≤ K * |x - y|) (p : ℝ) (hp : f p = p) (x₀ : ℝ) :
    Tendsto (fun n => f^[n] x₀) atTop (𝓝 p) :=
-- END SPEC
  by
    have h0 : Tendsto (fun n : ℕ => K ^ n * |x₀ - p|) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hK0 hK).mul_const |x₀ - p|
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0
    rw [Real.norm_eq_abs]
    exact iterate_error f K hK0 hf p hp x₀ n

end M107

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A priori: induction on `n`; one step is `|f xₙ - p| = |f xₙ - f p| ≤ K |xₙ - p|` (use `hp`). For the
    limit, squeeze `|xₙ - p|` between `0` and `Kⁿ |x₀ - p|`, which tends to 0.
H2. A posteriori: write `x = f^[n] x₀`, so `f^[n + 1] x₀ = f x`. Then `e = |f x - p| ≤ K |x - p|` and
    `|x - p| ≤ |f x - x| + e`, so `(1 - K) e ≤ K |f x - x|`; divide by `1 - K > 0`.
H3. Step case: `rw [Function.iterate_succ_apply']`, then
    `calc |f (f^[n] x₀) - p| = |f (f^[n] x₀) - f p| := by rw [hp]
       _ ≤ K * |f^[n] x₀ - p| := hf _ _
       _ ≤ K * (K ^ n * |x₀ - p|) := by gcongr`.
    A posteriori finish: `rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; nlinarith`.
    Limit: with `h0 : Tendsto (fun n => K ^ n * |x₀ - p|) atTop (𝓝 0)`, do
    `rw [tendsto_iff_norm_sub_tendsto_zero]; refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0`.
-/
