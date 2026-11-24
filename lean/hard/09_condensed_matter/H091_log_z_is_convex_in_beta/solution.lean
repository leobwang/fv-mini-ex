/- H091 | log Z is convex in β | 1-1.5 h | ConvexOn, Hölder inequality, rpow, physlib
GOAL
  For a finite system `𝓒` (units kB = 1), `b ↦ log Z(b)` is convex on all of ℝ. The intended route avoids
  derivatives: Hölder's inequality gives `Z(a x + c y) ≤ Z(x)^a * Z(y)^c` for weights `a, c > 0`, `a + c = 1`; take logs.

REFERENCE
  #check CanonicalEnsemble.mathematicalPartitionFunctionBetaReal  -- Z(b) = ∑ i, exp (-b * 𝓒.energy i)
  #check CanonicalEnsemble.mathematicalPartitionFunctionBetaReal_pos  -- [Nonempty ι] : 0 < Z(b)
  #check ConvexOn  -- Convex 𝕜 s ∧ ∀ x ∈ s, ∀ y ∈ s, ∀ a b, 0 ≤ a → 0 ≤ b → a + b = 1 → f (a • x + b • y) ≤ a • f x + b • f y
  #check Real.inner_le_Lp_mul_Lq_of_nonneg  -- Hölder: p.HolderConjugate q → f, g ≥ 0 on s → ∑ f i * g i ≤ (∑ f i ^ p) ^ (1 / p) * (∑ g i ^ q) ^ (1 / q)
  #check Real.holderConjugate_iff  -- p.HolderConjugate q ↔ 1 < p ∧ p⁻¹ + q⁻¹ = 1
  #check Real.exp_mul      -- exp (x * y) = exp x ^ y
  #check Real.log_rpow     -- 0 < x → log (x ^ y) = y * log x
  #check Real.log_mul      -- x ≠ 0 → y ≠ 0 → log (x * y) = log x + log y
  #check Real.log_le_log   -- 0 < x → x ≤ y → log x ≤ log y
  #check Real.rpow_pos_of_pos  -- 0 < x → 0 < x ^ y
  example (a : ℝ) : 1 / (1 / a) = a := one_div_one_div a
  `x ^ (y : ℝ)` is `Real.rpow` (real exponent); `a • x` on ℝ is `a * x` (`smul_eq_mul`).
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite
import Mathlib.Analysis.MeanInequalities

open CanonicalEnsemble Real

namespace H091

section Milestones

variable {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι)

-- MILESTONE (optional: change or delete)
theorem exp_rpow (x e a : ℝ) (ha : 0 < a) : Real.exp (-(a * x) * e) ^ (1 / a) = Real.exp (-x * e) := by
  rw [← Real.exp_mul]
  congr 1
  field_simp

-- MILESTONE (optional: change or delete)
theorem holderConjugate_weights (a c : ℝ) (ha : 0 < a) (hc : 0 < c) (hac : a + c = 1) :
    (1 / a).HolderConjugate (1 / c) := by
  rw [Real.holderConjugate_iff]
  refine ⟨?_, by simp [hac]⟩
  rw [lt_div_iff₀ ha]
  linarith

-- MILESTONE (optional: change or delete)
theorem holder_step (x y a c : ℝ) (ha : 0 < a) (hc : 0 < c) (hac : a + c = 1) :
    𝓒.mathematicalPartitionFunctionBetaReal (a * x + c * y) ≤
      𝓒.mathematicalPartitionFunctionBetaReal x ^ a * 𝓒.mathematicalPartitionFunctionBetaReal y ^ c := by
  have key := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ)
    (f := fun i => Real.exp (-(a * x) * 𝓒.energy i)) (g := fun i => Real.exp (-(c * y) * 𝓒.energy i))
    (holderConjugate_weights a c ha hc hac) (fun i _ => (exp_pos _).le) (fun i _ => (exp_pos _).le)
  simp only [exp_rpow _ _ _ ha, exp_rpow _ _ _ hc, one_div_one_div, ← Real.exp_add] at key
  simp only [mathematicalPartitionFunctionBetaReal]
  refine Eq.trans_le (Finset.sum_congr rfl fun i _ => ?_) key
  congr 1; ring

end Milestones

-- BEGIN SPEC
theorem logZ_convex {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) :
    ConvexOn ℝ Set.univ (fun b => Real.log (𝓒.mathematicalPartitionFunctionBetaReal b)) :=
-- END SPEC
  by
    refine ⟨convex_univ, fun x _ y _ a c ha hc hac => ?_⟩
    simp only [smul_eq_mul]
    rcases ha.eq_or_lt with rfl | ha'
    · obtain rfl : c = 1 := by linarith
      simp
    rcases hc.eq_or_lt with rfl | hc'
    · obtain rfl : a = 1 := by linarith
      simp
    have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos
    calc Real.log (𝓒.mathematicalPartitionFunctionBetaReal (a * x + c * y))
        ≤ Real.log (𝓒.mathematicalPartitionFunctionBetaReal x ^ a *
            𝓒.mathematicalPartitionFunctionBetaReal y ^ c) :=
          Real.log_le_log (hZ _) (holder_step 𝓒 x y a c ha' hc' hac)
      _ = a * Real.log (𝓒.mathematicalPartitionFunctionBetaReal x) +
            c * Real.log (𝓒.mathematicalPartitionFunctionBetaReal y) := by
          rw [Real.log_mul (rpow_pos_of_pos (hZ x) a).ne' (rpow_pos_of_pos (hZ y) c).ne',
            Real.log_rpow (hZ x), Real.log_rpow (hZ y)]

end H091

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `refine ⟨convex_univ, fun x _ y _ a c ha hc hac => ?_⟩`, then `simp only [smul_eq_mul]`. The weights
    `a = 0` or `c = 0` are edge cases (then the other weight is 1); dispose of them first with `rcases ha.eq_or_lt`.
H2. With `a, c > 0`, apply Hölder with exponents `p = 1/a`, `q = 1/c` to `f i = exp (-(a x) E i)` and
    `g i = exp (-(c y) E i)`: then `f i * g i = exp (-(a x + c y) E i)` and `f i ^ (1/a) = exp (-x E i)`.
    The result is `Z(a x + c y) ≤ Z(x) ^ a * Z(y) ^ c` (note `1 / (1 / a) = a`, `one_div_one_div`).
H3. `have key := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ) (f := fun i => Real.exp (-(a * x) * 𝓒.energy i))
    (g := fun i => Real.exp (-(c * y) * 𝓒.energy i)) (holderConjugate_weights a c ha hc hac) (by …) (by …)`;
    for `exp_rpow`: `rw [← Real.exp_mul]; congr 1; field_simp`. Last step: `Real.log_le_log`, then
    `Real.log_mul` and `Real.log_rpow` on the right.
-/
