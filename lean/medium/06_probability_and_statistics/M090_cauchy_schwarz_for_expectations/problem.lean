/- M090 | Cauchy–Schwarz for expectations | 15-20 min | discriminant argument, integral algebra, integral_nonneg, mathlib
GOAL
  `(E[XY])² ≤ E[X²] E[Y²]`. For every real `t`, `E[(X - tY)²] ≥ 0` is a quadratic in `t` that never
  goes negative, so its discriminant is `≤ 0`.

REFERENCE
  `μ[f]` is `∫ ω, f ω ∂μ` (here `μ` is any measure). `Integrable f μ`: `∫ |f| ∂μ < ∞`.
  #check integral_nonneg      -- 0 ≤ f → 0 ≤ ∫ x, f x ∂μ     (`0 ≤ f` is `∀ ω, 0 ≤ f ω`)
  #check integral_add         -- Integrable f μ → Integrable g μ → ∫ a, f a + g a ∂μ = ∫ f + ∫ g
  #check integral_const_mul   -- ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
  #check Integrable.const_mul -- Integrable f μ → ∀ c, Integrable (fun x => c * f x) μ   (and `.add`)
  #check discrim_le_zero      -- (∀ x, 0 ≤ a * (x * x) + b * x + c) → discrim a b c ≤ 0
  #check discrim              -- discrim a b c = b ^ 2 - 4 * a * c   (unfold with `rw [discrim] at h`)
BANNED: integral_mul_le_Lp_mul_Lq_of_nonneg, integral_mul_norm_le_Lp_mul_Lq, inner_mul_inner_self_le, real_inner_mul_inner_self_le, abs_real_inner_le_norm, real_inner_le_norm, norm_inner_le_norm
NOTE: `rw [integral_add hf hg]` matches only when `hf`, `hg` are stated as `Integrable (fun ω => ...) μ`.
-/
import Mathlib

namespace M090

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem cauchy_schwarz {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X Y : Ω → ℝ) (hX2 : Integrable (fun ω => X ω ^ 2) μ) (hY2 : Integrable (fun ω => Y ω ^ 2) μ)
    (hXY : Integrable (fun ω => X ω * Y ω) μ) :
    (μ[fun ω => X ω * Y ω]) ^ 2 ≤ μ[fun ω => X ω ^ 2] * μ[fun ω => Y ω ^ 2] :=
-- END SPEC
  sorry

end M090

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `(X - tY)² = t² Y² - 2t XY + X²`, so `0 ≤ E[(X - tY)²] = E[Y²] t² - 2 E[XY] t + E[X²]` for all `t`.
H2. Prove `key : ∀ t : ℝ, 0 ≤ μ[fun ω => Y ω ^ 2] * (t * t) + (-2 * μ[fun ω => X ω * Y ω]) * t + μ[fun ω => X ω ^ 2]`
    from `integral_nonneg fun ω => sq_nonneg (X ω - t * Y ω)`, after rewriting the integrand and
    splitting the integral. Then apply `discrim_le_zero key`.
H3. Inside `key`: `rw [e, integral_add i3 hX2, integral_add i1 i2, integral_const_mul, integral_const_mul] at h0; linarith`
    where `i1 : Integrable (fun ω => (t * t) * Y ω ^ 2) μ` etc. Finish with `rw [discrim] at this; nlinarith`.
-/
