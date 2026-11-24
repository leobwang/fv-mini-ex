/- M093 | Jensen off a closed domain: E[1/X] ≥ 1/E[X] | 15 min | convexity, tangent line, integral_mono, integral_pos_iff_support_of_nonneg, mathlib
GOAL
  For a strictly positive `X` with `X` and `1/X` integrable: `1 / E[X] ≤ E[1 / X]` (Jensen for the convex
  map `x ↦ 1/x` on `(0, ∞)`). Integrate the tangent line of `1/x` at `m = E[X]`, which lies below `1/x`.

REFERENCE
  `x⁻¹` is `1/x`. Library Jensen `ConvexOn.map_integral_le` (E102) needs a closed domain, and `(0, ∞)` is not
  closed; in Lean `0⁻¹ = 0`, so `x⁻¹` is not convex on `[0, ∞)`. `Function.support f = {ω | f ω ≠ 0}`.
  `μ[X]` is `E[X] = ∫ ω, X ω ∂μ`.
  #check integral_pos_iff_support_of_nonneg  -- 0 ≤ f → Integrable f μ → (0 < ∫ x, f x ∂μ ↔ 0 < μ (support f))
  #check integral_mono   -- Integrable f μ → Integrable g μ → f ≤ g → ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ
  #check integral_sub    -- Integrable f μ → Integrable g μ → ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
  #check integral_div    -- ∫ a, f a / r ∂μ = (∫ a, f a ∂μ) / r
  #check integral_const  -- ∫ x, c ∂μ = μ.real univ • c        (`simp` knows `μ.real univ = 1`)
  #check Integrable.div_const  -- Integrable f μ → ∀ c, Integrable (fun x => f x / c) μ
  #check div_le_iff₀     -- 0 < c → (b / c ≤ a ↔ b ≤ a * c)
  `field_simp` clears denominators it can prove nonzero; `nlinarith [sq_nonneg (x - m)]` uses `(x - m)² ≥ 0`.
NOTE: pass the function explicitly, `integral_mono (f := fun ω => …) hf hg hpt`, when `hpt : ∀ ω, … ≤ …`.
-/
import Mathlib

namespace M093

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem jensen_inv {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hpos : ∀ ω, 0 < X ω) (hX : Integrable X μ)
    (hinv : Integrable (fun ω => (X ω)⁻¹) μ) :
    (μ[X])⁻¹ ≤ μ[fun ω => (X ω)⁻¹] :=
-- END SPEC
  by
    have hm : 0 < μ[X] := by
      rw [integral_pos_iff_support_of_nonneg (fun ω => (hpos ω).le) hX]
      have : Function.support X = Set.univ := by
        ext ω; simp [(hpos ω).ne']
      simp [this]
    set m := μ[X]
    -- the tangent line of `x ↦ 1/x` at `m` lies below the graph on `(0, ∞)`
    have hpt : ∀ ω, 2 / m - X ω / m ^ 2 ≤ (X ω)⁻¹ := by
      intro ω
      have hx := hpos ω
      rw [div_sub_div _ _ hm.ne' (by positivity), div_le_iff₀ (by positivity)]
      field_simp
      nlinarith [sq_nonneg (X ω - m)]
    have hl : Integrable (fun ω => 2 / m - X ω / m ^ 2) μ :=
      (integrable_const _).sub (hX.div_const _)
    calc m⁻¹ = μ[fun ω => 2 / m - X ω / m ^ 2] := by
          have h2 : μ[fun ω => X ω / m ^ 2] = m / m ^ 2 := integral_div _ _
          rw [integral_sub (integrable_const _) (hX.div_const _), h2, integral_const]
          simp only [probReal_univ, one_smul]
          field_simp
          ring
      _ ≤ μ[fun ω => (X ω)⁻¹] := integral_mono (f := fun ω => 2 / m - X ω / m ^ 2) hl hinv hpt

end M093

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. First show `m := μ[X] > 0` (the support of `X` is all of `Ω`, which has measure 1). Then find a
    line `a - b x` below `1/x` on `(0, ∞)` whose expectation is exactly `1/m`.
H2. The tangent at `m`: `2/m - x/m² ≤ 1/x` for `x > 0`, because multiplied out it is `(x - m)² ≥ 0`.
    Its expectation is `2/m - m/m² = 1/m`. Finish with `integral_mono`.
H3. `have hpt : ∀ ω, 2 / m - X ω / m ^ 2 ≤ (X ω)⁻¹` (`rw [div_sub_div …, div_le_iff₀ …]; field_simp; nlinarith …`),
    then `calc m⁻¹ = μ[fun ω => 2 / m - X ω / m ^ 2] := … _ ≤ _ := integral_mono (f := fun ω => 2 / m - X ω / m ^ 2) hl hinv hpt`.
    For the `=` step, `have h2 : μ[fun ω => X ω / m ^ 2] = m / m ^ 2 := integral_div _ _` (a bare `rw [integral_div]`
    may grab the constant `2 / m` instead), then `integral_sub`, `integral_const`, `field_simp`.
-/
