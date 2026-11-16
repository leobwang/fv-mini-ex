/- H061 | Conditional expectation is the best predictor | 1-1.5 h | condExp, L² projection, pull-out, tower property, mathlib
GOAL
  `m` is a sub-σ-algebra (the information available). Among all `m`-measurable predictors `Y` of `X` with
  `E[Y²] < ∞`, `E[X | m]` has the smallest mean squared error `E[(X - Y)²]`. Key fact: the error
  `X - E[X | m]` is orthogonal to every `m`-measurable `L²` variable `W`, i.e. `E[W (X - E[X | m])] = 0`.

REFERENCE
  `{m mΩ : MeasurableSpace Ω}`, `hm : m ≤ mΩ`: `m` is coarser than the ambient (default, last-declared) σ-algebra `mΩ`.
  `μ[X | m]`: E[X | m];  `MemLp X 2 μ`: E[X²] < ∞;  `StronglyMeasurable[m] Y`: Y is m-measurable;  `∫ ω, f ω ∂μ`: E[f]
  #check stronglyMeasurable_condExp  -- StronglyMeasurable[m] μ[f | m];  `MemLp.condExp one_le_two hX : MemLp μ[X | m] 2 μ`
  #check integral_condExp            -- (hm : m ≤ mΩ) : ∫ x, μ[f | m] x ∂μ = ∫ x, f x ∂μ   (tower property)
  #check condExp_mul_of_stronglyMeasurable_left  -- StronglyMeasurable[m] f → Integrable (f * g) μ → Integrable g μ →
    --   μ[f * g | m] =ᵐ[μ] f * μ[g | m]   (pull out the known factor)
  #check integral_congr_ae           -- f =ᵐ[μ] g → ∫ a, f a ∂μ = ∫ a, g a ∂μ
  #check MemLp.integrable_mul        -- MemLp f 2 μ → MemLp g 2 μ → Integrable (f * g) μ   (Hölder)
    --   `MemLp.integrable_sq : MemLp f 2 μ → Integrable (fun x => f x ^ 2) μ`;  `MemLp.sub`: L² is closed under `-`
  #check integral_add                -- Integrable f μ → Integrable g μ → ∫ a, f a + g a ∂μ = ∫ f + ∫ g
  #check integral_nonneg             -- 0 ≤ f → 0 ≤ ∫ x, f x ∂μ;  also `integral_sub`, `integral_const_mul`
NOTE: `rw [integral_add hf hg]` matches only if `hf : Integrable (fun ω => …) μ` is in lambda form; restate via `have`.
-/
import Mathlib

namespace H061

open MeasureTheory ProbabilityTheory

-- MILESTONE (optional: change or delete)
theorem cross_term_zero {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X W : Ω → ℝ) (hX : MemLp X 2 μ) (hW : MemLp W 2 μ)
    (hWm : StronglyMeasurable[m] W) :
    ∫ ω, W ω * (X ω - μ[X | m] ω) ∂μ = 0 := by
  have hZ : MemLp (μ[X | m]) 2 μ := hX.condExp one_le_two
  have hWX : Integrable (W * X) μ := hW.integrable_mul hX
  have hWZ : Integrable (W * μ[X | m]) μ := hW.integrable_mul hZ
  -- WHY: E[W X] = E[E[W X | m]] = E[W E[X | m]]  (tower, then pull out the known factor W)
  have h1 : ∫ ω, (W * X) ω ∂μ = ∫ ω, (W * μ[X | m]) ω ∂μ := by
    rw [← integral_condExp hm (f := W * X)]
    exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hWm hWX (hX.integrable one_le_two))
  have e : (fun ω => W ω * (X ω - μ[X | m] ω)) = fun ω => (W * X) ω - (W * μ[X | m]) ω := by
    funext ω
    simp only [Pi.mul_apply]
    ring
  rw [e, integral_sub hWX hWZ, h1, sub_self]

-- MILESTONE (optional: change or delete)
theorem integral_sq_split {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y Z : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    ∫ ω, (X ω - Y ω) ^ 2 ∂μ = ∫ ω, (X ω - Z ω) ^ 2 ∂μ
      + 2 * ∫ ω, (Z ω - Y ω) * (X ω - Z ω) ∂μ + ∫ ω, (Z ω - Y ω) ^ 2 ∂μ := by
  have hXZ : MemLp (X - Z) 2 μ := hX.sub hZ
  have hZY : MemLp (Z - Y) 2 μ := hZ.sub hY
  -- WHY: state integrability in lambda form so `integral_add` can rewrite
  have i1 : Integrable (fun ω => (X ω - Z ω) ^ 2) μ := hXZ.integrable_sq
  have i2 : Integrable (fun ω => 2 * ((Z ω - Y ω) * (X ω - Z ω))) μ :=
    (hZY.integrable_mul hXZ).const_mul 2
  have i3 : Integrable (fun ω => (Z ω - Y ω) ^ 2) μ := hZY.integrable_sq
  have i12 : Integrable (fun ω => (X ω - Z ω) ^ 2 + 2 * ((Z ω - Y ω) * (X ω - Z ω))) μ := i1.add i2
  calc ∫ ω, (X ω - Y ω) ^ 2 ∂μ
      = ∫ ω, ((X ω - Z ω) ^ 2 + 2 * ((Z ω - Y ω) * (X ω - Z ω))) + (Z ω - Y ω) ^ 2 ∂μ := by
        congr 1; funext ω; ring
    _ = _ := by
        rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul]

-- BEGIN SPEC
theorem condExp_best_predictor {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hYm : StronglyMeasurable[m] Y) :
    ∫ ω, (X ω - μ[X | m] ω) ^ 2 ∂μ ≤ ∫ ω, (X ω - Y ω) ^ 2 ∂μ :=
-- END SPEC
  by
    have hZ : MemLp (μ[X | m]) 2 μ := hX.condExp one_le_two
    have hW : MemLp (μ[X | m] - Y) 2 μ := hZ.sub hY
    have hWm : StronglyMeasurable[m] (μ[X | m] - Y) := stronglyMeasurable_condExp.sub hYm
    have h0 : ∫ ω, (μ[X | m] ω - Y ω) * (X ω - μ[X | m] ω) ∂μ = 0 :=
      cross_term_zero hm μ X _ hX hW hWm
    rw [integral_sq_split μ X Y (μ[X | m]) hX hY hZ, h0, mul_zero, add_zero]
    have : 0 ≤ ∫ ω, (μ[X | m] ω - Y ω) ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    linarith

end H061

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Put `Z = μ[X | m]` and `W = Z - Y` (m-measurable and in L²). Then `X - Y = (X - Z) + W`, so
    `E[(X - Y)²] = E[(X - Z)²] + 2 E[W (X - Z)] + E[W²]`: the middle term is `0` and the last is `≥ 0`.
H2. Cross term: `E[W X] = E[E[W X | m]] = E[W Z]` (tower property `integral_condExp`, then pull out the
    known `W` under `integral_congr_ae`), and subtract `E[W Z]`. Expansion: one `ring` inside the integral,
    then `integral_add` with each summand's integrability from `MemLp.integrable_sq` / `MemLp.integrable_mul`
    (`hX.integrable one_le_two` turns `MemLp X 2 μ` into `Integrable X μ`).
H3. `have h1 : ∫ ω, (W * X) ω ∂μ = ∫ ω, (W * μ[X | m]) ω ∂μ := by`
    `  rw [← integral_condExp hm (f := W * X)]`
    `  exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hWm hWX (hX.integrable one_le_two))`.
    Main: `cross_term_zero hm μ X (μ[X | m] - Y) hX (hZ.sub hY) (stronglyMeasurable_condExp.sub hYm)`.
-/
