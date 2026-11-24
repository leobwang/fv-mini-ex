/- H061 | Conditional expectation is the best predictor | 1-1.5 h | condExp, L² projection, pull-out, tower property, mathlib
GOAL
  `m` is a sub-σ-algebra (the information available). Among all `m`-measurable predictors `Y` of `X` with
  `E[Y²] < ∞`, `E[X | m]` has the smallest mean squared error `E[(X - Y)²]`. Key fact: the error
  `X - E[X | m]` is orthogonal to every `m`-measurable `L²` variable `W`, i.e. `E[W (X - E[X | m])] = 0`.

GUIDE
  Entries R1–R24: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H061

open MeasureTheory ProbabilityTheory

/- SKELETON · cross_term_zero   (milestone 1; used by condExp_best_predictor)
  Write Z for μ[X | m]. Goal: E[W (X - Z)] = 0.
  1. Facts:  hZ : MemLp μ[X | m] 2 μ                                       R1
             hWX : Integrable (W * X) μ,  hWZ : Integrable (W * μ[X | m]) μ   R2
  2. h1 : ∫ ω, (W * X) ω ∂μ = ∫ ω, (W * μ[X | m]) ω ∂μ   (E[W X] = E[W Z])
       tower, right to left, naming f := W * X:                            R4
       then integrals of a.e.-equal functions (goal becomes an =ᵐ[μ]):    R6
       which the pull-out of the known factor W closes:                    R5 (third argument by R3)
  3. e : (fun ω => W ω * (X ω - μ[X | m] ω)) = fun ω => (W * X) ω - (W * μ[X | m]) ω
       R7, R8, then ring
  4. rw [e], split the integral (hWX, hWZ), rw [h1], close:                R9, rw [h1], R10
-/
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

/- SKELETON · integral_sq_split   (milestone 2; used by condExp_best_predictor)
  Pure linearity of ∫: no conditional expectation.
  1. hXZ : MemLp (X - Z) 2 μ,  hZY : MemLp (Z - Y) 2 μ:                    R11
  2. Each summand integrable, stated in lambda form (copy the summands from the goal):
       i1 : Integrable (fun ω => (X ω - Z ω) ^ 2) μ                        R12
       i2 : Integrable (fun ω => 2 * ((Z ω - Y ω) * (X ω - Z ω))) μ        R2 → R13
       i3 : Integrable (fun ω => (Z ω - Y ω) ^ 2) μ                        R12
       i12 : the sum of the first two                                     R14
  3. calc with two steps:                                                  R15
       = ∫ ω, ((X ω - Z ω) ^ 2 + 2 * (…)) + (Z ω - Y ω) ^ 2 ∂μ:           R16, R7, ring
       _ = _: split the outer + (i12, i3), then the inner (i1, i2), pull 2 out:   R17, R17, R18
-/
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

/- SKELETON · condExp_best_predictor
  Prove milestones 1 (cross_term_zero) and 2 (integral_sq_split) first.
  1. Facts:  hZ : MemLp μ[X | m] 2 μ                                       R1
             hW : MemLp (μ[X | m] - Y) 2 μ                                 R11
             hWm : StronglyMeasurable[m] (μ[X | m] - Y)                    R19 → R20
  2. h0 : ∫ ω, (μ[X | m] ω - Y ω) * (X ω - μ[X | m] ω) ∂μ = 0:             milestone 1 with W := μ[X | m] - Y
     Write this type out in the `have`: a bare `have h0 := cross_term_zero …` gets the type
     `∫ ω, (μ[X | m] - Y) ω * … = 0`, which the `rw [h0]` of step 3 does not find (Traps).
  3. rw with milestone 2, `integral_sq_split μ X Y (μ[X | m]) hX hY hZ` (it rewrites the right side),
     then rw [h0], drop the 2 * 0:                                         R21
  4. 0 ≤ ∫ ω, (μ[X | m] ω - Y ω) ^ 2 ∂μ:                                   R22 → R23
  5. finish:                                                               R24
-/
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
    `E[(X - Y)²] = E[(X - Z)²] + 2 E[W (X - Z)] + E[W²]` (milestone 2): the middle term is `0`
    (milestone 1) and the last is `≥ 0`.
H2. Milestone 1: `E[W X] = E[E[W X | m]] = E[W Z]` (tower R4, then pull out the known `W` under
    `integral_congr_ae`, R6 with R5), and subtract `E[W Z]` (R9, R10). Milestone 2: one `ring` inside the
    integral (R16), then `integral_add` twice with each summand's integrability stated in lambda form
    (R12–R14), then `integral_const_mul` (R18).
H3. `have h1 : ∫ ω, (W * X) ω ∂μ = ∫ ω, (W * μ[X | m]) ω ∂μ := by`
    `  rw [← integral_condExp hm (f := W * X)]`
    `  exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hWm hWX (hX.integrable one_le_two))`.
    Main: `have h0 : <the type in the skeleton> := cross_term_zero hm μ X (μ[X | m] - Y) hX (hZ.sub hY)`
    `  (stronglyMeasurable_condExp.sub hYm)`, then `rw [integral_sq_split μ X Y (μ[X | m]) hX hY hZ, h0]`.
-/
