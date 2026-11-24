/- M091 | Variance of an independent sum | 15-20 min | IndepFun, variance_eq_sub, MemLp, E[XY] = E[X]E[Y], L² products, mathlib
GOAL
  For independent square-integrable `X`, `Y`: `Var(X + Y) = Var X + Var Y`. Expand `E[(X + Y)²]` with
  `Var Z = E[Z²] - E[Z]²` and kill the cross term with `E[X Y] = E[X] E[Y]`.

REFERENCE
  `MemLp X 2 μ`: `X` is square-integrable (`E[X²] < ∞`). `μ[X]` is `E[X] = ∫ ω, X ω ∂μ`; `Var[X; μ]` is the variance; `X ⟂ᵢ[μ] Y`: independent.
  #check variance_eq_sub     -- MemLp X 2 μ → Var[X; μ] = μ[X ^ 2] - μ[X] ^ 2
  #check MemLp.add           -- MemLp f p μ → MemLp g p μ → MemLp (f + g) p μ
  #check MemLp.integrable    -- 1 ≤ q → MemLp f q μ → Integrable f μ    (`hX.integrable one_le_two`)
  #check MemLp.integrable_sq -- MemLp f 2 μ → Integrable (fun x => f x ^ 2) μ
  #check MemLp.integrable_mul  -- `hX.integrable_mul hY : Integrable (X * Y) μ` for two L² functions (Hölder)
  #check IndepFun.integral_mul_eq_mul_integral  -- X ⟂ᵢ[μ] Y → AEStronglyMeasurable X μ → (… Y) → μ[X * Y] = μ[X] * μ[Y]
  #check MemLp.aestronglyMeasurable  -- MemLp f p μ → AEStronglyMeasurable f μ
  `(X + Y) ^ 2` is a power of functions: `((X + Y) ^ 2) ω = (X ω + Y ω) ^ 2` (`Pi.pow_apply`, `Pi.add_apply`).
NOTE: `rw [integral_add hf hg]` fires only if `hf : Integrable (fun ω => …) μ` has the integrand's exact lambda shape.
BANNED: variance_add, variance_fun_add, variance_sum, variance_fun_sum, variance_sum', variance_fun_sum', variance_sum_pi, variance_add_prod, covariance_eq_zero, exact?, apply?, try?, rw?, hint, observe
-/
import Mathlib

namespace M091

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem variance_add_indep {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hXY : X ⟂ᵢ[μ] Y) :
    Var[X + Y; μ] = Var[X; μ] + Var[Y; μ] :=
-- END SPEC
  by
    have hXi : Integrable X μ := hX.integrable one_le_two
    have hYi : Integrable Y μ := hY.integrable one_le_two
    -- independence kills the cross term: E[XY] = E[X] E[Y]
    have hprod : μ[fun ω => X ω * Y ω] = μ[X] * μ[Y] :=
      hXY.integral_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable
    have i1 : Integrable (fun ω => X ω ^ 2) μ := hX.integrable_sq
    have i2 : Integrable (fun ω => 2 * (X ω * Y ω)) μ := (hX.integrable_mul hY).const_mul 2
    have i3 : Integrable (fun ω => Y ω ^ 2) μ := hY.integrable_sq
    -- WHY: `i1.add i2` has type `Integrable ((fun …) + fun …)`; restate it in lambda form for `rw`
    have i12 : Integrable (fun ω => X ω ^ 2 + 2 * (X ω * Y ω)) μ := i1.add i2
    have e : (fun ω => ((X + Y) ^ 2) ω) = fun ω => X ω ^ 2 + 2 * (X ω * Y ω) + Y ω ^ 2 := by
      funext ω; simp only [Pi.pow_apply, Pi.add_apply]; ring
    rw [variance_eq_sub (hX.add hY), variance_eq_sub hX, variance_eq_sub hY, e,
      integral_add i12 i3, integral_add i1 i2, integral_const_mul, hprod]
    simp only [Pi.add_apply, Pi.pow_apply]
    rw [integral_add hXi hYi]
    ring

end M091

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Rewrite all three variances with `variance_eq_sub`; the goal becomes an identity between expectations.
H2. Restate `(X + Y) ^ 2` as `fun ω => X ω ^ 2 + 2 * (X ω * Y ω) + Y ω ^ 2` (a `have … := by funext ω; …; ring`),
    split the expectation with `integral_add` (integrability `have`s first), and replace `μ[X * Y]` by `μ[X] * μ[Y]`.
H3. `have hprod : μ[fun ω => X ω * Y ω] = μ[X] * μ[Y] := hXY.integral_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable`,
    then `rw [e, integral_add i12 i3, integral_add i1 i2, integral_const_mul, hprod]`, where `i12 : Integrable
    (fun ω => X ω ^ 2 + 2 * (X ω * Y ω)) μ`, `i3`, `i1`, `i2` are the pieces. Split `μ[X + Y]` the same way
    (`simp only [Pi.add_apply]` first) and finish with `ring`.
-/
