/- M091 | Variance of an independent sum | 15-20 min | IndepFun, variance_eq_sub, MemLp, E[XY] = E[X]E[Y], L² products, mathlib
GOAL
  For independent square-integrable `X`, `Y`: `Var(X + Y) = Var X + Var Y`. Expand `E[(X + Y)²]` with
  `Var Z = E[Z²] - E[Z]²` and kill the cross term with `E[X Y] = E[X] E[Y]`.

BANNED: variance_add, variance_fun_add, variance_sum, variance_fun_sum, variance_sum', variance_fun_sum', variance_sum_pi, variance_add_prod, covariance_eq_zero, exact?, apply?, try?, rw?, hint, observe

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M091

/- SKELETON · variance_add_indep
  1. Integrability of the variables themselves (for `E[X + Y]` at the end):  R1
       hXi : Integrable X μ          hYi : Integrable Y μ
  2. The cross term, from independence:                                      R2 → R3
       hprod : μ[fun ω => X ω * Y ω] = μ[X] * μ[Y]
  3. Integrability of the three pieces of X² + 2XY + Y², types in `fun` form:
       i1 : Integrable (fun ω => X ω ^ 2) μ                                 R4
       i2 : Integrable (fun ω => 2 * (X ω * Y ω)) μ                         R5 → R6
       i3 : Integrable (fun ω => Y ω ^ 2) μ                                 R4
       i12 : Integrable (fun ω => X ω ^ 2 + 2 * (X ω * Y ω)) μ              R7 (from i1, i2)
  4. The integrand identity
       e : (fun ω => ((X + Y) ^ 2) ω) = fun ω => X ω ^ 2 + 2 * (X ω * Y ω) + Y ω ^ 2
     proof: funext ω, then                                                   R8, then ring
  5. Open the three variances (the first needs `MemLp (X + Y) 2 μ`):         R9 → R10, R10, R10
  6. Replace the integrand, split it outer `+` first, pull out `2`, use the cross term:
                                                                             R11 (rw [e]), R12 (i12, i3),
                                                                             R12 (i1, i2), R13, rw [hprod]
  7. Unfold `(X + Y) x`, `(X ^ 2) x` in the whole goal, split `E[X + Y]`:    R8, R12 (hXi, hYi)
  8. Close the identity between expectations:                                ring
-/
-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem variance_add_indep {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hXY : X ⟂ᵢ[μ] Y) :
    Var[X + Y; μ] = Var[X; μ] + Var[Y; μ] :=
-- END SPEC
  sorry

end M091

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Open all three variances with `variance_eq_sub` (R10); the goal becomes an identity between
    expectations. Every `integral_add` you will need wants integrability proofs: collect them first (R1, R4–R7).
H2. State `(X + Y) ^ 2` pointwise as `e : (fun ω => ((X + Y) ^ 2) ω) = fun ω => X ω ^ 2 + 2 * (X ω * Y ω) + Y ω ^ 2`
    (`funext ω; simp only [Pi.pow_apply, Pi.add_apply]; ring`), rewrite with it, split the integral with
    `integral_add` (outer `+` first), pull the `2` out with `integral_const_mul`, and replace `E[XY]` with the
    independence fact (R3). Then `simp only [Pi.add_apply, Pi.pow_apply]`, split `E[X + Y]`, and `ring`.
H3. `have hprod : μ[fun ω => X ω * Y ω] = μ[X] * μ[Y] := hXY.integral_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable`,
    then `rw [variance_eq_sub (hX.add hY), variance_eq_sub hX, variance_eq_sub hY, e, integral_add i12 i3,
    integral_add i1 i2, integral_const_mul, hprod]`, where `i12 : Integrable (fun ω => X ω ^ 2 + 2 * (X ω * Y ω)) μ`
    is `i1.add i2` with its type written out.
-/
