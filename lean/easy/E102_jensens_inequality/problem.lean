/- E102 | Jensen's inequality | 3 min | ConvexOn, map_integral_le, side conditions, mathlib
GOAL
  Two instances of Jensen's inequality `g(E[X]) ≤ E[g(X)]` for convex `g`: `exp(E[X]) ≤ E[exp X]` and
  `(E[X])² ≤ E[X²]`. The lesson is supplying the six arguments of the library lemma.

GUIDE
  Entries R1–R11: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E102

/- SKELETON · jensen
  1. Split the ∧ into the exp half and the square half:                 constructor (or ⟨_, _⟩)
  2. exp half: Jensen, the convexity proof as FIRST argument (it fixes
     g = Real.exp and s = Set.univ); five side goals remain, in order:   R1 with R2
       ContinuousOn Real.exp Set.univ                                    R3 → R4
       IsClosed Set.univ                                                 R5
       ∀ᵐ x ∂μ, X x ∈ Set.univ                                           R6 → intro → R7
       Integrable X μ                                                    the hypothesis hX
       Integrable (Real.exp ∘ X) μ                                       the hypothesis hexp (R8)
  3. square half: the same with g = fun x => x ^ 2:                     R1 with R9 → R10
       continuity                                                        R3 → R11
       closedness, a.e. membership, Integrable X μ                       R5, R6 → intro → R7, hX
       Integrable ((fun x => x ^ 2) ∘ X) μ                               the hypothesis hsq (R8)
-/
-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem jensen {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Integrable X μ) (hexp : Integrable (fun ω => Real.exp (X ω)) μ)
    (hsq : Integrable (fun ω => X ω ^ 2) μ) :
    Real.exp (μ[X]) ≤ μ[fun ω => Real.exp (X ω)] ∧ (μ[X]) ^ 2 ≤ μ[fun ω => X ω ^ 2] :=
-- END SPEC
  sorry

end E102

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both conjuncts are Jensen's inequality `ConvexOn.map_integral_le` (R1) with `s = Set.univ`, so the
    conditions about `s` are trivial. Split the `∧` first (`constructor`, or `⟨_, _⟩` in term mode).
H2. Give R1 the convexity proof as its first argument: `convexOn_exp` (R2), resp.
    `Even.convexOn_pow even_two` for `x ^ 2` (R9, R10). The other five arguments: `.continuousOn` (R3) of
    `Real.continuous_exp` / `continuous_pow 2`, `isClosed_univ`, `ae_of_all _ fun _ => Set.mem_univ _`,
    then the hypotheses `hX` and `hexp` / `hsq`.
H3. `ConvexOn.map_integral_le convexOn_exp Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ fun _ => Set.mem_univ _) hX hexp`, and the same with
    `(Even.convexOn_pow even_two) (continuous_pow 2).continuousOn ... hX hsq`.
-/
