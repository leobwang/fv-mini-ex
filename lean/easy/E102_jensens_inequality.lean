/- E102 | Jensen's inequality | 3 min | ConvexOn, map_integral_le, side conditions, mathlib
GOAL
  Two instances of Jensen's inequality `g(E[X]) ≤ E[g(X)]` for convex `g`: `exp(E[X]) ≤ E[exp X]` and
  `(E[X])² ≤ E[X²]`. The lesson is supplying the six arguments of the library lemma.

REFERENCE
  #check ConvexOn.map_integral_le  -- Jensen. Arguments in order, for f : α → E, g : E → ℝ, s : Set E:
    -- ConvexOn ℝ s g → ContinuousOn g s → IsClosed s → (∀ᵐ x ∂μ, f x ∈ s) →
    -- Integrable f μ → Integrable (g ∘ f) μ → g (∫ x, f x ∂μ) ≤ ∫ x, g (f x) ∂μ
  #check convexOn_exp              -- ConvexOn ℝ Set.univ Real.exp
  #check Even.convexOn_pow         -- Even n → ConvexOn 𝕜 Set.univ fun x => x ^ n
  #check Real.continuous_exp       -- Continuous Real.exp; `.continuousOn` gives ContinuousOn _ s
  #check even_two                  -- Even 2   (so `Even.convexOn_pow even_two` is x ↦ x ^ 2)
  #check continuous_pow            -- (n : ℕ) → Continuous fun a => a ^ n
  #check isClosed_univ             -- IsClosed Set.univ
  #check ae_of_all                 -- (μ) → (∀ a, p a) → ∀ᵐ a ∂μ, p a
  `∀ᵐ x ∂μ, p x` means "p holds μ-almost everywhere"; `ae_of_all _ fun _ => Set.mem_univ _ : ∀ᵐ x ∂μ, f x ∈ Set.univ`.
-/
import Mathlib

namespace E102

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
H1. Both conjuncts are `ConvexOn.map_integral_le` with `s = Set.univ`, so membership in `s` is trivial.
H2. For the square, the convex function is `fun x : ℝ => x ^ 2` with `n = 2` (`even_two : Even 2`);
    continuity of powers is `continuous_pow 2`. Almost-everywhere membership: `ae_of_all _ fun _ => Set.mem_univ _`.
H3. `ConvexOn.map_integral_le convexOn_exp Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ fun _ => Set.mem_univ _) hX hexp`, and the same with
    `(Even.convexOn_pow even_two) (continuous_pow 2).continuousOn ... hX hsq`.
-/
