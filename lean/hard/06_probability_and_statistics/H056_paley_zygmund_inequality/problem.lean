/- H056 | Paley–Zygmund inequality | 1-1.5 h | second moment method, Cauchy–Schwarz, indicators, integral_mono, mathlib
GOAL
  For `X ≥ 0` with `E[X²] < ∞` and `0 ≤ θ ≤ 1`: `P(X > θ E X) ≥ (1 - θ)² (E X)² / E[X²]` (stated
  without division). Split `E X` on the event `A = {X > θ E X}`, then bound `E[X 1_A]` by Cauchy–Schwarz.

GUIDE
  Entries R1–R28: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H056

open MeasureTheory ProbabilityTheory

/- SKELETON · split_mean   (milestone; prove it FIRST; paley_zygmund uses it in its second calc step)
  Below, A is `{ω | θ * μ[X] < X ω}` and 1_A ω is `A.indicator 1 ω` (write them out in Lean).
  1. Three facts, each a `have`:
       hXi : Integrable X μ                                                       R1
       hA  : MeasurableSet A                                                      R2
       hI  : Integrable (fun ω => X ω * 1_A ω) μ   (lambda form: cheatsheet Traps)
             integrable × bounded:                                                R3
             the bounded factor is measurable:                                    R4, R5
             ‖1_A ω‖ ≤ 1 for every ω, split on the condition:                     R6, R7, R8
  2. A two-step calc:                                                             R9
       μ[X] ≤ ∫ ω, (θ * μ[X] + X ω * 1_A ω) ∂μ
          _ = θ * μ[X] + ∫ ω, X ω * 1_A ω ∂μ
  3. The ≤ step: integrate a pointwise bound; the right side is integrable by:   R10 with R11
       split on the condition `θ * μ[X] < X ω`:                                   R7
       pos: simp leaves 0 ≤ θ * μ[X]:                                             R8, then R12, R13
       neg: simp leaves X ω ≤ θ * μ[X], which h gives:                            R8, then R14
  4. The = step: split the integral, then the constant's integral is itself:     R15, R16
-/
-- MILESTONE (optional: change or delete)
theorem split_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hmeas : Measurable X) (hX : MemLp X 2 μ) (hnn : ∀ ω, 0 ≤ X ω) (θ : ℝ) (hθ : 0 ≤ θ) :
    μ[X] ≤ θ * μ[X] + ∫ ω, X ω * {ω | θ * μ[X] < X ω}.indicator 1 ω ∂μ := by
  sorry

/- SKELETON · cs_indicator   (milestone; prove it before paley_zygmund, whose last calc step it is)
  Below, 1_A ω is `A.indicator 1 ω`; write `(1 : Ω → ℝ)` where Lean cannot infer the type.
  1. Facts, each a `have`:
       Integrable (fun ω => X ω ^ 2) μ                                            R17
       Integrable (fun ω => X ω * 1_A ω) μ                                        R1, R3–R8 (as in split_mean)
       Integrable (A.indicator (1 : Ω → ℝ)) μ                                     R18
       hsq : ∀ ω, 1_A ω ^ 2 = 1_A ω                                               R7, R8
  2. key : ∀ t : ℝ, 0 ≤ μ.real A * (t * t) + (-2 * ∫ ω, X ω * 1_A ω ∂μ) * t + μ[fun ω => X ω ^ 2]
     (exactly this shape: R25 needs it). Fix t, then:
       e : (fun ω => (X ω - t * 1_A ω) ^ 2)
             = fun ω => X ω ^ 2 + ((-2 * t) * (X ω * 1_A ω) + (t * t) * 1_A ω)
           funext ω, then                                                         R19 with hsq ω
       h0 : 0 ≤ ∫ ω, (X ω - t * 1_A ω) ^ 2 ∂μ                                     R13, R20
       integrability of the two new summands and of their sum:                   R21, R11
       rewrite h0: e, split twice, pull out both constants, ∫ 1_A = P(A):        R24 (R15, R15, R22, R22, R23)
       finish:                                                                    R14
  3. Discriminant of key, unfold it, finish:                                      R25, R26, R27
-/
-- MILESTONE (optional: change or delete)
theorem cs_indicator {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (A : Set Ω) (hA : MeasurableSet A) :
    (∫ ω, X ω * A.indicator 1 ω ∂μ) ^ 2 ≤ μ[fun ω => X ω ^ 2] * μ.real A := by
  sorry

/- SKELETON · paley_zygmund
  0. Prove the milestones first: split_mean (used in step 2) and cs_indicator (step 3).
  1. Facts:
       h1 : the instance of split_mean at these μ X θ (pass every hypothesis)    have
       h3 : 0 ≤ (1 - θ) * μ[X]          (1 - θ ≥ 0 and E X ≥ 0)                  R12, R14, R13
  2. A three-step calc:                                                           R9
       (1 - θ) ^ 2 * (μ[X]) ^ 2 = ((1 - θ) * μ[X]) ^ 2                            ring
          _ ≤ (∫ ω, X ω * {ω | θ * μ[X] < X ω}.indicator 1 ω ∂μ) ^ 2              R28 with h3, R14 on h1
          _ ≤ _                                                                   cs_indicator, its event by R2
-/
-- BEGIN SPEC
theorem paley_zygmund {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hmeas : Measurable X) (hX : MemLp X 2 μ) (hnn : ∀ ω, 0 ≤ X ω)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) ^ 2 * (μ[X]) ^ 2 ≤ μ[fun ω => X ω ^ 2] * μ.real {ω | θ * μ[X] < X ω} :=
-- END SPEC
  sorry

end H056

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove the two milestones first. `split_mean`: pointwise `X ω ≤ θ E X + X ω · 1_A(ω)` (on `A` the
    indicator is `1` and `θ E X ≥ 0`; off `A`, `X ω ≤ θ E X`), integrated (R10). `cs_indicator`:
    the quadratic `t ↦ E[(X - t 1_A)²] ≥ 0` has a nonpositive discriminant (R25), as in M090.
    Then `(1 - θ) E X ≤ E[X 1_A]`, square it (R28), and apply `cs_indicator`.
H2. `split_mean`: `calc` with `integral_mono hXi ((integrable_const _).add hI) fun ω => ?_` (R9–R11),
    `by_cases h : θ * μ[X] < X ω` and `simp [Set.indicator, h]` in each case (R7, R8), then
    `rw [integral_add (integrable_const _) hI]; simp` (R15, R16). `hI` comes from `Integrable.mul_bdd`
    with `c := 1` (R3–R8). `cs_indicator`: prove
    `∀ t, 0 ≤ μ.real A * (t * t) + (-2 * ∫ ω, X ω * A.indicator 1 ω ∂μ) * t + μ[fun ω => X ω ^ 2]`
    from `0 ≤ ∫ ω, (X ω - t * A.indicator 1 ω) ^ 2 ∂μ` by `rw [e, integral_add …, integral_add …,
    integral_const_mul, integral_const_mul, integral_indicator_one hA] at h0; linarith` (R24).
H3. `hI := hXi.mul_bdd (c := 1) (measurable_const.indicator hA).aestronglyMeasurable (ae_of_all _ fun ω => ?_)`.
    `cs_indicator` ends `have := discrim_le_zero key; rw [discrim] at this; nlinarith`. Main:
    `calc (1 - θ) ^ 2 * μ[X] ^ 2 = ((1 - θ) * μ[X]) ^ 2 := by ring
      _ ≤ (∫ ω, X ω * {ω | θ * μ[X] < X ω}.indicator 1 ω ∂μ) ^ 2 := pow_le_pow_left₀ h3 (by linarith) 2
      _ ≤ _ := cs_indicator μ X hX _ (measurableSet_lt measurable_const hmeas)`.
-/
