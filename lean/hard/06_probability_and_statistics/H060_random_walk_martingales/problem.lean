/- H060 | Random-walk martingales | 1.5-2 h | Martingale, natural filtration, condExp, independence, pull-out, mathlib
GOAL
  Independent, integrable, mean-zero steps `X 0, X 1, …`; the walk is `Sₙ = X 0 + … + X n`. Show `S` is a
  martingale for the natural filtration `ℱₙ = σ(X 0, …, X n)` (what is known after step `n`): adapted,
  integrable, and `E[Sₙ₊₁ - Sₙ | ℱₙ] = 0`. For `±1` steps, show `Sₙ² - (n + 1)` is a martingale too.
BANNED: condExp_natural_ae_eq_of_lt

GUIDE
  Entries R1–R40: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H060

open MeasureTheory ProbabilityTheory

/- SKELETON · partial_sum_adapted   (milestone 1; used by both spec theorems)
  Goal: the partial sum Sₙ is ℱₙ-measurable (ℱₙ = Filtration.natural X hX n; the infoview hides [ℱₙ]).
  1. A finite sum is measurable if each summand is:                       R1
  2. intro i hi, and turn hi : i ∈ range (n + 1) into i ≤ n:              R2
  3. X i is ℱᵢ-measurable:                                                R3
     ℱᵢ ≤ ℱₙ from step 2:                                                 R4
     move the measurability up from ℱᵢ to ℱₙ:                             R5 (with the R4 fact)
-/
-- MILESTONE (optional: change or delete)
theorem partial_sum_adapted {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, StronglyMeasurable (X i)) (n : ℕ) :
    StronglyMeasurable[Filtration.natural X hX n] (fun ω => ∑ i ∈ Finset.range (n + 1), X i ω) := by
  sorry

/- SKELETON · increment_condExp   (milestone 2; used by both spec theorems)
  1. h : μ[X (n + 1) | ℱₙ] =ᵐ[μ] fun _ => μ[X (n + 1)]                   R6, with
       m₁ := σ(X (n + 1)), m₂ := ℱₙ, and its four arguments:
       σ(X (n + 1)) ≤ mΩ                                                  R7 → R8
       ℱₙ ≤ mΩ                                                            R9
       X (n + 1) is σ(X (n + 1))-measurable                               R10 → R11
       Indep σ(X (n + 1)) ℱₙ, from n < n + 1                              R12
  2. Replace the mean by 0 inside h:                                      R13 (with hmean)
  3. exact h   (`fun x => 0` and `0` are the same function)
-/
-- MILESTONE (optional: change or delete)
theorem increment_condExp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, StronglyMeasurable (X i))
    (hindep : iIndepFun X μ) (hmean : ∀ i, μ[X i] = 0) (n : ℕ) :
    μ[X (n + 1) | Filtration.natural X hX n] =ᵐ[μ] 0 := by
  sorry

/- SKELETON · sq_increment   (milestone 3; used by walk_sq_martingale)
  1. Peel the last term off the longer sum only:                          R14
  2. ↑(n + 1) → ↑n + 1:                                                    R15
  3. What is left is (s + x)² - … = 2·s·x modulo x² = 1:                   R16 with h
-/
-- MILESTONE (optional: change or delete)
theorem sq_increment (X : ℕ → ℝ) (n : ℕ) (h : X (n + 1) ^ 2 = 1) :
    (∑ i ∈ Finset.range (n + 1 + 1), X i) ^ 2 - ((n + 1 : ℕ) + 1 : ℝ)
      - ((∑ i ∈ Finset.range (n + 1), X i) ^ 2 - (n + 1))
      = 2 * (∑ i ∈ Finset.range (n + 1), X i) * X (n + 1) := by
  sorry

/- SKELETON · walk_martingale
  Prove milestones 1 (partial_sum_adapted) and 2 (increment_condExp) first.
  1. Reduce to adapted / integrable / increments:                         R17
  2. hadp: StronglyAdapted is `∀ n, …` (R18), so milestone 1 applied to X hX is it.
  3. hint: for each n, a finite sum of integrable X i:                    R19
  4. hf: intro n, then first prove
       e : (fun ω => ∑ … range (n + 1 + 1) …) - (fun ω => ∑ … range (n + 1) …) = X (n + 1)
     (copy both sides from the goal):  funext ω, then simp with R14's lemma (R20 is applied by simp)
     rw [e], then milestone 2.
-/
-- BEGIN SPEC
theorem walk_martingale {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, StronglyMeasurable (X i)) (hint : ∀ i, Integrable (X i) μ)
    (hindep : iIndepFun X μ) (hmean : ∀ i, μ[X i] = 0) :
    Martingale (fun n ω => ∑ i ∈ Finset.range (n + 1), X i ω) (Filtration.natural X hX) μ :=
-- END SPEC
  sorry

/- SKELETON · walk_sq_martingale
  Uses milestones 1, 2, 3. First collect facts with `have`, in this order:
  1. hb : ∀ i ω, |X i ω| ≤ 1  and  hsq : ∀ i ω, X i ω ^ 2 = 1:   rcases hpm i ω, then simp
  2. hint : ∀ i, Integrable (X i) μ     bounded by 1:                    R22, R23, R24 (R21: ‖·‖ = |·|)
  3. set S := fun n ω => ∑ i ∈ Finset.range (n + 1), X i ω with hS:        R25
     (the goal keeps its ∑ form: it never contains that exact `fun`; S is
      the same function by definition, so `exact` accepts either form)
  4. hSm : ∀ n, S n is ℱₙ-measurable:                                      milestone 1
  5. hSb : ∀ n ω, |S n ω| ≤ n + 1, a calc:                                 R26, R27 (with hb), R28
  6. hSae : ∀ n, AEStronglyMeasurable (S n) μ:                             R5 with R9, then R23
  7. hSi : ∀ n, Integrable (S n) μ:                                        R22, R24 with hSb
  Then:
  8. Reduce to three goals:                                                R17
  9. hadp: intro n (R18); S n ^ 2 - const is ℱₙ-measurable:              R31
       (the goal shows an unreduced `(fun n ω => …) n`; `exact` sees through it)
  10. hint: intro n; h2 : Integrable (fun ω => S n ω ^ 2) μ:              R22 with R32,
        bound ‖S n ω ^ 2‖ ≤ (n + 1) ^ 2 for all ω:                        R24, then R21, R29, R30 (abs_nonneg, hSb)
      then subtract the constant:                                         R33
  11. hf: intro n; e : increment = (fun ω => 2 * S n ω) * X (n + 1)
        (copy the increment from the goal; `S n ω` may replace the sum)
        funext ω, milestone 3 at (fun i => X i ω) with hsq;  rw [e]
      hprod : Integrable ((fun ω => 2 * S n ω) * X (n + 1)) μ:           R34 → R35, with R23 for
        X (n + 1) and the bound hb through R24
      pull the ℱₙ-measurable factor out, chain:                           R36, R37 → R38
      go pointwise with milestone 2:                                      R39
      finish:                                                             R40 (simp [hω])
-/
-- BEGIN SPEC
theorem walk_sq_martingale {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, StronglyMeasurable (X i)) (hpm : ∀ i ω, X i ω = 1 ∨ X i ω = -1)
    (hindep : iIndepFun X μ) (hmean : ∀ i, μ[X i] = 0) :
    Martingale (fun n ω => (∑ i ∈ Finset.range (n + 1), X i ω) ^ 2 - (n + 1))
      (Filtration.natural X hX) μ :=
-- END SPEC
  sorry

end H060

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both theorems: `apply martingale_of_condExp_sub_eq_zero_nat` (R17) leaves adapted, integrable, and
    `μ[Sₙ₊₁ - Sₙ | ℱₙ] =ᵐ 0`. The increment of `S` is `X (n + 1)`, independent of `ℱₙ`, so its conditional
    expectation is its mean `0` (milestone 2). For the square walk the increment is `2 Sₙ X (n + 1)`
    (milestone 3): `2 Sₙ` is known at time `n`, so it comes out of the conditional expectation.
H2. Adapted: `X i` is `ℱᵢ`-measurable and `ℱᵢ ≤ ℱₙ` for `i ≤ n`, then sum (R1–R5). Square walk: no
    `hint` is given; `|X i| ≤ 1` and `|Sₙ| ≤ n + 1` give integrability by `Integrable.of_bound` (R22).
    Increments: prove `e : <increment as in the goal> = …` by `funext`, `rw [e]`, then R37 → R38 → R39 with
    milestone 2.
H3. Milestone 2: `condExp_indep_eq (hX (n + 1)).measurable.comap_le (Filtration.le _ n)
      (comap_measurable (X (n + 1))).stronglyMeasurable (hindep.indep_comap_natural_of_lt hX n.lt_succ_self)`,
    then `rw [hmean] at h`. Square walk, last goal:
    `refine (condExp_mul_of_stronglyMeasurable_left ((hSm n).const_mul 2) hprod (hint (n + 1))).trans ?_`,
    then `filter_upwards [increment_condExp μ X hX hindep hmean n] with ω hω` and `simp [hω]`.
-/
