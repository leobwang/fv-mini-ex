/- E095 | Events and probability measures | 2-3 min | IsProbabilityMeasure, ENNReal, Measure.real, measure_mono, complement, mathlib
GOAL
  Basic facts about a probability measure `μ` on a sample space `Ω`: the complement rule, monotonicity
  and `μ B ≤ 1` for `μ : Measure Ω`, then the complement rule for the real-valued `μ.real`.

GUIDE
  Entries R1–R6: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E095

/- SKELETON · events_basics
  1. Split the triple into its three conjuncts (or build it as one term
     `⟨_, _, _⟩` with the three proofs below):                              R1
  2. `μ Aᶜ = 1 - μ A`: the complement rule, given `hA`:                      R2
  3. `μ A ≤ μ B`: monotonicity, given `hAB`:                                 R3
  4. `μ B ≤ 1`: a probability is at most 1 (no arguments):                   R4
-/
-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem events_basics {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) (hA : MeasurableSet A) (hAB : A ⊆ B) :
    μ Aᶜ = 1 - μ A ∧ μ A ≤ μ B ∧ μ B ≤ 1 :=
-- END SPEC
  ⟨prob_compl_eq_one_sub hA, measure_mono hAB, prob_le_one⟩

/- SKELETON · real_compl
  1. Rewrite `μ.real Aᶜ` with the real complement rule, given `hA`:          R5
       goal: μ.real A + (1 - μ.real A) = 1
  2. Real arithmetic in the unknown `μ.real A`:                              R6
-/
-- BEGIN SPEC
theorem real_compl {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Set Ω) (hA : MeasurableSet A) : μ.real A + μ.real Aᶜ = 1 :=
-- END SPEC
  by rw [probReal_compl_eq_one_sub hA]; ring

end E095

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each conjunct of `events_basics` is one library lemma about measures (R2, R3, R4). `real_compl` is the
    real-valued complement rule (R5) plus arithmetic, done in `ℝ` because `ring` fails in `ENNReal`.
H2. `events_basics`: build the triple with the anonymous constructor `⟨_, _, _⟩` (R1); the complement rule
    takes `hA`, monotonicity takes `hAB`, `prob_le_one` takes nothing.
    `real_compl`: `rw` the term `μ.real Aᶜ` away, then `ring`.
H3. `⟨prob_compl_eq_one_sub hA, measure_mono hAB, prob_le_one⟩`;
    `rw [probReal_compl_eq_one_sub hA]; ring`.
-/
