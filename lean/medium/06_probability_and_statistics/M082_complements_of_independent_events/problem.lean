/- M082 | Complements of independent events | 10-15 min | IndepSet, ENNReal subtraction, measure algebra, mathlib
GOAL
  If the events `A` and `B` are independent under a probability measure `μ`, then so are `A` and `Bᶜ`
  (the complement of `B`).

BANNED: indepSet_of_measurableSet, indep_of_indep_of_le_right, indep_of_indep_of_le_left
GUIDE
  Entries R1–R11: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M082

/- SKELETON · indep_compl
  1. Goal `IndepSet A Bᶜ μ` → `μ (A ∩ Bᶜ) = μ A * μ Bᶜ` (needs `MeasurableSet Bᶜ`):   R1 with R2
  2. Hypothesis `h : IndepSet A B μ` → `h : μ (A ∩ B) = μ A * μ B`:                 R3
  3. Prove the split first, as its own fact:                                         have
       h1 : μ (A ∩ Bᶜ) = μ A - μ (A ∩ B)
     its proof: split `μ A` along `B`, cancel (needs `μ (A ∩ B) ≠ ⊤`), rewrite
     the difference as an intersection; `rw` then closes it:                         R4 → R6 with R5 → R7, R11
  4. Main goal: substitute h1, then h, then `μ Bᶜ`:                                  rw [h1], rw [h], R8
  5. Distribute `μ A * (1 - μ B)` (side condition `μ A ≠ ⊤`), drop `* 1`;
     `rw` closes the goal:                                                           R9 with R5 → R10, R11
-/
-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem indep_compl {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B) (h : IndepSet A B μ) :
    IndepSet A Bᶜ μ :=
-- END SPEC
  sorry

end M082

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Turn both `IndepSet` statements into product equations (R1 on the goal with `hB.compl`, R3 on `h`);
    the goal becomes `μ (A ∩ Bᶜ) = μ A * μ Bᶜ`. `ENNReal` subtraction truncates, so no `ring`.
H2. First prove `h1 : μ (A ∩ Bᶜ) = μ A - μ (A ∩ B)` by splitting `μ A` along `B` and cancelling;
    then rewrite with `h1`, `h`, `μ Bᶜ = 1 - μ B`, and distribute `μ A * (1 - μ B)`.
H3. `h1` is `rw [← measure_inter_add_sdiff A hB, ENNReal.add_sub_cancel_left (measure_ne_top μ _), Set.sdiff_eq]`;
    the main chain ends with `prob_compl_eq_one_sub hB, ENNReal.mul_sub (fun _ _ => measure_ne_top μ A), mul_one`.
-/
