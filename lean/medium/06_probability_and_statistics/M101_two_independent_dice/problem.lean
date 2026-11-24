/- M101 | Two independent dice (product measure) | 15 min | Measure.pi, iIndepFun_pi, counting, ENNReal, decide, mathlib
GOAL
  Build an independent pair instead of assuming one: two rolls of a fair die are the coordinates of
  `ω : Fin 2 → Fin 6` under the product measure. Prove the two rolls are independent, and that the
  total number of pips is 7 with probability 1/6.

GUIDE
  Entries R1–R21: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M101

open MeasureTheory ProbabilityTheory

-- BEGIN SPEC
/-- a fair die: face `i : Fin 6` shows `i + 1` pips -/
noncomputable abbrev die : Measure (Fin 6) := (PMF.uniformOfFintype (Fin 6)).toMeasure

/-- two independent rolls: the product measure on `Fin 2 → Fin 6` -/
noncomputable abbrev twoDice : Measure (Fin 2 → Fin 6) := Measure.pi fun _ => die
-- END SPEC

/- SKELETON · rolls_indep
  1. Build the fact first: all coordinates of the product measure are
     mutually independent, `hf := iIndepFun_pi (μ := …) (X := …) (…)`:     R1
       take `μ := fun _ : Fin 2 => die` and `X := fun _ (x : Fin 6) => x`
       (so `X i (ω i)` is `ω i`); its premise, each `X i` measurable:     R2 → R3
       `hf : iIndepFun (fun i ω => ω i) (Measure.pi fun x => die)`
  2. Pick out coordinates 0 and 1 of that family: apply hf.indepFun        R4
       side goal `0 ≠ 1` (in `Fin 2`):                                     decide
  Do not `apply iIndepFun.indepFun` or `apply iIndepFun_pi` straight on the
  goal: Lean cannot guess the family from `fun ω => ω 0` and `apply` fails.
  Build `hf` as a term (step 1), then use it (W1 shows both forms on coins).
-/
-- BEGIN SPEC
theorem rolls_indep : (fun ω : Fin 2 → Fin 6 => ω 0) ⟂ᵢ[twoDice] (fun ω => ω 1) :=
-- END SPEC
  sorry

/- SKELETON · prob_sum_seven
  1. Prove three facts first (`have`):
       hs    : the event (a `Set`) = ↑(Finset.univ.filter fun ω : Fin 2 → Fin 6 => same predicate)
                 R5, then `simp` (it applies R6, R7)
       hdie  : ∀ x : Fin 6, die {x} = 6⁻¹
                 intro x, then `simp [die]` (it does the work of R8, R9 and R15)
       hcard : (Finset.univ.filter fun ω : Fin 2 → Fin 6 => same predicate).card = 6
                 R10
  2. Real probability → sum of point masses:                     R11, rw [hs], R12 (right to left)
  3. One point mass, inside `∑ x with …, twoDice {x}`. `rw` cannot rewrite
     under the `∑` binder (the summand mentions the bound `x`), so put the
     unfolding and these entries into ONE `simp only [twoDice, …]`:
       twoDice, R13, hdie, R14, R15       the summand is now `6⁻¹ ^ 2`
  4. The sum of a constant, then the count:                       R16, hcard
       goal `(6 • 6⁻¹ ^ 2).toReal = 1 / 6`
  5. Into ℝ:                                                       R17, then simp with R19 named
       (it applies R18–R21), then norm_num
-/
-- BEGIN SPEC
theorem prob_sum_seven :
    twoDice.real {ω | ((ω 0 : ℕ) + 1) + ((ω 1 : ℕ) + 1) = 7} = 1 / 6 :=
-- END SPEC
  sorry

end M101

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Independence: the coordinates of a product of probability measures are mutually independent (R1);
    two members of an independent family are independent (R4). Probability: the event is a finite set
    of outcomes, each of mass `6⁻¹ * 6⁻¹`, and there are 6 of them.
H2. Independence: build R1's fact with every `X i = id` as a term, naming `μ` and `X` (measurability: R2,
    R3); then R4 on it with `(0 : Fin 2) ≠ 1`.
    Probability: prove `hs` (`ext ω; simp`), `hdie` (`simp [die]`) and `hcard` (`decide`) first, then
    `rw [measureReal_def, hs, ← sum_measure_singleton]`.
H3. Independence: `iIndepFun_pi (μ := fun _ : Fin 2 => die) (X := fun _ (x : Fin 6) => x) …`, then
    `.indepFun` with a proof of `(0 : Fin 2) ≠ 1`. Probability: after the rewrites, `simp only [twoDice,
    Measure.pi_singleton, hdie, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.sum_const,
    hcard]`, then `rw [ENNReal.toReal_nsmul]`, `simp [ENNReal.toReal_inv]`, `norm_num`.
-/
