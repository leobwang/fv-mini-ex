/- E101 | Laws: the Gaussian | 2 min | HasLaw, gaussianReal, distribution of a random variable, mathlib
GOAL
  If `X` has the normal law `N(m, v)` under `P`, then `E[X] = m` and `Var(X) = v`.

GUIDE
  Entries R1–R5: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E101

/- SKELETON · gaussian_moments
  The goal prints as `∫ (x : Ω), X x ∂P = m ∧ Var[X; P] = ↑v`.
  1. Split the two moments (a tactic, or the term `⟨by …, by …⟩`):      R1
  2. Mean: move from `X` under `P` to its law, then ask the Gaussian:   R2 → R3
  3. Variance: the same two moves for `Var`:                            R4 → R5
     (each `rw` closes the final `a = a` by itself)
-/
-- BEGIN SPEC
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem gaussian_moments {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) (m : ℝ)
    (v : ℝ≥0) (hX : HasLaw X (gaussianReal m v) P) : P[X] = m ∧ Var[X; P] = v :=
-- END SPEC
  ⟨by rw [hX.integral_eq, integral_id_gaussianReal], by rw [hX.variance_eq, variance_id_gaussianReal]⟩

end E101

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Neither conjunct mentions `Ω` once you replace `X` by its law `gaussianReal m v`: the mean and the
    variance of `X` are those of its law.
H2. Split the `∧` (R1). Each half is two rewrites: first the `HasLaw` lemma used through `hX` by dot
    notation (R2 / R4), then the Gaussian fact about `∫ x, x ∂gaussianReal m v` / `Var[id; gaussianReal m v]`
    (R3 / R5).
H3. `⟨by rw [hX.integral_eq, integral_id_gaussianReal], by rw [hX.variance_eq, variance_id_gaussianReal]⟩`.
-/
