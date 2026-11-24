/- E116 | Two-state partition function | 2-3 min | CanonicalEnsemble, twoState, partitionFunction, Fin.sum_univ_two, physlib
GOAL
  physlib's `twoState E₀ E₁ : CanonicalEnsemble (Fin 2)` is a two-level system: state `0` has energy
  `E₀`, state `1` has energy `E₁`. With energies `0` and `ε`, show `Z = 1 + e^{-βε}`.
BANNED: twoState_partitionFunction_apply, twoState_partitionFunction_apply_eq_cosh

GUIDE
  Entries R1–R6: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.TwoState

open CanonicalEnsemble

namespace E116

/- SKELETON · twoState_Z
  1. `Z` → the finite sum `∑ i, Real.exp (-↑T.β * (twoState 0 ε).energy i)`:  R1
  2. The sum over `Fin 2` → its terms at `0` and `1`:                       R2
  3. Plug in the two energies (only after step 2: R3, R4 need `energy 0`,
     `energy 1` literally, not `energy i` under the `∑`):                  R3, R4
  4. `-↑T.β * 0` → `0`, then `Real.exp 0` → `1`; the last `rw` closes the goal: R5 → R6
  After step 1, a single `simp` also performs steps 2–4.
-/
-- BEGIN SPEC
theorem twoState_Z (ε : ℝ) (T : Temperature) :
    (twoState 0 ε).partitionFunction T = 1 + Real.exp (-(T.β : ℝ) * ε) :=
-- END SPEC
  by
    rw [partitionFunction_of_fintype, Fin.sum_univ_two, twoState_energy_fst, twoState_energy_snd,
      mul_zero, Real.exp_zero]

end E116

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `partitionFunction` is defined through an integral; do not unfold it (plain `simp` does, and gets
    stuck). Rewrite it into a finite sum with `partitionFunction_of_fintype` (R1) first.
H2. After R1: split the sum over `Fin 2` (R2), plug in the energies (R3, R4), then clean up the zero
    energy (R5, R6). The instances `IsFinite` etc. are found automatically.
H3. `rw [partitionFunction_of_fintype, Fin.sum_univ_two, twoState_energy_fst, twoState_energy_snd]`,
    then `mul_zero` and `Real.exp_zero` in the same `rw` (or `rw [partitionFunction_of_fintype]; simp`).
-/
