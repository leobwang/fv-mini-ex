/- M161 | Entropy of a two-level system | 15-20 min | thermodynamicEntropy, shannonEntropy, Real.log_div, generalize, physlib
GOAL
  Compute the entropy of physlib's two-level system `twoState 0 ε` (energies `0` and `ε`) at temperature
  `T`, with `β = 1 / (kB T)`: `S = kB (log (1 + e^{-βε}) + βε / (e^{βε} + 1))`. physlib only states this
  as an `informal_lemma`; prove it.
BANNED: twoState_probability_fst, twoState_probability_snd, twoState_helmholtzFreeEnergy_eq, twoState_helmholtzFreeEnergy_eq_T_neq_zero, twoState_meanEnergy_eq

GUIDE
  Entries R1–R20: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.TwoState

open CanonicalEnsemble Constants Real

namespace M161

/- SKELETON · twoState_entropy
  1. Switch to the finite formula `-kB * ∑ i, p i * log (p i)`:                 R1, R2
  2. Prove the two probabilities as facts, each by one `simp [...]` naming R3, R4, R5
     (R6–R8 it applies by itself); state them in simp's form `-(↑T.β * ε)`:     R3 → R8
       hp0 : (twoState 0 ε).probability T 0 = 1 / (1 + rexp (-(↑T.β * ε)))
       hp1 : (twoState 0 ε).probability T 1 = rexp (-(↑T.β * ε)) / (1 + rexp (-(↑T.β * ε)))
  3. Split the entropy sum, then substitute the facts:                         R5, rw [hp0, hp1]
  4. Turn the spec's `-↑T.β * ε` into `-(↑T.β * ε)`, then name `↑T.β * ε` as x:  R9, R10
  5. hD : 0 < 1 + rexp (-x)                                                    R11
     Split both logarithms (side goals: `1 ≠ 0`, `rexp (-x) ≠ 0`, `hD.ne'`):   R13 (R11, R12), R14, R15
  6. he : rexp x * rexp (-x) = 1                                               R16, then simp
     hx : x / (rexp x + 1) = x * rexp (-x) / (1 + rexp (-x))                    R17 (R11, R12) → R18 with he
     rw [hx]
  7. Clear the denominators and finish:                                        R19 → R20
-/
-- BEGIN SPEC
theorem twoState_entropy (ε : ℝ) (T : Temperature) :
    (twoState 0 ε).thermodynamicEntropy T =
      kB * (Real.log (1 + Real.exp (-(T.β : ℝ) * ε)) +
        (T.β : ℝ) * ε / (Real.exp ((T.β : ℝ) * ε) + 1)) :=
-- END SPEC
  by
    rw [thermodynamicEntropy_eq_shannonEntropy, shannonEntropy]
    have hp0 : (twoState 0 ε).probability T 0 = 1 / (1 + Real.exp (-((T.β : ℝ) * ε))) := by
      simp [probability, mathematicalPartitionFunction_of_fintype, Fin.sum_univ_two]
    have hp1 : (twoState 0 ε).probability T 1 =
        Real.exp (-((T.β : ℝ) * ε)) / (1 + Real.exp (-((T.β : ℝ) * ε))) := by
      simp [probability, mathematicalPartitionFunction_of_fintype, Fin.sum_univ_two]
    rw [Fin.sum_univ_two, hp0, hp1, show -(T.β : ℝ) * ε = -((T.β : ℝ) * ε) by ring]
    -- WHY: `generalize`, not `set`: `ring` would treat a `set` variable and `↑T.β * ε` as different atoms.
    generalize (T.β : ℝ) * ε = x
    have hD : 0 < 1 + Real.exp (-x) := by positivity
    rw [Real.log_div (by norm_num) hD.ne', Real.log_div (by positivity) hD.ne',
      Real.log_one, Real.log_exp]
    have he : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    have hx : x / (Real.exp x + 1) = x * Real.exp (-x) / (1 + Real.exp (-x)) := by
      rw [div_eq_div_iff (by positivity) hD.ne']
      linear_combination (-x) * he
    rw [hx]
    field_simp
    ring

end M161

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Switch to the finite formula `S = -kB ∑ p log p` (R1, R2), compute the two Boltzmann probabilities
    as `have` facts, and then it is pure algebra in one variable `x = βε` (R10).
H2. Each probability: one `simp [probability, mathematicalPartitionFunction_of_fintype, Fin.sum_univ_two]`.
    Then `rw [Fin.sum_univ_two, hp0, hp1, show -(T.β : ℝ) * ε = -((T.β : ℝ) * ε) by ring]` and
    `generalize (T.β : ℝ) * ε = x` (not `set`). With `hD : 0 < 1 + rexp (-x)`, split the logs (R13–R15).
H3. `rw [Real.log_div (by norm_num) hD.ne', Real.log_div (by positivity) hD.ne', Real.log_one, Real.log_exp]`;
    rewrite `x / (rexp x + 1) = x * rexp (-x) / (1 + rexp (-x))` by `div_eq_div_iff` and
    `linear_combination (-x) * he` with `he : rexp x * rexp (-x) = 1`; then `field_simp; ring`.
-/
