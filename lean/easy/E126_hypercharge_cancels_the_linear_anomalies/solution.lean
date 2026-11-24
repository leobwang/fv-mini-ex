/- E126 | Hypercharge cancels the linear anomalies | 3 min | anomaly cancellation, linear maps, decomp lemmas, physlib
GOAL
  One Standard Model family plus a right-handed neutrino has 6 species `Q, U, D, L, E, N`. Show that the
  hypercharge assignment `Y = (1, -4, 2, -3, 6, 0)` satisfies the gravitational, SU(2) and SU(3) anomaly
  equations `accGrav Y = 0`, `accSU2 Y = 0`, `accSU3 Y = 0`.

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.Basic

open SMνCharges SMνACCs

namespace E126

-- BEGIN SPEC
/-- Hypercharge of one family, in the species order `(Q, U, D, L, E, N)` (normalized to integers). -/
def Y : (SMνCharges 1).Charges := ![1, -4, 2, -3, 6, 0]
-- END SPEC

/- SKELETON · Y_linear
  1. Split the three equations:                                             R1
  2. In each goal, in this order (collapse the sums BEFORE unfolding `Y`):
       anomaly → one sum per species: the matching `_decomp` lemma         R2 / R3 / R4
       one family: each sum → its single term                              R5
       species in family 0 → entry of `Y`                                  R6
       unfold `Y` and read off the entries                                 R7 (with `Y`)
       finish the rational arithmetic, if a goal is left                   R8
-/
-- BEGIN SPEC
theorem Y_linear : accGrav Y = 0 ∧ accSU2 Y = 0 ∧ accSU3 Y = 0 :=
-- END SPEC
  by
    refine ⟨?_, ?_, ?_⟩
    · rw [accGrav_decomp]
      simp only [sum_one, toSpecies_one]
      simp [Y]
      norm_num
    · rw [accSU2_decomp]
      simp only [sum_one, toSpecies_one]
      simp [Y]
    · rw [accSU3_decomp]
      simp only [sum_one, toSpecies_one]
      simp [Y]
      norm_num

end E126

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Split the conjunction (R1). Each anomaly is a linear map defined as a sum over families; its
    `_decomp` lemma (R2–R4) writes it as one sum per species, which is the form you can compute with.
H2. With one family, `sum_one` (R5) turns `∑ i, Q Y i` into one term and `toSpecies_one` (R6) turns that
    term into an entry of `Y`. Only then unfold `Y` (R7) and compute (R8).
H3. Per conjunct: `rw [accGrav_decomp]; simp only [sum_one, toSpecies_one]; simp [Y]; norm_num`
    (`accSU2_decomp` / `accSU3_decomp` for the others; the SU(2) goal is already closed by `simp [Y]`).
-/
