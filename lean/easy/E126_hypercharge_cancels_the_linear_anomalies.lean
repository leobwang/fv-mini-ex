/- E126 | Hypercharge cancels the linear anomalies | 3 min | anomaly cancellation, linear maps, decomp lemmas, physlib
GOAL
  One Standard Model family plus a right-handed neutrino has 6 species `Q, U, D, L, E, N`. Show that the
  hypercharge assignment `Y = (1, -4, 2, -3, 6, 0)` satisfies the gravitational, SU(2) and SU(3) anomaly
  equations `accGrav Y = 0`, `accSU2 Y = 0`, `accSU3 Y = 0`.

REFERENCE
  `(SMνCharges n).Charges` = rational charges of 6 species × `n` families; `Q S i` = charge of `Q` in family `i`.
  #check SMνACCs.accGrav_decomp  -- accGrav S = 6 * ∑ i, Q S i + 3 * ∑ i, U S i + ... + ∑ i, N S i
  #check SMνACCs.accSU2_decomp   -- accSU2 S = 3 * ∑ i, Q S i + ∑ i, L S i
  #check SMνACCs.accSU3_decomp   -- accSU3 S = 2 * ∑ i, Q S i + ∑ i, U S i + ∑ i, D S i
  #check SMνCharges.sum_one      -- for one family, a sum over families is its single term
  #check SMνCharges.toSpecies_one -- (toSpecies j) S ⟨0, _⟩ = S j   (`Q = toSpecies 0`, ..., `N = toSpecies 5`)
  `simp [Y]` then unfolds `Y` and evaluates `![1, -4, 2, -3, 6, 0] j`; `norm_num` finishes the ℚ arithmetic.
NOTE: use sum_one, toSpecies_one before `simp [Y]` (unfolding Y first blocks them); `Y 0` fails (no numerals).
-/
import Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.Basic

open SMνCharges SMνACCs

namespace E126

-- BEGIN SPEC
/-- Hypercharge of one family, in the species order `(Q, U, D, L, E, N)` (normalized to integers). -/
def Y : (SMνCharges 1).Charges := ![1, -4, 2, -3, 6, 0]
-- END SPEC

-- BEGIN SPEC
theorem Y_linear : accGrav Y = 0 ∧ accSU2 Y = 0 ∧ accSU3 Y = 0 :=
-- END SPEC
  sorry

end E126

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Split the conjunction with `refine ⟨?_, ?_, ?_⟩`; each anomaly is a linear map, so first write it as
    sums over species and families.
H2. `rw [accGrav_decomp]` (resp. `_SU2`, `_SU3`); with one family, `sum_one` and `toSpecies_one` turn
    `∑ i, Q Y i` into the plain entry of `Y`. Then compute.
H3. `rw [accGrav_decomp]; simp only [sum_one, toSpecies_one]; simp [Y]; norm_num` (the SU(2) goal is already
    closed by `simp [Y]`).
-/
