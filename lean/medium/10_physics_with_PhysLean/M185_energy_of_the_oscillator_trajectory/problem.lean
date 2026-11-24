/- M185 | Energy of the oscillator trajectory | 15-20 min | inner products, norm_smul, sin²+cos², linear_combination, physlib
GOAL
  physlib solves the harmonic oscillator explicitly: `x(t) = cos(ωt) x₀ + (sin(ωt)/ω) v₀`. By direct
  computation, show that its energy at every time `t` is `½ (m ‖v₀‖² + k ‖x₀‖²)`.

BANNED: trajectory_energy, energy_conservation_of_equationOfMotion, energy_conservation_of_equationOfMotion', exact?, apply?, rw?, hint, observe, try?

GUIDE
  Entries R1–R15: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution

open ClassicalMechanics HarmonicOscillator Time Real InnerProductSpace

namespace M185

/- SKELETON · energy_along_trajectory
  1. MILESTONE first, so `S.k` can be traded for `S.ω` later (used in step 6):
       hk : S.k = S.m * S.ω ^ 2                     proof: R1, then R2
  2. Unfold the energy:                                                     R3
  3. Substitute the velocity, BEFORE the trajectory is unfolded:            R4
  4. One `simp only [...]` that unfolds the position and expands every
     inner product into ⟪x₀, x₀⟫_ℝ, ⟪v₀, v₀⟫_ℝ, ⟪x₀, v₀⟫_ℝ:                   R5, R6, R7, R8, R9, R10, R11
  5. Only now: ⟪x₀, x₀⟫_ℝ → ‖x₀‖ ^ 2 and ⟪v₀, v₀⟫_ℝ → ‖v₀‖ ^ 2:               R12 (twice)
  6. Replace S.k by the milestone:                                          rw [hk]
  7. Clear every `/ S.ω`:                                                   R13
  8. Close modulo sin² + cos² = 1 at the angle `S.ω * t.val`; read the
     coefficient off the goal left by step 7:                               R15 with R14
-/
-- BEGIN SPEC
theorem energy_along_trajectory (S : HarmonicOscillator) (IC : InitialConditions) (t : Time) :
    S.energy (IC.trajectory S) t = 1/2 * (S.m * ‖IC.v₀‖ ^ 2 + S.k * ‖IC.x₀‖ ^ 2) :=
-- END SPEC
  sorry

end M185

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold the energy, substitute the velocity and the position, and expand all inner products into
    `‖x₀‖²`, `‖v₀‖²` and `⟪x₀, v₀⟫_ℝ`. The cross terms cancel once `k = m ω²`; what remains is `sin² + cos² = 1`.
H2. Prove `hk : S.k = S.m * S.ω ^ 2` first (`ω_sq`, then `field_simp [S.m_ne_zero]`). Then `simp only` the three
    energy definitions, `rw [InitialConditions.trajectory_velocity]` (before `trajectory_eq`), expand with one
    `simp only` (R5–R11), and only afterwards turn `⟪x, x⟫_ℝ` into `‖x‖ ^ 2`. `rw [hk]`, `field_simp [S.ω_ne_zero]`.
H3. The last line is `linear_combination (_) * Real.sin_sq_add_cos_sq (S.ω * t.val)`, and the coefficient `(_)`
    is the right-hand side of the goal that `field_simp` leaves (R15: whatever multiplies `sin ^ 2` there).
-/
