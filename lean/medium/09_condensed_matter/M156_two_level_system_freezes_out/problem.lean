/- M156 | Two-level system freezes out | 10-15 min | Filter.atTop, Tendsto, exp limits, physlib
GOAL
  physlib's `twoState 0 ε` is a two-level system with energies `0` (ground) and `ε > 0` (excited).
  Show that its mean energy `U(b) = ∑ i, E i * p i(b)` tends to the ground-state energy `0` as the
  inverse temperature `b → ∞`, i.e. as `T → 0` (units with kB = 1).

GUIDE
  Entries R1–R19: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.TwoState

open CanonicalEnsemble Real Filter Topology

namespace M156

/- SKELETON · twoState_low_T
  1. Closed form first, for every `b` (intro b, then prove it):
       h : ∀ b, (twoState 0 ε).meanEnergyBetaReal b = ε / (Real.exp (b * ε) + 1)
       unfold U, p, Z and the two-term sum; energies 0, ε; the 0-terms drop:  R1 → R2 → R3 → R4 → R5 → R6, R7, R8
         (one `simp [...]` naming the three definitions and R4 does all of this)
       one exponential instead of two:                                    R9
       clear the fractions, which closes it:                              R10
  2. Replace the unapplied function in the goal by the closed form:       R11 → R12
  3. Constant over a denominator: reduce to `denominator → ∞`:           R13 with R14 (numerator `ε`)
  4. The denominator `fun b => rexp (b * ε) + 1` tends to `atTop`, built inside out:
       b → ∞, then b * ε → ∞ (uses hε), then rexp (b * ε) → ∞, then + 1:  R16 → R17 → R15, R18 → R19 with R14
-/
-- BEGIN SPEC
theorem twoState_low_T (ε : ℝ) (hε : 0 < ε) :
    Tendsto (twoState 0 ε).meanEnergyBetaReal atTop (𝓝 0) :=
-- END SPEC
  sorry

end M156

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Find a closed form first: the ground level has energy 0, so only the excited level contributes,
    `U(b) = ε e^{-bε} / (1 + e^{-bε}) = ε / (e^{bε} + 1)`. A constant over something that grows without
    bound tends to 0. `Tendsto` mentions `U` unapplied, so the closed form must replace the whole function.
H2. `have h : ∀ b, (twoState 0 ε).meanEnergyBetaReal b = ε / (Real.exp (b * ε) + 1)`: `intro b`, unfold with
    `simp [meanEnergyBetaReal, probabilityBetaReal, mathematicalPartitionFunctionBetaReal, Fin.sum_univ_two]`
    (R1–R8), then `rw [Real.exp_neg]` (R9) and `field_simp` (R10). Swap the function with
    `rw [show (twoState 0 ε).meanEnergyBetaReal = fun b => ε / (Real.exp (b * ε) + 1) from funext h]` (R11, R12).
H3. `apply Tendsto.div_atTop tendsto_const_nhds` (R13, R14) leaves the denominator; build it as
    `(Real.tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const hε)).atTop_add tendsto_const_nhds` (R15–R19).
-/
