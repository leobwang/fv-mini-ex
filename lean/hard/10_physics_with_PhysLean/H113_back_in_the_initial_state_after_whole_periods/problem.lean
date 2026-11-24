/- H113 | Back in the initial state exactly after whole periods | 1-1.5 h | trigonometry, inner products, Real.cos_eq_one_iff, iff, physlib
GOAL
  A non-trivial oscillator (`x₀ ≠ 0` or `v₀ ≠ 0`) is back at its initial position **and** velocity at time `t`
  if and only if `t` is an integer multiple of the period `2π/ω`.

BANNED: HarmonicOscillator.return_time, HarmonicOscillator.trajectory_periodic, exact?, apply?, try?, hint

GUIDE
  Entries R1–R29: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution

open ClassicalMechanics HarmonicOscillator Time Real InnerProductSpace

namespace H113

/- SKELETON · det_pos   (milestone 1: ⟪v₀,v₀⟫ + ω²⟪x₀,x₀⟫ > 0; used in milestone 2 to cancel that factor)
  1. Put the sign facts in the context:
       hx : 0 ≤ ⟪IC.x₀, IC.x₀⟫_ℝ,  hv : 0 ≤ ⟪IC.v₀, IC.v₀⟫_ℝ                 R1, R1
       hω : 0 < S.ω ^ 2                                                     R2 → R3
  2. Split `non_trivial` into `h : IC.x₀ ≠ 0` and `h : IC.v₀ ≠ 0`:            R4
  3. In each case: the nonzero vector has a positive square; hand that fact
     to `nlinarith`, which also uses hx, hv, hω:                            R5 → R6
-/
-- MILESTONE (optional: change or delete)
/-- A non-trivial initial state has positive "energy-like" quantity `‖v₀‖² + ω²‖x₀‖²`. -/
theorem det_pos (S : HarmonicOscillator) (IC : InitialConditions)
    (non_trivial : IC.x₀ ≠ 0 ∨ IC.v₀ ≠ 0) :
    0 < ⟪IC.v₀, IC.v₀⟫_ℝ + S.ω ^ 2 * ⟪IC.x₀, IC.x₀⟫_ℝ := by
  sorry

/- SKELETON · cos_eq_one   (milestone 2: return ⇒ cos (ω t) = 1; uses milestone 1; used for (→) in the main theorem)
  1. Replace position and velocity by their formulas, in `hx` and `hv`:      R7, R8
  2. Pair them: h1 from `hx` with `⟪IC.x₀, ·⟫_ℝ`, h2 from `hv` with `⟪IC.v₀, ·⟫_ℝ`:   R9, R9
  3. Expand both inner products (one `simp only … at h1 h2`):                R10, R11, R12
  4. Make h2 mention `⟪IC.x₀, IC.v₀⟫_ℝ` like h1 does:                         R13
  5. Clear `/ S.ω` in h1 (put `S.ω ≠ 0` in the context first):               R14 → R15
  6. key : (⟪IC.v₀, IC.v₀⟫_ℝ + S.ω ^ 2 * ⟪IC.x₀, IC.x₀⟫_ℝ) * (cos (S.ω * t.val) - 1) = 0
       proof: one linear combination of h1 and h2 (find the coefficient)    R16
  7. Split the product: the first factor contradicts milestone 1, the second
     gives the goal:                                                        R17 → R4; R18, R19; R20
-/
-- MILESTONE (optional: change or delete)
/-- Returning to the initial state forces `cos (ω t) = 1`. -/
theorem cos_eq_one (S : HarmonicOscillator) (IC : InitialConditions)
    (non_trivial : IC.x₀ ≠ 0 ∨ IC.v₀ ≠ 0) (t : Time)
    (hx : IC.trajectory S t = IC.x₀) (hv : ∂ₜ (IC.trajectory S) t = IC.v₀) :
    Real.cos (S.ω * t.val) = 1 := by
  sorry

/- SKELETON · state_at_period   (milestone 3: the (←) direction; used in the main theorem)
  1. hωt : S.ω * t.val = ((2 * n : ℤ) : ℝ) * π
       proof: rw [← hn], then                                               R21, R22 (with R14)
  2. hc : cos (S.ω * t.val) = 1
       proof: rw [hωt], then R23, witness `n`, the equation by              R21, ring
  3. hs : sin (S.ω * t.val) = 0         proof: rw [hωt], then                R24
  4. Split the `∧`:                                                         constructor
  5. Each side: the formula on the goal, then collapse with hc, hs:         R7 / R8, R25 → R26
-/
-- MILESTONE (optional: change or delete)
/-- The (←) direction: after `n` whole periods the state is the initial one. -/
theorem state_at_period (S : HarmonicOscillator) (IC : InitialConditions) (t : Time) (n : ℤ)
    (hn : (n : ℝ) * (2 * π / S.ω) = t.val) :
    IC.trajectory S t = IC.x₀ ∧ ∂ₜ (IC.trajectory S) t = IC.v₀ := by
  sorry

/- SKELETON · returns_iff_whole_periods
  Prove the milestones first: milestone 1 feeds milestone 2; milestone 2 gives (→), milestone 3 gives (←).
  1. Split the `↔`:                                                         R27
  2. (→) Take the `∧` apart:                                                R28
     cos (S.ω * t.val) = 1 from milestone 2, read as an `∃` and opened:     R23 (`.mp`) → R29
     give the witness:                                                      refine ⟨n, ?_⟩
     clear `/ S.ω` in the goal, then use `hn`:                              R22 (with R14), R16
  3. (←) Take the `∃` apart and use milestone 3:                            R28, exact
-/
-- BEGIN SPEC
theorem returns_iff_whole_periods (S : HarmonicOscillator) (IC : InitialConditions)
    (non_trivial : IC.x₀ ≠ 0 ∨ IC.v₀ ≠ 0) (t : Time) :
    (IC.trajectory S t = IC.x₀ ∧ ∂ₜ (IC.trajectory S) t = IC.v₀) ↔
      ∃ n : ℤ, (n : ℝ) * (2 * π / S.ω) = t.val :=
-- END SPEC
  sorry

end H113

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. (←) is direct: `ω t = 2nπ`, so `cos = 1` and `sin = 0` and both formulas collapse (milestone 3).
    (→) is the real work: pair the position equation with `x₀` and the velocity equation with `v₀`
    (`congrArg (fun w => ⟪IC.x₀, w⟫_ℝ) hx`) to get two scalar equations in `c = cos ωt`, `s = sin ωt`,
    `xx = ⟪x₀,x₀⟫`, `vv = ⟪v₀,v₀⟫`, `xv = ⟪x₀,v₀⟫`.
H2. The scalar equations are `c·xx + (s/ω)·xv = xx` and `−ω·s·xv + c·vv = vv`. Clear `/ω` in the first
    (it becomes `ω·c·xx + s·xv = ω·xx`), multiply it by `ω` and add the second: the `s·xv` terms cancel,
    leaving `(vv + ω²·xx)(c − 1) = 0`; `det_pos` rules out the first factor. For `det_pos`, split
    `non_trivial` and use `nlinarith` with `real_inner_self_pos.mpr h`. Both directions go through
    `Real.cos_eq_one_iff`.
H3. `cos_eq_one`: after the two `rw … at`, the pairings and
    `simp only [inner_add_right, real_inner_smul_right] at h1 h2`, `rw [real_inner_comm IC.x₀ IC.v₀] at h2`,
    `have hω := S.ω_ne_zero`, `field_simp at h1`, prove
    `key : (vv + ω²·xx) * (cos (S.ω * t.val) - 1) = 0 := by linear_combination S.ω * h1 + h2`.
    (←): `have : S.ω * t.val = (2 * n : ℤ) * π := by rw [← hn]; push_cast; field_simp [S.ω_ne_zero]`.
    (→): after `obtain ⟨n, hn⟩` and `refine ⟨n, ?_⟩`: `field_simp [S.ω_ne_zero]; linear_combination hn`.
-/
