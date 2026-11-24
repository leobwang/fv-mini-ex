/- M192 | A damped oscillator never gains energy | 15-20 min | DampedHarmonicOscillator, Time vs ℝ, chain rule through toRealCLE, antitone_of_deriv_nonpos, physlib
GOAL
  Along any smooth solution `x` of physlib's damped equation `m ẍ + γ ẋ + k x = 0` (with `γ ≥ 0`), the
  energy `E t = ½ m ⟪ẋ, ẋ⟫_ℝ + ½ k ⟪x, x⟫_ℝ` never increases: `t₁ ≤ t₂ → E t₂ ≤ E t₁` (`⟪u, v⟫_ℝ` = dot product).

GUIDE
  Entries R1–R22: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic

open ClassicalMechanics Time ContDiff InnerProductSpace

namespace M192

/- SKELETON · energy_antitone
  1. The energy is differentiable:   hE : Differentiable ℝ (S.energy x)          R1
  2. Move to ℝ, keeping the body (`let`, not `have`):
       g : ℝ → ℝ := S.energy x ∘ Time.toRealCLE.symm                              R2
  3. hg : Differentiable ℝ g                                                      R3, R4
  4. hderiv : ∀ r, deriv g r ≤ 0.  After `intro r`:
     a. MILESTONE, prove first:  e : deriv g r = ∂ₜ (S.energy x) (Time.toRealCLE.symm r)
          chain rule:                    R6 → R7 (its arguments: R5, R4) → R8 → R9 → R10
          match the directions `↑toRealCLE.symm 1` and `1`:   R11 → R12 → R13, R14
     b. rw [e], then the dissipation rate:                                        R15
     c. the two signs, `0 ≤ S.γ` and `0 ≤ ⟪v, v⟫_ℝ` for v = ∂ₜ x (toRealCLE.symm r),
        then close:                                                               R16, R17 → R18
  5. Close the theorem in one `exact`: R19 applied to hg, hderiv and
     the real inequality from `ht` (R20), as in R21; `exact` sees g t.val as S.energy x t: R22
-/
-- BEGIN SPEC
theorem energy_antitone (S : DampedHarmonicOscillator) (x : Time → EuclideanSpace ℝ (Fin 1))
    (hx : ContDiff ℝ ∞ x) (h : S.EquationOfMotion x) (t₁ t₂ : Time) (ht : t₁ ≤ t₂) :
    S.energy x t₂ ≤ S.energy x t₁ :=
-- END SPEC
  sorry

end M192

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The energy's time derivative is `-γ ⟪ẋ, ẋ⟫_ℝ ≤ 0` (physlib proves the equality, R15). What is missing is
    the step "derivative ≤ 0 everywhere ⇒ antitone", which Mathlib has only for functions `ℝ → ℝ` (R19).
H2. `let g : ℝ → ℝ := S.energy x ∘ Time.toRealCLE.symm`. Prove `hg : Differentiable ℝ g` (R3, R4) and
    `∀ r, deriv g r ≤ 0` via the milestone `deriv g r = ∂ₜ (S.energy x) (Time.toRealCLE.symm r)` (chain rule;
    a linear equivalence is its own derivative and sends `1 ↦ 1`), then finish with
    `antitone_of_deriv_nonpos hg hderiv ((Time.le_def _ _).mp ht)`.
H3. Milestone: `rw [← fderiv_apply_one_eq_deriv, fderiv_comp _ (hE _) Time.toRealCLE.symm.differentiableAt,
    ContinuousLinearEquiv.fderiv, Time.deriv_eq, ContinuousLinearMap.comp_apply]`, then
    `congr 1; ext; simp [Time.toRealCLE, Time.one_val]`. Sign: `rw [e, S.energy_dissipation_rate x _ h hx]`,
    add `S.γ_nonneg` and `real_inner_self_nonneg (x := ∂ₜ x (Time.toRealCLE.symm r))`, then `nlinarith`.
-/
