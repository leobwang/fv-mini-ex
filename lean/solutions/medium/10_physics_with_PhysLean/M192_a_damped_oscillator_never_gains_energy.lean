/- M192 | A damped oscillator never gains energy | 15-20 min | DampedHarmonicOscillator, Time vs ℝ, chain rule through toRealCLE, antitone_of_deriv_nonpos, physlib
GOAL
  Along any smooth solution `x` of physlib's damped equation `m ẍ + γ ẋ + k x = 0` (with `γ ≥ 0`), the
  energy `E t = ½ m ⟪ẋ, ẋ⟫_ℝ + ½ k ⟪x, x⟫_ℝ` never increases: `t₁ ≤ t₂ → E t₂ ≤ E t₁` (`⟪u, v⟫_ℝ` = dot product).

REFERENCE
  `S.m`, `S.k`, `S.γ : ℝ`; `S.γ_nonneg : 0 ≤ S.γ`; `S.energy x : Time → ℝ` (from `HarmonicOscillator`); `x t : EuclideanSpace ℝ (Fin 1)` (a 1-D vector).
  `Time` wraps one real `t.val`; `ContDiff ℝ ∞ x` = smooth; `∂ₜ f t` is `fderiv ℝ f t 1` (`Time.deriv_eq`, also `rfl`).
  #check DampedHarmonicOscillator.energy_dissipation_rate  -- S x t h hx : ∂ₜ (S.energy x) t = -S.γ * ⟪∂ₜ x t, ∂ₜ x t⟫_ℝ
  #check HarmonicOscillator.energy_differentiable  -- S.energy_differentiable x hx : Differentiable ℝ (S.energy x)
  #check Time.le_def                 -- t₁ ≤ t₂ ↔ t₁.val ≤ t₂.val
  example : Time.toRealCLE.symm (1 : ℝ) = (1 : Time) := by ext; simp [Time.toRealCLE, Time.one_val]  -- `Time.toRealCLE : Time ≃L[ℝ] ℝ` (`t ↦ t.val`) sends direction 1 ↦ 1 (not `rfl`)
  #check antitone_of_deriv_nonpos    -- (f : ℝ → ℝ) Differentiable ℝ f → (∀ x, deriv f x ≤ 0) → Antitone f   (`Antitone f` = `a ≤ b → f b ≤ f a`)
  #check fderiv_comp                 -- x hg hf : fderiv 𝕜 (g ∘ f) x = fderiv 𝕜 g (f x) ∘L fderiv 𝕜 f x   (`∘L` = composition of continuous linear maps)
  #check ContinuousLinearEquiv.fderiv  -- fderiv 𝕜 e x = e   (also `e.differentiable`, `e.differentiableAt`)
  #check fderiv_apply_one_eq_deriv   -- fderiv 𝕜 f x 1 = deriv f x   (for `f : 𝕜 → F`)
  #check real_inner_self_nonneg      -- 0 ≤ ⟪x, x⟫_ℝ
NOTE: `antitone_of_deriv_nonpos` wants `f : ℝ → ℝ`, but `S.energy x` lives on `Time`: precompose with `Time.toRealCLE.symm`.
-/
import Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic

open ClassicalMechanics Time ContDiff InnerProductSpace

namespace M192

-- BEGIN SPEC
theorem energy_antitone (S : DampedHarmonicOscillator) (x : Time → EuclideanSpace ℝ (Fin 1))
    (hx : ContDiff ℝ ∞ x) (h : S.EquationOfMotion x) (t₁ t₂ : Time) (ht : t₁ ≤ t₂) :
    S.energy x t₂ ≤ S.energy x t₁ :=
-- END SPEC
  by
    have hE : Differentiable ℝ (S.energy x) := S.energy_differentiable x hx
    -- WHY: Mathlib's monotonicity-from-derivative lemma is stated on ℝ, not on `Time`.
    let g : ℝ → ℝ := S.energy x ∘ Time.toRealCLE.symm
    have hg : Differentiable ℝ g := hE.comp Time.toRealCLE.symm.differentiable
    have hderiv : ∀ r, deriv g r ≤ 0 := by
      intro r
      have e : deriv g r = ∂ₜ (S.energy x) (Time.toRealCLE.symm r) := by
        rw [← fderiv_apply_one_eq_deriv, fderiv_comp _ (hE _) Time.toRealCLE.symm.differentiableAt,
          ContinuousLinearEquiv.fderiv, Time.deriv_eq, ContinuousLinearMap.comp_apply]
        congr 1
        ext
        simp [Time.toRealCLE, Time.one_val]
      rw [e, S.energy_dissipation_rate x _ h hx]
      have h1 := S.γ_nonneg
      have h2 := real_inner_self_nonneg (x := ∂ₜ x (Time.toRealCLE.symm r))
      nlinarith
    exact antitone_of_deriv_nonpos hg hderiv ((Time.le_def _ _).mp ht)

end M192

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The energy's time derivative is `-γ ⟪ẋ, ẋ⟫_ℝ ≤ 0` (physlib proves the equality). What is missing is the step
    "derivative ≤ 0 everywhere ⇒ antitone", which Mathlib has only for functions `ℝ → ℝ`.
H2. Set `g : ℝ → ℝ := S.energy x ∘ Time.toRealCLE.symm`. Show `g` is differentiable, that
    `deriv g r = ∂ₜ (S.energy x) (Time.toRealCLE.symm r)` (chain rule; the derivative of the linear equivalence is
    itself, and it sends `1 ↦ 1`), then apply `antitone_of_deriv_nonpos` and evaluate at `t₁.val ≤ t₂.val`.
H3. `rw [← fderiv_apply_one_eq_deriv, fderiv_comp _ (hE _) Time.toRealCLE.symm.differentiableAt,
    ContinuousLinearEquiv.fderiv, Time.deriv_eq, ContinuousLinearMap.comp_apply]` leaves the two arguments
    `Time.toRealCLE.symm 1` vs `1` to match (`congr 1; ext; simp [Time.toRealCLE, Time.one_val]`); the sign
    then follows from `energy_dissipation_rate`, `S.γ_nonneg`, `real_inner_self_nonneg` and `nlinarith`.
-/
