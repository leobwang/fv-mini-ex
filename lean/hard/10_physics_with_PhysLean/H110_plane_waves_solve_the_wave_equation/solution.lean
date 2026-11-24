/- H110 | Plane waves solve the wave equation | 1.5-2 h | Δᵥ, ∂ₜ, chain rule, fderiv_comp, inner product with a unit vector, physlib
GOAL
  For a C² profile `f₀ : ℝ → ℝ^d`, speed `c` and unit vector `s`, the plane wave `f(t, x) = f₀(⟪x, s⟫ - c t)`
  satisfies physlib's `WaveEquation`: `c² Δf - ∂²f/∂t² = 0`. Do both chain rules yourself.
BANNED: planeWave_waveEquation, planeWave_laplacian, planeWave_time_deriv_time_deriv, planeWave_space_deriv_space_deriv, planeWave_apply_space_deriv_space_deriv, planeWave_time_deriv, planeWave_space_deriv, planeWave_apply_space_deriv, wave_dx2, space_fderiv_of_inner_product_wave_eq_space_fderiv, wave_fderiv_inner_eq_inner_fderiv_proj, exact?, apply?, rw?, try?, hint, observe

GUIDE
  Entries R1–R44: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.ClassicalMechanics.WaveEquation.Basic

open Space Time ClassicalMechanics InnerProductSpace

namespace H110

/- SKELETON · time_deriv_comp   (milestone 1: d/dt g(a - c t) = -c g'(a - c t); used twice in milestone 3)
  1. `∂ₜ` → the derivative map applied to `1`:                               R1
  2. Write the function as `g ∘ fun τ : Time => a - c * τ.val`:              R2
  3. Chain rule; its two arguments are `hg _` and `by fun_prop`:             R5 (R3, R4)
  4. Evaluate the composed map; outer derivative → `deriv g`:               R6, R7
  5. Inner derivative `τ ↦ a - c * τ.val` (side argument `by fun_prop`):     R8, R9
  6. `simp` closes `(-(c • fderiv ℝ Time.val t)) 1 • v = -c • v`:           simp (uses R11, R10)
-/
-- MILESTONE (optional: change or delete)
/-- Chain rule in time: `d/dt g(a - c t) = -c g'(a - c t)`. -/
theorem time_deriv_comp {d : ℕ} (g : ℝ → EuclideanSpace ℝ (Fin d)) (hg : Differentiable ℝ g)
    (a c : ℝ) (t : Time) :
    ∂ₜ (fun τ : Time => g (a - c * τ.val)) t = -c • deriv g (a - c * t.val) := by
  rw [Time.deriv_eq]
  -- WHY: `fderiv_comp` needs the function literally in the form `g ∘ inner`.
  change fderiv ℝ (g ∘ fun τ : Time => a - c * τ.val) t 1 = _
  rw [fderiv_comp _ (hg _) (by fun_prop), ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv,
    fderiv_const_sub, fderiv_const_mul (by fun_prop)]
  simp

/- SKELETON · space_deriv_comp   (milestone 2: ∂ᵢ g(⟪y, u⟫ - b) = uᵢ g'(⟪x, u⟫ - b); used twice in milestone 4)
  Same shape as milestone 1, with the partial derivative in place of `∂ₜ`.
  1. `∂[i]` → the derivative map applied to `Space.basis i`:                 R12
  2. Write the function as `g ∘ fun y : Space d => ⟪y, u⟫_ℝ - b`:            R2
  3. Chain rule, evaluate, outer derivative → `deriv g`:                     R5 (R3, R4), R6, R7
  4. Inner derivative: drop `- b`, then the product rule for `⟪y, u⟫_ℝ`
     (both arguments `by fun_prop`):                                        R13, R14
  5. `simp` closes it:                                                       simp (uses R15, R16, R17)
-/
-- MILESTONE (optional: change or delete)
/-- Chain rule in space: `∂ᵢ g(⟪y, u⟫ - b) = uᵢ g'(⟪x, u⟫ - b)`. -/
theorem space_deriv_comp {d : ℕ} (g : ℝ → EuclideanSpace ℝ (Fin d)) (hg : Differentiable ℝ g)
    (u : Space d) (b : ℝ) (i : Fin d) (x : Space d) :
    ∂[i] (fun y : Space d => g (⟪y, u⟫_ℝ - b)) x = u i • deriv g (⟪x, u⟫_ℝ - b) := by
  rw [Space.deriv_eq]
  change fderiv ℝ (g ∘ fun y : Space d => ⟪y, u⟫_ℝ - b) x (basis i) = _
  rw [fderiv_comp _ (hg _) (by fun_prop), ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv,
    fderiv_sub_const, fderiv_inner_apply ℝ (by fun_prop) (by fun_prop)]
  simp

/- SKELETON · time_deriv_time_deriv   (milestone 3: ∂ₜ²f = c² f₀''; used in planeWave_solves)
  Uses milestone 1 twice: with `g = f₀`, then with `g = deriv f₀`.
  1. h1 : Differentiable ℝ f₀:                                              R18
  2. h2 : Differentiable ℝ (deriv f₀): from R19, simplified by R20:          R19, R22 (R20)
  3. Unfold the plane wave and apply milestone 1 (`g = f₀`, `h1`) inside the
     outer `fun τ => …`, in one `simp only`:                                 R23, R24
  4. Pull `-c` out of the outer `∂ₜ` (side argument `by fun_prop`), then
     milestone 1 again (`g = deriv f₀`, `h2`):                               R25, rw [milestone 1]
  5. Right side `iteratedDeriv 2 f₀` → `deriv (deriv f₀)`:                   R21, R20
  6. Merge the scalars, then close `(-c * -c) • v = c ^ 2 • v`:              R26, R27
-/
-- MILESTONE (optional: change or delete)
theorem time_deriv_time_deriv {d : ℕ} (c : ℝ) (s : Direction d) (f₀ : ℝ → EuclideanSpace ℝ (Fin d))
    (hf₀ : ContDiff ℝ 2 f₀) (t : Time) (x : Space d) :
    ∂ₜ (fun τ => ∂ₜ (fun τ => planeWave f₀ c s τ x) τ) t
      = c ^ 2 • iteratedDeriv 2 f₀ (⟪x, s.unit⟫_ℝ - c * t.val) := by
  have h1 : Differentiable ℝ f₀ := hf₀.differentiable (by simp)
  have h2 : Differentiable ℝ (deriv f₀) := by
    simpa [iteratedDeriv_one] using hf₀.differentiable_iteratedDeriv 1 (by norm_num)
  simp only [planeWave_eq, time_deriv_comp f₀ h1]
  rw [Time.deriv_smul _ _ (by fun_prop), time_deriv_comp _ h2, iteratedDeriv_succ, iteratedDeriv_one,
    smul_smul]
  ring_nf

/- SKELETON · laplacianVec_planeWave   (milestone 4: Δf = f₀''; used in planeWave_solves)
  Uses milestone 2 twice: with `g = f₀` (step 2), then with `g = deriv f₀` (step 3).
  1. h1, h2 as in milestone 3:                                               R18; R19, R22 (R20)
  2. hd : ∀ i, ∂[i] (planeWave f₀ c s t) = fun y => s.unit i • deriv f₀ (⟪y, s.unit⟫_ℝ - c * t.val)
     `intro i`, `funext y`, then `exact` milestone 2 with `h1` (`planeWave` unfolds by itself).
  3. hdd : ∀ i, ∂[i] (∂[i] (planeWave f₀ c s t)) x = s.unit i ^ 2 • iteratedDeriv 2 f₀ (⟪x, s.unit⟫_ℝ - c * t.val)
     `intro i`, then one `rw` chain: `hd`, R12, R28, R11 (`_root_.smul_apply`), R12 backwards,
     milestone 2 with `h2`, R26, R21, R20, R29.
  4. hF : Differentiable ℝ (planeWave f₀ c s t):                             R30, R4
     hF' : ∀ i, Differentiable ℝ (∂[i] (planeWave f₀ c s t)):                rw [hd], R4
  5. hsum : ∑ i, s.unit i ^ 2 = 1:                                           R31 backwards, R32, R33
  6. Componentwise: `ext j`, then one `simp only`:                            R34; R35, R37, R36
  7. hc : ∀ i, ∂[i] (fun y => (planeWave f₀ c s t y).ofLp j) = fun y => (∂[i] (planeWave f₀ c s t) y).ofLp j
     `intro i`, `funext y`, then `exact` R38 with `hF`.
  8. One `simp only` closes it: `hc`, R38 with `hF' _`, `hdd`, then collect:  R39, R40, R41 backwards, hsum, R42
-/
-- MILESTONE (optional: change or delete)
theorem laplacianVec_planeWave {d : ℕ} (c : ℝ) (s : Direction d) (f₀ : ℝ → EuclideanSpace ℝ (Fin d))
    (hf₀ : ContDiff ℝ 2 f₀) (t : Time) (x : Space d) :
    Δᵥ (planeWave f₀ c s t) x = iteratedDeriv 2 f₀ (⟪x, s.unit⟫_ℝ - c * t.val) := by
  have h1 : Differentiable ℝ f₀ := hf₀.differentiable (by simp)
  have h2 : Differentiable ℝ (deriv f₀) := by
    simpa [iteratedDeriv_one] using hf₀.differentiable_iteratedDeriv 1 (by norm_num)
  have hd : ∀ i, ∂[i] (planeWave f₀ c s t) =
      fun y => s.unit i • deriv f₀ (⟪y, s.unit⟫_ℝ - c * t.val) := by
    intro i
    funext y
    exact space_deriv_comp f₀ h1 _ _ i y
  have hdd : ∀ i, ∂[i] (∂[i] (planeWave f₀ c s t)) x =
      s.unit i ^ 2 • iteratedDeriv 2 f₀ (⟪x, s.unit⟫_ℝ - c * t.val) := by
    intro i
    rw [hd, Space.deriv_eq, fderiv_fun_const_smul (by fun_prop), _root_.smul_apply, ← Space.deriv_eq,
      space_deriv_comp _ h2, smul_smul, iteratedDeriv_succ, iteratedDeriv_one, pow_two]
  have hF : Differentiable ℝ (planeWave f₀ c s t) := by
    unfold planeWave
    fun_prop
  have hF' : ∀ i, Differentiable ℝ (∂[i] (planeWave f₀ c s t)) := by
    intro i
    rw [hd]
    fun_prop
  have hsum : ∑ i, s.unit i ^ 2 = 1 := by
    rw [← Space.norm_sq_eq, s.norm, one_pow]
  ext j
  simp only [laplacianVec, laplacian_eq_sum_snd_deriv, PiLp.toLp_apply]
  -- WHY: `Δᵥ` works on components; move `j` out through both derivatives with `deriv_euclid`.
  have hc : ∀ i, ∂[i] (fun y => planeWave f₀ c s t y j) = fun y => ∂[i] (planeWave f₀ c s t) y j := by
    intro i
    funext y
    exact Space.deriv_euclid hF y
  simp only [hc, Space.deriv_euclid (hF' _), hdd, PiLp.smul_apply, smul_eq_mul, ← Finset.sum_mul,
    hsum, one_mul]

/- SKELETON · planeWave_solves
  Prove the milestones first: milestones 1, 2 feed 3, 4, and 3, 4 are used here.
  1. Unfold the wave equation:                                               R43
  2. Substitute milestone 4 (`Δᵥ`) and milestone 3 (`∂ₜ²`), both with `c s f₀ hf₀`:
                                                                             rw [milestone 4, milestone 3]
  3. The goal is now `v - v = 0`:                                            R44
-/
-- BEGIN SPEC
theorem planeWave_solves {d : ℕ} (c : ℝ) (s : Direction d) (f₀ : ℝ → EuclideanSpace ℝ (Fin d))
    (hf₀ : ContDiff ℝ 2 f₀) (t : Time) (x : Space d) :
    WaveEquation (planeWave f₀ c s) t x c :=
-- END SPEC
  by
    rw [WaveEquation, laplacianVec_planeWave c s f₀ hf₀, time_deriv_time_deriv c s f₀ hf₀, sub_self]

end H110

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both terms of the wave equation equal `c² f₀''(⟪x, s⟫ - c t)`: each time derivative pulls out `-c`, each
    `∂ᵢ∂ᵢ` pulls out `sᵢ²`, and `∑ sᵢ² = ‖s‖² = 1`. Prove the two chain rules once for a general `g`
    (milestones 1, 2) and use them with `g = f₀` and then `g = deriv f₀` (milestones 3, 4).
H2. Chain rules: `rw [Time.deriv_eq]` (or `Space.deriv_eq`), then `change fderiv ℝ (g ∘ fun τ : Time => a - c * τ.val) t 1 = _`
    so that `fderiv_comp` applies; then `ContinuousLinearMap.comp_apply`, `fderiv_eq_smul_deriv`, the inner
    derivative (`fderiv_const_sub`, `fderiv_const_mul`, or `fderiv_sub_const`, `fderiv_inner_apply ℝ`), and `simp`.
    `deriv f₀` is differentiable by `simpa [iteratedDeriv_one] using hf₀.differentiable_iteratedDeriv 1 (by norm_num)`.
    For the Laplacian, first show `hd : ∀ i, ∂[i] (planeWave f₀ c s t) = fun y => s.unit i • deriv f₀ (…)`, then go to
    components with `ext j` and `Space.deriv_euclid`.
H3. Time: `simp only [planeWave_eq, time_deriv_comp f₀ h1]; rw [Time.deriv_smul _ _ (by fun_prop), time_deriv_comp _ h2]`.
    Second space derivative: `rw [hd, Space.deriv_eq, fderiv_fun_const_smul (by fun_prop), _root_.smul_apply,
    ← Space.deriv_eq, space_deriv_comp _ h2, smul_smul]`. Sum with `← Finset.sum_mul` and `hsum`. Main:
    `rw [WaveEquation, laplacianVec_planeWave c s f₀ hf₀, time_deriv_time_deriv c s f₀ hf₀, sub_self]`.
-/
