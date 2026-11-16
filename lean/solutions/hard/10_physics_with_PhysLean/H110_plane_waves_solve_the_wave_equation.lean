/- H110 | Plane waves solve the wave equation | 1.5-2 h | Δᵥ, ∂ₜ, chain rule, fderiv_comp, inner product with a unit vector, physlib
GOAL
  For a C² profile `f₀ : ℝ → ℝ^d`, speed `c` and unit vector `s`, the plane wave `f(t, x) = f₀(⟪x, s⟫ - c t)`
  satisfies physlib's `WaveEquation`: `c² Δf - ∂²f/∂t² = 0`. Do both chain rules yourself.

REFERENCE
  `Time` wraps ℝ (`t.val`); `∂ₜ f t = fderiv ℝ f t 1`; `∂[i] f x = fderiv ℝ f x (basis i)`; `s.unit : Space d`, `s.norm : ‖s.unit‖ = 1`.
  `⟪a, b⟫_ℝ` = real inner product (dot product) of `a b : Space d`.
  example {d} (f₀ : ℝ → EuclideanSpace ℝ (Fin d)) c (s : Direction d) t x : planeWave f₀ c s t x = f₀ (⟪x, s.unit⟫_ℝ - c * t.val) := rfl
  example {d} (f : Time → Space d → EuclideanSpace ℝ (Fin d)) t x c :
    WaveEquation f t x c ↔ c ^ 2 • Δᵥ (f t) x - ∂ₜ (fun τ => ∂ₜ (fun τ => f τ x) τ) t = 0 := Iff.rfl
  example {d} (F : Space d → EuclideanSpace ℝ (Fin d)) x j : Δᵥ F x j = Δ (fun y => F y j) x := rfl  -- componentwise
  #check Space.laplacian_eq_sum_snd_deriv  -- Δ f = fun x => ∑ i, ∂[i] (∂[i] f) x
  #check Space.deriv_euclid      -- Differentiable f → ∂[ν] (fun x => f x μ) x = ∂[ν] f x μ
  #check fderiv_comp             -- g, f DifferentiableAt → fderiv (g ∘ f) x = fderiv g (f x) ∘L fderiv f x
  #check fderiv_eq_smul_deriv    -- for f : ℝ → F, fderiv ℝ f x y = y • deriv f x
  #check fderiv_inner_apply      -- (explicit ℝ) fderiv of fun t => ⟪f t, g t⟫ applied to y: product rule
  example (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by rw [iteratedDeriv_succ, iteratedDeriv_one]
BANNED: planeWave_waveEquation, planeWave_laplacian, planeWave_time_deriv_time_deriv, planeWave_space_deriv_space_deriv, planeWave_apply_space_deriv_space_deriv, planeWave_time_deriv, planeWave_space_deriv, planeWave_apply_space_deriv, wave_dx2, space_fderiv_of_inner_product_wave_eq_space_fderiv, wave_fderiv_inner_eq_inner_fderiv_proj, exact?, apply?, rw?, try?, hint, observe
-/
import Physlib.ClassicalMechanics.WaveEquation.Basic

open Space Time ClassicalMechanics InnerProductSpace

namespace H110

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

-- BEGIN SPEC
theorem planeWave_solves {d : ℕ} (c : ℝ) (s : Direction d) (f₀ : ℝ → EuclideanSpace ℝ (Fin d))
    (hf₀ : ContDiff ℝ 2 f₀) (t : Time) (x : Space d) :
    WaveEquation (planeWave f₀ c s) t x c :=
-- END SPEC
  by
    rw [WaveEquation, laplacianVec_planeWave c s f₀ hf₀, time_deriv_time_deriv c s f₀ hf₀, sub_self]

end H110

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both sides equal `c² f₀''(⟪x, s⟫ - c t)`: two time derivatives each pull out `-c`; each `∂ᵢ∂ᵢ` pulls out `sᵢ²`,
    and `∑ sᵢ² = ‖s‖² = 1` (`Space.norm_sq_eq` and `s.norm`). Prove the two chain rules once for a general
    `g` and use them with `g = f₀` and then `g = deriv f₀`.
H2. Chain rules: `rw [Time.deriv_eq]` (or `Space.deriv_eq`), then `change fderiv ℝ (g ∘ fun τ : Time => a - c * τ.val) t 1 = _`
    so that `fderiv_comp` applies; then `fderiv_eq_smul_deriv`, `fderiv_const_sub`, `fderiv_const_mul` (time) or
    `fderiv_sub_const`, `fderiv_inner_apply ℝ` (space), and `simp`. `deriv f₀` is differentiable by
    `hf₀.differentiable_iteratedDeriv 1 (by norm_num)` plus `iteratedDeriv_one`. For the Laplacian, first show
    `∂[i] (planeWave f₀ c s t) = fun y => s.unit i • deriv f₀ (…)`, then go to components with `Space.deriv_euclid`.
H3. Time: `simp only [planeWave_eq, time_deriv_comp f₀ h1]; rw [Time.deriv_smul _ _ (by fun_prop), time_deriv_comp _ h2]`.
    Second space derivative: `rw [hd, Space.deriv_eq, fderiv_fun_const_smul (by fun_prop), _root_.smul_apply,
    ← Space.deriv_eq, space_deriv_comp _ h2, smul_smul]`. Sum with `← Finset.sum_mul`. Main:
    `rw [WaveEquation, laplacianVec_planeWave c s f₀ hf₀, time_deriv_time_deriv c s f₀ hf₀, sub_self]`.
-/
