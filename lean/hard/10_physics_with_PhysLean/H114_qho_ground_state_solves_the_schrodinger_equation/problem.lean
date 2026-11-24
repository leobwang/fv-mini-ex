/- H114 | The QHO ground state solves the Schrödinger equation | 1-1.5 h | deriv of ℝ → ℂ, chain rule, Complex.exp, casts, field_simp, physlib
GOAL
  The 1D quantum harmonic oscillator's ground state `ψ₀(x) = (√π ξ)^(-1/2) · exp(−x²/(2ξ²))` satisfies the
  time-independent Schrödinger equation `H ψ₀ = ½ ℏ ω ψ₀`. Compute `ψ₀'` and `ψ₀''` yourself (chain and product rule).

REFERENCE
  `Q : HarmonicOscillator` has mass `Q.m > 0`, frequency `Q.ω > 0`, length `Q.ξ = √(ℏ / (m ω))`.
  `ℏ : {x : ℝ // 0 < x}` (`Constants.ℏ`, a subtype); it shows as `↑ℏ` in ℝ and `↑↑ℏ` in ℂ; `ℏ_ne_zero : (↑ℏ : ℝ) ≠ 0`.
  `Q.schrodingerOperator ψ x = -ℏ^2/(2m) * deriv (deriv ψ) x + 1/2 * m * ω^2 * x^2 * ψ x` for `ψ : ℝ → ℂ`; `Q.eigenValue n = (n + 1/2) * ℏ * ω`.
  #check HarmonicOscillator.schrodingerOperator_eq_ξ  -- = fun x => ↑↑ℏ^2/(2m) * (-deriv (deriv ψ) x + (1/ξ^2)^2 * x^2 * ψ x)
  #check HarmonicOscillator.eigenfunction_zero  -- Q.eigenfunction 0 = fun x => 1/√(√π * ξ) * Complex.exp (-x^2/(2 * ξ^2))
  #check HarmonicOscillator.ξ_sq       -- Q.ξ ^ 2 = ℏ / (Q.m * Q.ω)   (also `ξ_ne_zero`, `m_ne_zero`, `ω_ne_zero`)
  #check deriv_comp                    -- deriv (h₂ ∘ h) x = deriv h₂ (h x) * deriv h x   (needs both differentiable: `by fun_prop`)
  #check Complex.deriv_exp             -- deriv Complex.exp = Complex.exp   (also `Complex.deriv_ofReal : deriv (↑) x = 1`)
  #check deriv_const_mul_field'        -- (deriv fun x => u * v x) = fun x => u * deriv v x
  #check deriv_fun_mul                 -- deriv (fun y => c y * d y) x = deriv c x * d x + c x * deriv d x
  #check Complex.ofReal_ne_zero        -- (↑r : ℂ) ≠ 0 ↔ r ≠ 0   e.g. `.mpr Q.ξ_ne_zero` (for `field_simp`); `push_cast` moves casts
  `simp only [deriv_div_const, deriv.fun_neg']` peels `/ c` and `-` off a `deriv`; `dsimp only` beta-reduces `(fun x => …) x`.
BANNED: schrodingerOperator_eigenfunction, deriv_eigenfunction_zero, deriv_eigenfunction_zero', deriv_deriv_eigenfunction_zero, deriv_deriv_eigenfunction_succ, deriv_deriv_eigenfunction, deriv_eigenfunction_succ, exact?, apply?, try?, hint
-/
import Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.TISE

open QuantumMechanics OneDimension HarmonicOscillator Constants

namespace H114

-- MILESTONE (optional: change or delete)
/-- Chain rule for the Gaussian factor. -/
theorem deriv_gauss (Q : HarmonicOscillator) (x : ℝ) :
    deriv (fun x : ℝ => Complex.exp (-x ^ 2 / (2 * Q.ξ ^ 2))) x =
      -x / Q.ξ ^ 2 * Complex.exp (-x ^ 2 / (2 * Q.ξ ^ 2)) := by
  sorry

-- MILESTONE (optional: change or delete)
/-- `ψ₀' = (-x / ξ²) ψ₀`. -/
theorem deriv_ground (Q : HarmonicOscillator) :
    deriv (Q.eigenfunction 0) = fun x : ℝ => (-(x : ℂ) / (Q.ξ : ℂ) ^ 2) * Q.eigenfunction 0 x := by
  sorry

-- MILESTONE (optional: change or delete)
/-- `ψ₀'' = (-1/ξ²)(1 - x²/ξ²) ψ₀`. -/
theorem deriv_deriv_ground (Q : HarmonicOscillator) (x : ℝ) :
    deriv (deriv (Q.eigenfunction 0)) x =
      (-1 / Q.ξ ^ 2) * (1 - x ^ 2 / Q.ξ ^ 2) * Q.eigenfunction 0 x := by
  sorry

-- BEGIN SPEC
theorem ground_state_tise (Q : HarmonicOscillator) (x : ℝ) :
    Q.schrodingerOperator (Q.eigenfunction 0) x = Q.eigenValue 0 * Q.eigenfunction 0 x :=
-- END SPEC
  sorry

end H114

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Three derivative computations, then algebra. `ψ₀` is a constant times `exp ∘ g` with `g x = -x²/(2ξ²)`, so
    `ψ₀' = g' ψ₀ = (-x/ξ²) ψ₀`, and by the product rule `ψ₀'' = (-1/ξ²) ψ₀ + (-x/ξ²)(-x/ξ²) ψ₀`.
H2. `deriv_gauss`: get `deriv (fun x : ℝ => (x : ℂ) ^ 2) x = 2 * x` first (`pow_two`, `deriv_fun_mul`,
    `Complex.deriv_ofReal`), view the function as `Complex.exp ∘ g`, and use `deriv_comp` and `Complex.deriv_exp`.
    `deriv_ground`: unfold `eigenfunction_zero`, pull the constant out with `deriv_const_mul_field'`, use `deriv_gauss`.
    `deriv_deriv_ground`: product rule `deriv_fun_mul` on `(-x/ξ²) · ψ₀`, with `deriv_ground` for the `ψ₀'` factor.
    Main: expand with `schrodingerOperator_eq_ξ` and `eigenValue`, insert `ψ₀''`; the algebra only closes once `ξ²`
    is replaced by `ℏ/(m ω)` inside ℂ, so prove that equation with the casts on the ℂ side (`hsq` below).
H3. Chain-rule step: `rw [show (fun x : ℝ => Complex.exp (-x ^ 2 / (2 * Q.ξ ^ 2))) =
    Complex.exp ∘ (fun x : ℝ => -x ^ 2 / (2 * Q.ξ ^ 2)) from rfl, deriv_comp _ (by fun_prop) (by fun_prop)]`.
    Cast trick: `have hsq : (Q.ξ : ℂ) ^ 2 = ℏ / (Q.m * Q.ω) := by rw [← Complex.ofReal_pow, ξ_sq]; push_cast; rfl`;
    rewrite with `hsq` before `field_simp` (afterwards the goal holds `ξ ^ 4`, which `hsq` no longer matches).
-/
