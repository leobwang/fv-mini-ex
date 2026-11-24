/- H114 | The QHO ground state solves the Schrödinger equation | 1-1.5 h | deriv of ℝ → ℂ, chain rule, Complex.exp, casts, field_simp, physlib
GOAL
  The 1D quantum harmonic oscillator's ground state `ψ₀(x) = (√π ξ)^(-1/2) · exp(−x²/(2ξ²))` satisfies the
  time-independent Schrödinger equation `H ψ₀ = ½ ℏ ω ψ₀`. Compute `ψ₀'` and `ψ₀''` yourself (chain and product rule).
BANNED: schrodingerOperator_eigenfunction, deriv_eigenfunction_zero, deriv_eigenfunction_zero', deriv_deriv_eigenfunction_zero, deriv_deriv_eigenfunction_succ, deriv_deriv_eigenfunction, deriv_eigenfunction_succ, exact?, apply?, try?, hint

GUIDE
  Entries R1–R22: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.TISE

open QuantumMechanics OneDimension HarmonicOscillator Constants

namespace H114

/- SKELETON · deriv_gauss   (milestone 1; used in `deriv_ground`, step 4)
  1. Two facts first:
       hsq : deriv (fun x : ℝ => (x : ℂ) ^ 2) x = 2 * x
         proof: R1, then R2 with both arguments R3, then R4, then `ring`
       hξ : (Q.ξ : ℂ) ≠ 0                                                 R5 with R6
  2. Rewrite the function as `Complex.exp ∘ (fun x : ℝ => -x ^ 2 / (2 * Q.ξ ^ 2))`:   R7
  3. Chain rule; both side goals by `fun_prop`:                           R8, R9
  4. Evaluate the derivatives in one `simp only [...]` with R10, R11, R12 and `hsq`
  5. Clear the denominator `2 * ξ²` (needs `hξ`); this closes the goal:   R13
-/
-- MILESTONE (optional: change or delete)
/-- Chain rule for the Gaussian factor. -/
theorem deriv_gauss (Q : HarmonicOscillator) (x : ℝ) :
    deriv (fun x : ℝ => Complex.exp (-x ^ 2 / (2 * Q.ξ ^ 2))) x =
      -x / Q.ξ ^ 2 * Complex.exp (-x ^ 2 / (2 * Q.ξ ^ 2)) := by
  sorry

/- SKELETON · deriv_ground   (milestone 2; uses milestone 1; used twice in `deriv_deriv_ground`, step 2)
  1. Unfold `ψ₀` everywhere (both sides of the goal):                      R14
  2. Equation of functions → equation at a point `x`:                     R15
  3. Pull the constant `1 / ↑√(√π ξ)` out of the derivative:             R16
  4. β-reduce the `(fun x => …) x` left by steps 1 and 3:                 R17
  5. Milestone 1: `rw [deriv_gauss]`, then `ring`
-/
-- MILESTONE (optional: change or delete)
/-- `ψ₀' = (-x / ξ²) ψ₀`. -/
theorem deriv_ground (Q : HarmonicOscillator) :
    deriv (Q.eigenfunction 0) = fun x : ℝ => (-(x : ℂ) / (Q.ξ : ℂ) ^ 2) * Q.eigenfunction 0 x := by
  sorry

/- SKELETON · deriv_deriv_ground   (milestone 3; uses milestone 2; used in `ground_state_tise`, step 2)
  1. hξ : (Q.ξ : ℂ) ≠ 0                                                   R5 with R6
  2. One `rw [...]` with three steps:
       milestone 2 turns `deriv (deriv ψ₀)` into `deriv (fun x => -↑x / ↑Q.ξ ^ 2 * ψ₀ x)`
       product rule, both side goals by `fun_prop`                        R2, R9
       milestone 2 again, for the factor `deriv ψ₀ x` the product rule made
  3. Evaluate `deriv (fun x => -↑x / ↑Q.ξ ^ 2) x` in one `simp only [...]`
     (it also β-reduces):                                                 R11, R12, R4
  4. Clear denominators, then `ring`:                                     R13
-/
-- MILESTONE (optional: change or delete)
/-- `ψ₀'' = (-1/ξ²)(1 - x²/ξ²) ψ₀`. -/
theorem deriv_deriv_ground (Q : HarmonicOscillator) (x : ℝ) :
    deriv (deriv (Q.eigenfunction 0)) x =
      (-1 / Q.ξ ^ 2) * (1 - x ^ 2 / Q.ξ ^ 2) * Q.eigenfunction 0 x := by
  sorry

/- SKELETON · ground_state_tise   (prove milestones 1, 2, 3 first; this proof uses milestone 3)
  1. Expand the operator, then β-reduce with `simp only`:                 R18, R17
  2. Insert `ψ₀''` (milestone 3: `rw [deriv_deriv_ground]`), unfold the eigenvalue:   R19
  3. The nonzero facts in ℂ: hm, hω, hℏ                                   R5 with R6
  4. hsq : (Q.ξ : ℂ) ^ 2 = ℏ / (Q.m * Q.ω)
       proof: R20 → R21 → R22, then `rfl` (both sides print the same; cheatsheet: Traps)
  5. Push the cast of the real eigenvalue into ℂ:                        R22
  6. `rw [hsq]` BEFORE clearing denominators, then R13, then `ring`
-/
-- BEGIN SPEC
theorem ground_state_tise (Q : HarmonicOscillator) (x : ℝ) :
    Q.schrodingerOperator (Q.eigenfunction 0) x = Q.eigenValue 0 * Q.eigenfunction 0 x :=
-- END SPEC
  sorry

end H114

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Three derivative computations, then algebra. `ψ₀` is a constant times `exp ∘ g` with `g x = -x²/(2ξ²)`, so
    `ψ₀' = g' ψ₀ = (-x/ξ²) ψ₀`, and by the product rule `ψ₀'' = (-1/ξ²) ψ₀ + (-x/ξ²)(-x/ξ²) ψ₀`. Prove the three
    milestones in order; each one is used by the next, and the main theorem is algebra once `ψ₀''` is known.
H2. `deriv_gauss`: get `deriv (fun x : ℝ => (x : ℂ) ^ 2) x = 2 * x` first (R1 `pow_two`, R2 `deriv_fun_mul`,
    R4 `Complex.deriv_ofReal`), view the function as `Complex.exp ∘ g` (R7), and use R8 `deriv_comp` and R10.
    `deriv_ground`: unfold with R14 `eigenfunction_zero`, pull the constant out with R16, use `deriv_gauss`.
    `deriv_deriv_ground`: rewrite with `deriv_ground`, product rule R2 on `(-x/ξ²) · ψ₀`, `deriv_ground` again.
    Main: expand with R18 `schrodingerOperator_eq_ξ` and R19 `eigenValue`, insert `ψ₀''`; the algebra only closes
    once `ξ²` is replaced by `ℏ/(m ω)` inside ℂ, so prove that equation with the casts on the ℂ side (`hsq` below).
H3. Chain-rule step: `rw [show (fun x : ℝ => Complex.exp (-x ^ 2 / (2 * Q.ξ ^ 2))) =
    Complex.exp ∘ (fun x : ℝ => -x ^ 2 / (2 * Q.ξ ^ 2)) from rfl, deriv_comp _ (by fun_prop) (by fun_prop)]`.
    Cast trick: `have hsq : (Q.ξ : ℂ) ^ 2 = ℏ / (Q.m * Q.ω) := by rw [← Complex.ofReal_pow, ξ_sq]; push_cast; rfl`;
    after `push_cast` on the goal, rewrite with `hsq` before `field_simp` (afterwards the goal holds `ξ ^ 4`,
    which `hsq` no longer matches).
-/
