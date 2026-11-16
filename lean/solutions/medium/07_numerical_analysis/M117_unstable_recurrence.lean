/- M117 | An unstable recurrence | 15-20 min | integration by parts, HasDerivAt, factorial, linear_combination, stability, mathlib
GOAL
  `Iₙ = ∫₀¹ xⁿ e^(x-1) dx` satisfies `Iₙ₊₁ = 1 - (n+1) Iₙ` (integrate by parts). Then any sequence `J` obeying
  the same recurrence has `Jₙ - Iₙ = (-1)ⁿ n! (J₀ - I₀)`: an error in the start value is multiplied by n!, so
  running the recurrence forward in floating point is hopeless (a classic forward-unstable recurrence).

REFERENCE
  #check intervalIntegral.integral_mul_deriv_eq_deriv_mul  -- integration by parts:
    -- (∀ x ∈ uIcc a b, HasDerivAt u (u' x) x) → (same for v, v') → IntervalIntegrable u' volume a b → (same for v') →
    --   ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x        (uIcc a b = [min a b, max a b])
  example (n : ℕ) (x : ℝ) : HasDerivAt (fun x => x ^ n) (↑n * x ^ (n - 1)) x := hasDerivAt_pow n x
  example (x : ℝ) : HasDerivAt (fun x => Real.exp (x - 1)) (Real.exp (x - 1)) x :=
    ((hasDerivAt_id' x).sub_const 1).exp.congr_deriv (by ring)   -- `congr_deriv` fixes up the derivative's form
  example (n : ℕ) (a b : ℝ) : IntervalIntegrable (fun x : ℝ => (n : ℝ) * x ^ n) MeasureTheory.volume a b := by
    apply Continuous.intervalIntegrable; fun_prop
  #check intervalIntegral.integral_const_mul  -- ∫ x in a..b, c * f x = c * ∫ x in a..b, f x
  #check Nat.factorial_succ                   -- (n + 1)! = (n + 1) * n !
  `linear_combination e * ih` proves an equation that is `e` times the equation `ih`, up to ring algebra.
-/
import Mathlib

namespace M117

-- BEGIN SPEC
noncomputable def I (n : ℕ) : ℝ := ∫ x in (0:ℝ)..1, x ^ n * Real.exp (x - 1)
-- END SPEC

-- BEGIN SPEC
theorem I_succ (n : ℕ) : I (n + 1) = 1 - (n + 1) * I n :=
-- END SPEC
  by
    have hu : ∀ x ∈ Set.uIcc (0:ℝ) 1,
        HasDerivAt (fun x : ℝ => x ^ (n + 1)) ((n + 1 : ℕ) * x ^ n) x :=
      fun x _ => by simpa using hasDerivAt_pow (n + 1) x
    have hv : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x => Real.exp (x - 1)) (Real.exp (x - 1)) x :=
      fun x _ => ((hasDerivAt_id' x).sub_const 1).exp.congr_deriv (by ring)
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
      ((by fun_prop : Continuous fun x : ℝ => ((n + 1 : ℕ) : ℝ) * x ^ n).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun x : ℝ => Real.exp (x - 1)).intervalIntegrable _ _)
    unfold I
    rw [hibp]
    simp only [one_pow, sub_self, Real.exp_zero, mul_one, ne_eq, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, not_false_eq_true, zero_pow, zero_mul, sub_zero]
    rw [show (fun x : ℝ => ((n + 1 : ℕ) : ℝ) * x ^ n * Real.exp (x - 1))
        = fun x => ((n + 1 : ℕ) : ℝ) * (x ^ n * Real.exp (x - 1)) by funext x; ring,
      intervalIntegral.integral_const_mul]
    push_cast
    ring

-- BEGIN SPEC
theorem error_amplification (J : ℕ → ℝ) (hJ : ∀ n, J (n + 1) = 1 - (n + 1) * J n) (n : ℕ) :
    J n - I n = (-1) ^ n * n.factorial * (J 0 - I 0) :=
-- END SPEC
  by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hJ, I_succ, Nat.factorial_succ]
      push_cast
      linear_combination (-(n + 1 : ℝ)) * ih

end M117

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `I_succ`: integrate by parts with `u x = x ^ (n+1)` and `v x = e^(x-1)` (so `v' = v`). The boundary term is
    `1 · e⁰ - 0 · e⁻¹ = 1`, and the remaining integral is `(n+1)` times the one defining `I n`.
H2. Build `hu : ∀ x ∈ Set.uIcc 0 1, HasDerivAt (fun x => x ^ (n+1)) ((n+1 : ℕ) * x ^ n) x` (`simpa using
    hasDerivAt_pow (n+1) x`) and `hv` from the REFERENCE example; after the IBP rewrite, `simp` the boundary
    values and pull the constant out of the integral. `error_amplification`: induction on n.
H3. Constant: `rw [show (fun x : ℝ => ((n+1 : ℕ) : ℝ) * x ^ n * Real.exp (x - 1)) = fun x => ((n+1 : ℕ) : ℝ) *
    (x ^ n * Real.exp (x - 1)) by funext x; ring, intervalIntegral.integral_const_mul]`. Induction step:
    `rw [hJ, I_succ, Nat.factorial_succ]; push_cast; linear_combination (-(n + 1 : ℝ)) * ih`.
-/
