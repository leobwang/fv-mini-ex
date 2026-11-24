/- M117 | An unstable recurrence | 15-20 min | integration by parts, HasDerivAt, factorial, linear_combination, stability, mathlib
GOAL
  `Iₙ = ∫₀¹ xⁿ e^(x-1) dx` satisfies `Iₙ₊₁ = 1 - (n+1) Iₙ` (integrate by parts). Then any sequence `J` obeying
  the same recurrence has `Jₙ - Iₙ = (-1)ⁿ n! (J₀ - I₀)`: an error in the start value is multiplied by n!, so
  running the recurrence forward in floating point is hopeless (a classic forward-unstable recurrence).

GUIDE
  Entries R1–R23: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M117

-- BEGIN SPEC
noncomputable def I (n : ℕ) : ℝ := ∫ x in (0:ℝ)..1, x ^ n * Real.exp (x - 1)
-- END SPEC

/- SKELETON · I_succ
  1. Prove the two derivative facts first, on `Set.uIcc (0:ℝ) 1`:
       hu : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x : ℝ => x ^ (n + 1)) ((n + 1 : ℕ) * x ^ n) x
            the point, the power rule, then fix `n + 1 - 1` and the cast:        R1, R2, R3
       hv : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x => Real.exp (x - 1)) (Real.exp (x - 1)) x
            the point, then a dot-notation chain, then fix `… * 1`:            R1, R4 → R5 → R6 → R7
  2. Integration by parts with u = x ^ (n + 1), v = e^(x-1):
       hibp from hu, hv and the integrability of u' and v'                      R10 with R8, R9
  3. Turn `I` into integrals, then use hibp:                                    R11, rw [hibp]
  4. Boundary term `1 ^ (n+1) * e^(1-1) - 0 ^ (n+1) * e^(0-1)` → `1`, in one `rw [...]`:
       `exp (1 - 1)` → `1`, then `1 ^ (n+1) * 1` → `1`:                          R12, R14
       `0 ^ (n+1)` → `0` (side goal `n + 1 ≠ 0`: write `zero_pow (by simp)`):    R13
       `0 * …`, `… - 0`:                                                        R14
     Not plain `simp`: it also cancels the `1 - ·` on both sides and rewrites `↑(n + 1)`,
     so the function in step 5 no longer matches.
  5. Pull the constant `↑(n + 1)` out of the remaining integral:
       reassociate the integrand as a function equation, then pull out         R16 (R15, ring), R17
  6. Cast `↑(n + 1)` → `↑n + 1`, then the two sides agree:                      R18, ring
-/
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

/- SKELETON · error_amplification
  1. Induction on `n` (`J` and `hJ` stay fixed):                                 R19
  2. Base case `(-1) ^ 0 * ↑(Nat.factorial 0) * (J 0 - I 0)`:                     R20 (`simp`)
  3. Step: one step of `J`, one step of `I` (the theorem above), split `(n+1)!`: R21 (hJ), R21 (I_succ), R22
  4. Cast `↑((n + 1) * n.factorial)` → `(↑n + 1) * ↑n.factorial`:                 R18
  5. The goal is `ih` times the factor `-(n + 1)`, up to ring algebra:           R23
-/
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
    `error_amplification`: induction on `n`; subtracting the two recurrences, the error is multiplied by
    `-(n+1)` at each step (the `1`s cancel).
H2. `I_succ`: build `hu`, `hv` (SKELETON step 1), feed them with two integrability proofs to
    `intervalIntegral.integral_mul_deriv_eq_deriv_mul` as `hibp`, then `unfold I; rw [hibp]`, rewrite the
    boundary term to `1` (`sub_self`, `Real.exp_zero`, `one_pow`, `one_mul`, `zero_pow (by simp)`, `zero_mul`,
    `sub_zero`), pull the constant out with `intervalIntegral.integral_const_mul`, `push_cast; ring`.
    `error_amplification`: base case `simp`; step `rw [hJ, I_succ, Nat.factorial_succ]; push_cast`, then
    `linear_combination`.
H3. `hu := fun x _ => by simpa using hasDerivAt_pow (n + 1) x`;
    `hv := fun x _ => ((hasDerivAt_id' x).sub_const 1).exp.congr_deriv (by ring)`;
    integrability: `((by fun_prop : Continuous fun x : ℝ => ((n + 1 : ℕ) : ℝ) * x ^ n).intervalIntegrable _ _)`.
    Constant: `rw [show (fun x : ℝ => ((n+1 : ℕ) : ℝ) * x ^ n * Real.exp (x - 1)) = fun x => ((n+1 : ℕ) : ℝ) *
    (x ^ n * Real.exp (x - 1)) by funext x; ring, intervalIntegral.integral_const_mul]`.
    Induction step: `linear_combination (-(n + 1 : ℝ)) * ih`.
-/
