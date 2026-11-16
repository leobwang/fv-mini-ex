/- M122 | Harmonic oscillator: Euler vs symplectic Euler | 15-20 min | Prod, recursion, induction, linear_combination, nlinarith, energy, mathlib
GOAL
  Integrate q' = p, p' = -ω²q with step h. Explicit Euler multiplies the energy `p² + ω²q²` by exactly
  `1 + h²ω²` every step (the orbit spirals out). Symplectic Euler (new p first, then q with the new p)
  conserves the shadow energy `p² + ω²q² - hω²qp`, so for `hω < 2` the true energy stays bounded forever.

REFERENCE
  example (a b : ℝ) (h : a = 2 * b) : a ^ 2 = 4 * b ^ 2 := by linear_combination (a + 2 * b) * h
  --   ^ `linear_combination e₁ * h₁ + …` closes `lhs = rhs` when `lhs - rhs - Σ eᵢ (hᵢ.lhs - hᵢ.rhs)` is 0 by `ring`
  example (s : ℕ → ℝ × ℝ) : s 0 = ((s 0).1, (s 0).2) := rfl   -- `.1` is position q, `.2` is momentum p
  `simp only [sympHO]` unfolds one step of the recursion (its `let` too); `induction n with | zero => … | succ n ih => …`
  `set q := (sympHO ω h q₀ p₀ n).1 with hq` -- name a subterm everywhere (goal and hypotheses)
  #check div_mul_eq_mul_div    -- a / b * c = a * c / b
  #check le_div_iff₀           -- 0 < c → (a ≤ b / c ↔ a * c ≤ b)
  example (x y : ℝ) (hx : 0 ≤ x) : 0 ≤ x * (y - 1) ^ 2 := mul_nonneg hx (sq_nonneg _)
  `nlinarith [t₁, t₂]` adds the facts `tᵢ` (and products of pairs of hypotheses) and runs `linarith`.
BANNED: grind, try?
NOTE: `grind` and `try?` are banned: they close the two identities without the algebra you are meant to do.
-/
import Mathlib

namespace M122

-- BEGIN SPEC
/-- explicit Euler for q' = p, p' = -ω²q; a state is (q, p) -/
def eulerHO (ω h q₀ p₀ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (q₀, p₀)
  | n + 1 => ((eulerHO ω h q₀ p₀ n).1 + h * (eulerHO ω h q₀ p₀ n).2,
              (eulerHO ω h q₀ p₀ n).2 - h * ω ^ 2 * (eulerHO ω h q₀ p₀ n).1)

/-- symplectic Euler: new momentum first, then position with the new momentum -/
def sympHO (ω h q₀ p₀ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (q₀, p₀)
  | n + 1 =>
    let p' := (sympHO ω h q₀ p₀ n).2 - h * ω ^ 2 * (sympHO ω h q₀ p₀ n).1
    ((sympHO ω h q₀ p₀ n).1 + h * p', p')
-- END SPEC

-- BEGIN SPEC
theorem euler_energy_grows (ω h q₀ p₀ : ℝ) (n : ℕ) :
    (eulerHO ω h q₀ p₀ n).2 ^ 2 + ω ^ 2 * (eulerHO ω h q₀ p₀ n).1 ^ 2
      = (1 + h ^ 2 * ω ^ 2) ^ n * (p₀ ^ 2 + ω ^ 2 * q₀ ^ 2) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem symp_shadow_energy (ω h q₀ p₀ : ℝ) (n : ℕ) :
    (sympHO ω h q₀ p₀ n).2 ^ 2 + ω ^ 2 * (sympHO ω h q₀ p₀ n).1 ^ 2
        - h * ω ^ 2 * (sympHO ω h q₀ p₀ n).1 * (sympHO ω h q₀ p₀ n).2
      = p₀ ^ 2 + ω ^ 2 * q₀ ^ 2 - h * ω ^ 2 * q₀ * p₀ :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem symp_energy_bounded (ω h q₀ p₀ : ℝ) (hω : 0 ≤ ω) (hh : 0 ≤ h) (hstab : h * ω < 2) (n : ℕ) :
    (sympHO ω h q₀ p₀ n).2 ^ 2 + ω ^ 2 * (sympHO ω h q₀ p₀ n).1 ^ 2
      ≤ (2 + h * ω) / (2 - h * ω) * (p₀ ^ 2 + ω ^ 2 * q₀ ^ 2) :=
-- END SPEC
  sorry

end M122

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The first two are inductions whose step is a pure polynomial identity; the third needs no induction: use `symp_shadow_energy` at `n`.
H2. Euler step: unfold one step and use `linear_combination` with the IH scaled by the growth factor. Shadow step: rewrite the right side with `← ih`, unfold, `ring`. Bound: with `E = p² + ω²q²` and `S` the shadow energy, `2ω|q||p| ≤ E` gives `(1 - hω/2) E ≤ S ≤ (1 + hω/2) E`.
H3. Euler: the `linear_combination` coefficient is the growth factor `1 + h ^ 2 * ω ^ 2`. Bound: clear the fraction with `div_mul_eq_mul_div` and `le_div_iff₀`; with `q, p` the step-`n` state, the two facts `nlinarith` needs are `0 ≤ h * ω * (ω * q - p) ^ 2` and `0 ≤ h * ω * (ω * q₀ + p₀) ^ 2`.
-/
