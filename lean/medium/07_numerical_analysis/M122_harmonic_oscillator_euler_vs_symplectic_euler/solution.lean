/- M122 | Harmonic oscillator: Euler vs symplectic Euler | 15-20 min | Prod, recursion, induction, linear_combination, nlinarith, energy, mathlib
GOAL
  Integrate q' = p, p' = -ω²q with step h. Explicit Euler multiplies the energy `p² + ω²q²` by exactly
  `1 + h²ω²` every step (the orbit spirals out). Symplectic Euler (new p first, then q with the new p)
  conserves the shadow energy `p² + ω²q² - hω²qp`, so for `hω < 2` the true energy stays bounded forever.

BANNED: grind, try?

GUIDE
  Entries R1–R14: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · euler_energy_grows
  1. Induct on the step count `n`:                                          R1
  2. `zero`: unfold step 0, the pair projections and `x ^ 0`:               R2  (d = eulerHO)
  3. `succ`: unfold exactly one step; step `n` stays folded, so `ih` fits:  R3  (d = eulerHO)
       the goal is now a polynomial in `(eulerHO ω h q₀ p₀ n).1`, `.2`
  4. Close with `ih` scaled by the factor one step multiplies the energy by: R4
-/
-- BEGIN SPEC
theorem euler_energy_grows (ω h q₀ p₀ : ℝ) (n : ℕ) :
    (eulerHO ω h q₀ p₀ n).2 ^ 2 + ω ^ 2 * (eulerHO ω h q₀ p₀ n).1 ^ 2
      = (1 + h ^ 2 * ω ^ 2) ^ n * (p₀ ^ 2 + ω ^ 2 * q₀ ^ 2) :=
-- END SPEC
  by
    induction n with
    | zero => simp [eulerHO]
    | succ n ih =>
      simp only [eulerHO]
      linear_combination (1 + h ^ 2 * ω ^ 2) * ih

/- SKELETON · symp_shadow_energy
  1. Induct on `n`:                                                         R1
  2. `zero`:                                                                R2  (d = sympHO)
  3. `succ`: turn the constant right side into the step-`n` shadow energy:  R5
  4. Unfold one step; the `let p'` is inlined:                              R6  (d = sympHO)
  5. The one-step identity is a polynomial identity:                        ring
-/
-- BEGIN SPEC
theorem symp_shadow_energy (ω h q₀ p₀ : ℝ) (n : ℕ) :
    (sympHO ω h q₀ p₀ n).2 ^ 2 + ω ^ 2 * (sympHO ω h q₀ p₀ n).1 ^ 2
        - h * ω ^ 2 * (sympHO ω h q₀ p₀ n).1 * (sympHO ω h q₀ p₀ n).2
      = p₀ ^ 2 + ω ^ 2 * q₀ ^ 2 - h * ω ^ 2 * q₀ * p₀ :=
-- END SPEC
  by
    induction n with
    | zero => simp [sympHO]
    | succ n ih => rw [← ih]; simp only [sympHO]; ring

/- SKELETON · symp_energy_bounded   (no induction: `symp_shadow_energy` does that work)
  1. Get the conserved shadow energy at step `n` from `symp_shadow_energy`:  R7
  2. Name the step-`n` state `q`, `p` (after step 1, so `hS` is renamed too): R8
  3. The fact `hc : 0 ≤ h * ω`:                                              R9
  4. Clear the fraction; the side goal `0 < 2 - h * ω` comes from `hstab`:   R11 → R12, R13
  5. Close with two hints, each `hc` times a square (which squares: see the
     sandwich in cheatsheet.md, Part 3):                                     R9, R10 → R14
-/
-- BEGIN SPEC
theorem symp_energy_bounded (ω h q₀ p₀ : ℝ) (hω : 0 ≤ ω) (hh : 0 ≤ h) (hstab : h * ω < 2) (n : ℕ) :
    (sympHO ω h q₀ p₀ n).2 ^ 2 + ω ^ 2 * (sympHO ω h q₀ p₀ n).1 ^ 2
      ≤ (2 + h * ω) / (2 - h * ω) * (p₀ ^ 2 + ω ^ 2 * q₀ ^ 2) :=
-- END SPEC
  by
    have hS := symp_shadow_energy ω h q₀ p₀ n
    set q := (sympHO ω h q₀ p₀ n).1
    set p := (sympHO ω h q₀ p₀ n).2
    have hc : 0 ≤ h * ω := mul_nonneg hh hω
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    -- WHY: 2ω|q||p| ≤ p² + ω²q² sandwiches the shadow energy between (1 ∓ hω/2) times the energy
    nlinarith [mul_nonneg hc (sq_nonneg (ω * q - p)), mul_nonneg hc (sq_nonneg (ω * q₀ + p₀))]

end M122

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The first two are inductions on `n` whose step is a pure polynomial identity in the step-`n` state;
    the third needs no induction: use `symp_shadow_energy` at `n`.
H2. Euler step: unfold one step with `simp only [eulerHO]` and close with `linear_combination`, scaling `ih`
    by the growth factor. Shadow step: `rw [← ih]`, `simp only [sympHO]`, `ring`. Bound: with `E = p² + ω²q²`
    at step `n` and `S` the shadow energy, `0 ≤ hω(ωq - p)²` gives `(2 - hω) E ≤ 2S`, and
    `0 ≤ hω(ωq₀ + p₀)²` gives `2S₀ ≤ (2 + hω) E₀`; `S = S₀` chains them.
H3. Euler: `linear_combination (1 + h ^ 2 * ω ^ 2) * ih`. Bound: with `q, p` the step-`n` state (`set`) and
    `hc : 0 ≤ h * ω`, clear the fraction with `rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]`; the two
    `nlinarith` hints are `mul_nonneg hc (sq_nonneg (ω * q - p))` and `mul_nonneg hc (sq_nonneg (ω * q₀ + p₀))`.
-/
