/- M119 | Discrete Gronwall inequality | 15 min | induction, strengthening, exp bound, error recursion, mathlib
GOAL
  If an error sequence obeys `eₙ₊₁ ≤ (1 + a) eₙ + b` with `a, b, e₀ ≥ 0`, then `eₙ ≤ e^(na) (e₀ + n b)`.
  This discrete Gronwall inequality is how one bounds the global error of a one-step ODE method
  (`b` = local error per step, `1 + a` = how much one step can amplify an existing error).

REFERENCE
  #check one_le_pow₀          -- 1 ≤ a → 1 ≤ a ^ n
  #check Real.add_one_le_exp  -- x + 1 ≤ exp x
  #check Real.exp_nat_mul     -- exp (n * x) = exp x ^ n
  #check pow_succ             -- a ^ (n + 1) = a ^ n * a
  example (a b c : ℝ) (hc : 0 ≤ c) (h : a ≤ b) : c * a ≤ c * b := by gcongr
  example (n : ℕ) (b : ℝ) : ((n + 1 : ℕ) : ℝ) * b = n * b + b := by push_cast; ring
  `have key : ∀ n : ℕ, e n ≤ ... := by intro n; induction n with ...` proves an auxiliary claim inside a proof.
  `nlinarith [h1, h2]` proves nonlinear (in)equalities using products of the listed facts.
-/
import Mathlib

namespace M119

-- BEGIN SPEC
theorem discrete_gronwall (e : ℕ → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (he0 : 0 ≤ e 0)
    (hstep : ∀ n, e (n + 1) ≤ (1 + a) * e n + b) (n : ℕ) :
    e n ≤ Real.exp (n * a) * (e 0 + n * b) :=
-- END SPEC
  sorry

end M119

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Inducting on the statement as given is awkward because of the exponential. Prove a sharper bound with
    `(1 + a) ^ n` in place of `e^(na)` first, then compare the two factors.
H2. Claim `e n ≤ (1 + a) ^ n * (e 0 + n * b)`. In the step, apply `hstep`, then the IH (multiplied by `1 + a ≥ 0`);
    what remains is `(1+a)·(1+a)ⁿ(e₀ + nb) + b ≤ (1+a)ⁿ⁺¹(e₀ + (n+1)b)`, true because `1 ≤ (1+a)ⁿ⁺¹`.
    Finally `(1 + a)ⁿ ≤ (e^a)ⁿ = e^(na)`.
H3. Step: `calc e (n+1) ≤ (1 + a) * e n + b := hstep n; _ ≤ (1 + a) * ((1 + a) ^ n * (e 0 + n * b)) + b := by gcongr`,
    then `push_cast; rw [pow_succ]; nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 1 + a)]` with
    `h1 : 1 ≤ (1 + a) ^ n := one_le_pow₀ (by linarith)`. End: `gcongr` and `rw [← Real.exp_nat_mul]`.
-/
