/- M095 | Mean of the Poisson distribution | 20 min | poissonMeasure, tsum, HasSum, index shift, mathlib
GOAL
  The Poisson law `Po(r)`, `P(K = k) = e^{-r} r^k / k!`, has mean `r`. Mathlib does not have this: turn
  the expectation into a series, shift the index by one, and reuse that the probabilities sum to 1.

REFERENCE
  `poissonMeasure r : Measure ℕ` (notation `Po(r)`), rate `r : ℝ≥0` (a nonnegative real, used as `(r : ℝ)`).
  `HasSum f a`: the series `∑ f n` converges (unconditionally) to `a`. `∑' n, f n` is its value (0 if divergent).
  `•` is scalar multiplication, here ordinary `*` (`smul_eq_mul`).
  #check integral_poissonMeasure   -- ∫ n, f n ∂Po(r) = ∑' n, (exp (-r) * r ^ n / n.factorial) • f n
  #check hasSum_one_poissonMeasure -- HasSum (fun n => exp (-r) * r ^ n / n.factorial) 1
  #check HasSum.mul_left           -- (a₂) → HasSum f a₁ → HasSum (fun i => a₂ * f i) (a₂ * a₁)
  #check hasSum_nat_add_iff'       -- (k) → (HasSum (fun n => f (n + k)) (g - ∑ i ∈ range k, f i) ↔ HasSum f g)
  #check HasSum.tsum_eq            -- HasSum f a → ∑' b, f b = a
  #check Nat.factorial_succ        -- (n + 1).factorial = (n + 1) * n.factorial
  `set f : ℕ → ℝ := fun n => … with hf` names the summand; `push_cast` moves casts inward, then `field_simp`.
NOTE: prove a function identity with `funext n` and `rw` it, rather than `convert … using 1` on a `HasSum` (it leaves instance goals).
-/
import Mathlib

namespace M095

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem poisson_mean (r : ℝ≥0) :
    ∫ k, (k : ℝ) ∂(poissonMeasure r) = r :=
-- END SPEC
  by
    rw [integral_poissonMeasure]
    set f : ℕ → ℝ := fun n => (Real.exp (-r) * r ^ n / n.factorial) • (n : ℝ) with hf
    -- the shifted series is `r` times the total probability
    have hshift : HasSum (fun n => f (n + 1)) r := by
      have h1 := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
      rw [mul_one] at h1
      have e : (fun n => f (n + 1)) = fun i => (r : ℝ) * (Real.exp (-r) * r ^ i / i.factorial) := by
        funext n
        simp only [hf, smul_eq_mul, Nat.factorial_succ]
        push_cast
        field_simp
        ring
      rw [e]
      exact h1
    have : HasSum f r := by
      rw [← hasSum_nat_add_iff' 1]
      simpa [hf] using hshift
    exact this.tsum_eq

end M095

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Show `HasSum f r` for the summand `f n = (e^{-r} rⁿ / n!) • n` and conclude with `.tsum_eq`. The `n = 0`
    term is 0, and `f (n + 1) = r · (e^{-r} rⁿ / n!)`: the shifted series is `r` times the total probability.
H2. Get `HasSum (fun n => f (n + 1)) r` from `(hasSum_one_poissonMeasure r).mul_left r` after a `funext`
    identity (`Nat.factorial_succ`, `push_cast`, `field_simp`, `ring`). Unshift with `hasSum_nat_add_iff' 1`.
H3. `have : HasSum f r := by rw [← hasSum_nat_add_iff' 1]; simpa [hf] using hshift`, then `exact this.tsum_eq`.
-/
