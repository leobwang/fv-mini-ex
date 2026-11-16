/- M115 | Interpolatory quadrature is exact | 15-20 min | Lagrange.basis, eval_finsetSum, integral_finsetSum, conv, mathlib
GOAL
  Take n distinct nodes `v i` (i ∈ s) and weights `wᵢ = ∫ₐᵇ Lᵢ(x) dx`, where `Lᵢ = Lagrange.basis s v i` is the
  polynomial of degree < n with `Lᵢ(v j) = 1` if j = i and 0 otherwise. Show that the rule `∑ᵢ wᵢ p(v i)`
  integrates every polynomial `p` of degree < n exactly (the principle behind Newton–Cotes and Gauss rules).

REFERENCE
  #check Lagrange.eq_interpolate     -- (hv : Set.InjOn v s) (hp : p.degree < s.card) : p = interpolate s v (fun i => p.eval (v i))
  #check Lagrange.interpolate_apply  -- interpolate s v r = ∑ i ∈ s, C (r i) * Lagrange.basis s v i
  #check Polynomial.eval_finsetSum   -- (∑ i ∈ s, g i).eval x = ∑ i ∈ s, (g i).eval x   (also `eval_mul`, `eval_C`)
  #check intervalIntegral.integral_finsetSum  -- (∀ i ∈ s, IntervalIntegrable (f i) μ a b) → ∫ x in a..b, ∑ i ∈ s, f i x = ∑ i ∈ s, ∫ ...
  #check intervalIntegral.integral_const_mul  -- ∫ x in a..b, c * f x = c * ∫ x in a..b, f x
  example (p : ℝ[X]) (c a b : ℝ) : IntervalIntegrable (fun x => c * p.eval x) MeasureTheory.volume a b :=
    ((Polynomial.continuous p).intervalIntegrable a b).const_mul c
  `conv_lhs => rw [h]` rewrites only the left-hand side of the goal.
  `∫ x in a..b, f x` is the integral over [a, b]; `C c : ℝ[X]` is the constant polynomial c; `ℝ[X]` needs `open Polynomial`.
NOTE: a plain `rw [Lagrange.eq_interpolate hv hp]` would also rewrite the `p` inside `p.eval (v i)` on the right.
-/
import Mathlib

open Polynomial

namespace M115

-- BEGIN SPEC
theorem interpolatory_quadrature_exact {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ℝ)
    (hv : Set.InjOn v s) (a b : ℝ) (p : ℝ[X]) (hp : p.degree < s.card) :
    ∫ x in a..b, p.eval x =
      ∑ i ∈ s, (∫ x in a..b, (Lagrange.basis s v i).eval x) * p.eval (v i) :=
-- END SPEC
  sorry

end M115

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. On the left only, replace `p` by its own interpolant: since deg p < s.card, `p` equals the Lagrange
    interpolant of its values `p.eval (v i)`, which is `∑ i ∈ s, C (p.eval (v i)) * Lagrange.basis s v i`.
H2. Evaluate the sum termwise (`eval_finsetSum`, `eval_mul`, `eval_C`), swap integral and finite sum
    (`integral_finsetSum`, each summand is a constant times a polynomial, hence integrable), then pull the
    constant `p.eval (v i)` out of each integral and compare term by term.
H3. Start with `conv_lhs => rw [Lagrange.eq_interpolate hv hp, Lagrange.interpolate_apply]` and then
    `simp only [eval_finsetSum, eval_mul, eval_C]`; the rest is H2's swap-and-compare.
-/
