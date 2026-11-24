/- M115 | Interpolatory quadrature is exact | 15-20 min | Lagrange.basis, eval_finsetSum, integral_finsetSum, conv, mathlib
GOAL
  Take n distinct nodes `v i` (i ∈ s) and weights `wᵢ = ∫ₐᵇ Lᵢ(x) dx`, where `Lᵢ = Lagrange.basis s v i` is the
  polynomial of degree < n with `Lᵢ(v j) = 1` if j = i and 0 otherwise. Show that the rule `∑ᵢ wᵢ p(v i)`
  integrates every polynomial `p` of degree < n exactly (the principle behind Newton–Cotes and Gauss rules).

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Polynomial

namespace M115

/- SKELETON · interpolatory_quadrature_exact
  1. On the LEFT side only, replace `p` by its Lagrange interpolant (uses `hv`, `hp`),
     then expand the interpolant as a sum over the basis:                    R1 with R2, R3
       (the `p` in `eval (v i) p` on the right must stay as it is)
  2. Push `eval x` through the sum, the product and the constant `C _`
     (all under `∫ x in a..b, …`, so `simp only`, not `rw`):                 R4, R5, R6
  3. Swap `∫` and `∑`:                                                       R7
       side goal: for each `i ∈ s`, `fun x => eval (v i) p * eval x (Lagrange.basis s v i)`
       is interval integrable (a constant times a polynomial): intro i hi,  R8 → R9 → R10
       It is the SECOND goal, after the main one (steps 4–5); or pass its proof as
       R7's argument (cheatsheet R7, W4) so it never appears
  4. Compare the two sums term by term:                                      R11
  5. In each term, pull the constant `eval (v i) p` out of the integral,
     then swap the two factors to match the right side:                     R12, R13
-/
-- BEGIN SPEC
theorem interpolatory_quadrature_exact {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ℝ)
    (hv : Set.InjOn v s) (a b : ℝ) (p : ℝ[X]) (hp : p.degree < s.card) :
    ∫ x in a..b, p.eval x =
      ∑ i ∈ s, (∫ x in a..b, (Lagrange.basis s v i).eval x) * p.eval (v i) :=
-- END SPEC
  sorry

end M115

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Since `p.degree < s.card`, `p` is its own Lagrange interpolant on the nodes. Substitute that on the
    left side only: the left becomes the integral of a finite sum, and the right is already a finite sum.
H2. `conv_lhs` with `Lagrange.eq_interpolate hv hp` and `Lagrange.interpolate_apply` (R1–R3); then
    `simp only [eval_finsetSum, eval_mul, eval_C]` (R4–R6); swap `∫` and `∑` with
    `intervalIntegral.integral_finsetSum` (R7: each summand is a constant times a polynomial, so continuous,
    so integrable, R8–R10); finally compare term by term with `Finset.sum_congr rfl` (R11).
H3. Key lines: `conv_lhs => rw [Lagrange.eq_interpolate hv hp, Lagrange.interpolate_apply]`; the side goal
    of R7 is `((Polynomial.continuous _).intervalIntegrable _ _).const_mul _` for each `i`; each term closes
    with `rw [intervalIntegral.integral_const_mul, mul_comm]`.
-/
