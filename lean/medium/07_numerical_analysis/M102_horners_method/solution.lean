/- M102 | Horner's method | 10-15 min | List, induction, Finset.sum, getD, Polynomial.eval, mathlib
GOAL
  Horner's rule `c₀ + x * (c₁ + x * (c₂ + …))` computes `∑ cᵢ * xⁱ` (n multiplications instead of
  ~n²/2), and run on a polynomial's coefficient list `[p₀, p₁, …, p_d]` it computes `p.eval x`.

REFERENCE
  #check Finset.sum_range_succ'   -- ∑ k ∈ range (n + 1), f k = ∑ k ∈ range n, f (k + 1) + f 0
  #check Finset.mul_sum           -- a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i
  #check List.getD_cons_succ      -- (x :: xs).getD (n + 1) d = xs.getD n d   (and `List.getD_cons_zero`)
  #check List.getD_eq_getElem?_getD   -- l.getD i d = l[i]?.getD d
  #check Polynomial.eval_eq_sum_range -- p.eval x = ∑ i ∈ range (p.natDegree + 1), p.coeff i * x ^ i
  example (f g : ℕ → ℝ) (h : ∀ i ∈ Finset.range 3, f i = g i) :
      ∑ i ∈ Finset.range 3, f i = ∑ i ∈ Finset.range 3, g i := Finset.sum_congr rfl h
  `xs.getD i 0` is the i-th entry of `xs` (0 if `i ≥ xs.length`); `p.coeff i` is the coefficient of `Xⁱ`.
  `ℝ[X]` (polynomials over ℝ) needs `open Polynomial`; `List.range n = [0, 1, …, n-1]`.
  `p.natDegree : ℕ` is the degree of `p` (0 for `p = 0`), so the list has `natDegree + 1` coefficients.
-/
import Mathlib

namespace M102

-- BEGIN SPEC
open Polynomial

-- coefficients low-to-high: [c₀, c₁, …, cₙ] ↦ c₀ + x * (c₁ + x * (… + x * cₙ))
def horner (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | c :: cs => c + x * horner x cs
-- END SPEC

-- BEGIN SPEC
theorem horner_eq_sum (x : ℝ) (cs : List ℝ) :
    horner x cs = ∑ i ∈ Finset.range cs.length, cs.getD i 0 * x ^ i :=
-- END SPEC
  by
    induction cs with
    | nil => simp [horner]
    | cons c cs ih =>
      rw [horner, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
      rw [add_comm]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring

-- BEGIN SPEC
theorem horner_eval (p : ℝ[X]) (x : ℝ) :
    horner x ((List.range (p.natDegree + 1)).map p.coeff) = p.eval x :=
-- END SPEC
  by
    rw [horner_eq_sum, eval_eq_sum_range]
    simp only [List.length_map, List.length_range]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    simp [List.getD_eq_getElem?_getD, hi]

end M102

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `horner_eq_sum`: induction on `cs`. In the cons case, peel off the `i = 0` term of the sum with
    `Finset.sum_range_succ'`; what is left is `x *` (the sum for `cs`), shifted by one index.
H2. `horner_eval`: rewrite both sides as sums over `range (p.natDegree + 1)` (the first theorem and
    `eval_eq_sum_range`), then compare term by term with `Finset.sum_congr rfl`.
H3. Cons case: `rw [horner, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]`, then
    `simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]` and finish with
    `add_comm` + `Finset.sum_congr rfl` + `ring`. Termwise in `horner_eval`: `simp [List.getD_eq_getElem?_getD, hi]`
    with `hi : i < p.natDegree + 1`.
-/
