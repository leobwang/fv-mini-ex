/- M102 | Horner's method | 10-15 min | List, induction, Finset.sum, getD, Polynomial.eval, mathlib
GOAL
  Horner's rule `c₀ + x * (c₁ + x * (c₂ + …))` computes `∑ cᵢ * xⁱ` (n multiplications instead of
  ~n²/2), and run on a polynomial's coefficient list `[p₀, p₁, …, p_d]` it computes `p.eval x`.

GUIDE
  Entries R1–R22: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · horner_eq_sum
  1. Induction on the list `cs`:                                            R1
  2. `nil`: unfold `horner` and the empty sum, closed by `simp [horner]`:   R2
  3. `cons c cs ih`, left side: unfold one step, then the IH:               R3, rw [ih]
       goal  c + x * ∑ i ∈ range cs.length, cs.getD i 0 * x ^ i = ∑ … over range (c :: cs).length
  4. Right side: length → `+ 1`, split off the `i = 0` term; push `x` into the left sum:
                                                                            R4 → R5 → R6
  5. Clean the terms under `∑` (simp only, not rw):                         R7, R8, R9, R10
  6. Both sides are now `c + ∑ …` and `∑ … + c`: swap, drop the equal `c`:  R11, R12
  7. The two sums agree termwise; each term is a ring identity:             R13, ring
-/
-- BEGIN SPEC
theorem horner_eq_sum (x : ℝ) (cs : List ℝ) :
    horner x cs = ∑ i ∈ Finset.range cs.length, cs.getD i 0 * x ^ i :=
-- END SPEC
  sorry

/- SKELETON · horner_eval
  MILESTONE: `horner_eq_sum` (Part 1) must be proved first; it is used in step 1.
  1. Both sides as sums over `range (p.natDegree + 1)`:                     rw [horner_eq_sum], R14
  2. Simplify the left range's length:                                      R15, R16
  3. Compare termwise, introducing `i` and `hi`:                            R13
  4. `hi : i ∈ range …` → `hi : i < p.natDegree + 1`:                       R17
  5. Read entry `i` of the mapped list: one `simp` given R18 and `hi`.     R18
     simp then applies R15, R16 (inside the side condition), R19, R21, R22, R20 itself
-/
-- BEGIN SPEC
theorem horner_eval (p : ℝ[X]) (x : ℝ) :
    horner x ((List.range (p.natDegree + 1)).map p.coeff) = p.eval x :=
-- END SPEC
  sorry

end M102

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `horner_eq_sum`: induction on `cs`. In the cons case the left side is `c + x * (sum for cs)`; on the
    right, peel off the `i = 0` term of the sum (`Finset.sum_range_succ'`, R5) and push the `x` into the
    left sum (`Finset.mul_sum`, R6). `horner_eval`: rewrite both sides into sums over
    `range (p.natDegree + 1)` and compare them term by term.
H2. Cons case: `rw [horner, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]`, then clean the
    terms under `∑` with `simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]`.
    `horner_eval`: `rw [horner_eq_sum, eval_eq_sum_range]`, then `simp only [List.length_map, List.length_range]`.
H3. Cons case end: `rw [add_comm]; congr 1; exact Finset.sum_congr rfl fun i _ => by ring`.
    Termwise in `horner_eval`: `refine Finset.sum_congr rfl fun i hi => ?_`, `rw [Finset.mem_range] at hi`,
    then `simp [List.getD_eq_getElem?_getD, hi]`.
-/
