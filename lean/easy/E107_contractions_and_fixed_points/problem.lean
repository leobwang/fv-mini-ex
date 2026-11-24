/- E107 | Contractions and fixed points | 2-3 min | LipschitzWith, ContractingWith, IsFixedPt, NNReal, mathlib
GOAL
  Show that `g x = x / 2 + 1` is Lipschitz with constant `1/2`, hence a contraction, and that `2` is a
  fixed point of `g`. This is the vocabulary of fixed-point iteration `x_{n+1} = g x_n`.

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E107

/- SKELETON · half_lipschitz
  1. `LipschitzWith` → a `dist` bound for two points `x y`:                          R1
  2. One `simp only`: every `dist` → `|·|`, the constant `↑(1 / 2)` → `1 / 2 : ℝ`:   R2, R3, R4, R5
  3. Reshape the difference to `(x - y) / 2`:                                         R6
  4. Split the absolute value of the quotient, then `|2|` → `2`:                      R7, R8
  5. Close the linear inequality (`|x - y|` is one unknown):                          R9
-/
-- BEGIN SPEC
theorem half_lipschitz : LipschitzWith (1 / 2) (fun x : ℝ => x / 2 + 1) :=
-- END SPEC
  sorry

/- SKELETON · half_contracting
  1. Build the pair `⟨_, _⟩` (term mode is enough):                                  R10
       first component  `1 / 2 < 1` in `NNReal`:                                    R11
       second component the Lipschitz fact: `half_lipschitz` by name
-/
-- BEGIN SPEC
theorem half_contracting : ContractingWith (1 / 2) (fun x : ℝ => x / 2 + 1) :=
-- END SPEC
  sorry

/- SKELETON · two_is_fixed
  1. Unfold `Function.IsFixedPt` (simp also substitutes `2` into the `fun`):          R12
  2. Close the numeral equation:                                                     R11
     (one call does both: R12's `norm_num [Function.IsFixedPt]`)
-/
-- BEGIN SPEC
theorem two_is_fixed : Function.IsFixedPt (fun x : ℝ => x / 2 + 1) 2 :=
-- END SPEC
  sorry

end E107

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each predicate is a definition: `LipschitzWith` is a bound on distances, `ContractingWith K f` is
    `K < 1 ∧ LipschitzWith K f`, `Function.IsFixedPt f x` is `f x = x`. On `ℝ`, distance is `|x - y|`.
H2. Lipschitz: switch to `dist` with `LipschitzWith.of_dist_le_mul` (R1), turn `dist` into `|·|` and the
    `NNReal` constant `↑(1 / 2)` into the real `1 / 2` with one `simp only` (R2–R5), rewrite the difference as
    `(x - y) / 2`, pull `|2|` out, finish with `linarith`. Contraction: the pair of `1 / 2 < 1` and `half_lipschitz`.
    Fixed point: unfold `Function.IsFixedPt` and compute.
H3. `refine LipschitzWith.of_dist_le_mul fun x y => ?_`, then
    `simp only [Real.dist_eq, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]`, then
    `rw [show x / 2 + 1 - (y / 2 + 1) = (x - y) / 2 by ring, abs_div, abs_two]; linarith`.
    The contraction is the pair `⟨(proof of 1 / 2 < 1), half_lipschitz⟩`; for the fixed point, give `norm_num`
    the definition `Function.IsFixedPt` to unfold.
-/
