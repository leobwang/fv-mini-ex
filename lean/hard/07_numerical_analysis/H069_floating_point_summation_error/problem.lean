/- H069 | Floating-point summation error | 1-1.5 h | inductive types, structural induction, relative error model, gcongr, mathlib
GOAL
  Standard model: each rounded addition returns `s (1 + δ)` with `|δ| ≤ u`. Adding along any binary tree has
  error `≤ ((1 + u)^depth - 1) · ∑ |xᵢ|`; also prove the list version (recursive summation, depth `n`) directly.
  (Pairwise summation has depth ⌈log₂ n⌉, which is why it is far more accurate.)

GUIDE
  Entries R1–R27: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H069

-- BEGIN SPEC
/-- `fl` rounds every real with relative error at most `u`. -/
def RelErr (u : ℝ) (fl : ℝ → ℝ) : Prop := ∀ x, ∃ δ, |δ| ≤ u ∧ fl x = x * (1 + δ)

/-- a summation order: leaves hold the inputs, each node is one addition -/
inductive STree where
  | leaf (x : ℝ)
  | node (l r : STree)

/-- the exact sum of the leaves -/
def STree.exact : STree → ℝ
  | leaf x => x
  | node l r => l.exact + r.exact
/-- `∑ |xᵢ|` over the leaves -/
def STree.absSum : STree → ℝ
  | leaf x => |x|
  | node l r => l.absSum + r.absSum
/-- number of additions on the longest root-to-leaf path -/
def STree.depth : STree → ℕ
  | leaf _ => 0
  | node l r => max l.depth r.depth + 1
/-- the floating-point sum: every addition is rounded -/
def STree.flSum (fl : ℝ → ℝ) : STree → ℝ
  | leaf x => x
  | node l r => fl (l.flSum fl + r.flSum fl)

/-- recursive summation of a list: `[x₁, …, xₙ] ↦ fl (x₁ + fl (x₂ + … fl (xₙ + 0)))` -/
def fsum (fl : ℝ → ℝ) : List ℝ → ℝ
  | [] => 0
  | x :: xs => fl (x + fsum fl xs)
-- END SPEC

/- SKELETON · abs_exact_le   (milestone: prove it first; used in tree_sum_error steps 4 and 6)
  1. Induction on `t`:                                                      R1
  2. leaf: unfold, then `simp` closes `|x| ≤ |x|`:                          R2
  3. node: unfold, then triangle inequality chained with both IHs:          R2, then R4 → R3 → R5
-/
-- MILESTONE (optional: change or delete)
theorem abs_exact_le (t : STree) : |t.exact| ≤ t.absSum := by
  sorry

/- SKELETON · abs_list_sum_le   (milestone: prove it first; used in fsum_error step 5)
  1. Induction on `xs`; nil: `simp`:                                        R6
  2. cons: rewrite the list functions at `x :: xs`:                         R7
  3. triangle inequality, then the rest is linear in `|x|`, `|xs.sum|`:      R4 → R3, R8
-/
-- MILESTONE (optional: change or delete)
theorem abs_list_sum_le (xs : List ℝ) : |xs.sum| ≤ (xs.map abs).sum := by
  sorry

/- SKELETON · one_add_delta   (milestone: prove it first; used in both main theorems)
  1. Both absolute values → pairs of linear inequalities:                   R9
  2. Split the `∧` and close each half:                                     constructor, R8
-/
-- MILESTONE (optional: change or delete)
theorem one_add_delta (u δ : ℝ) (hδ : |δ| ≤ u) : |1 + δ| ≤ 1 + u := by
  sorry

/- SKELETON · tree_sum_error
  0. MILESTONES first: `abs_exact_le` (steps 4, 6) and `one_add_delta` (step 6).
  1. Induction on `t`:                                                      R1
  2. leaf: unfold `flSum`, `exact`, `depth`; `simp` closes the rest:        R2, R10
  3. node: take the rounding error of this node's addition, then unfold and substitute:
       obtain ⟨δ, hδ, hs⟩ := hfl (l.flSum fl + r.flSum fl)                  R11
       unfold `flSum, exact, absSum, depth`; rw [hs]; set d := max l.depth r.depth   R2, rw [hs], R12
  4. Facts for gcongr:  hAl : 0 ≤ l.absSum,  hAr : 0 ≤ r.absSum             R13, R3 with abs_exact_le
  5. Lift both IHs to depth d:
       el : |l.flSum fl - l.exact| ≤ ((1 + u) ^ d - 1) * l.absSum,  er likewise   R3, R15, R8, R16
  6. Split the error with an identity (propagated part + new rounding):     R17
       … = ((l.flSum fl - l.exact) + (r.flSum fl - r.exact)) * (1 + δ) + (l.exact + r.exact) * δ
     then a calc with three links:                                          R18
       a. ≤ |… * (1 + δ)| + |… * δ|                                         R4
       b. ≤ (((1 + u) ^ d - 1) * l.absSum + ((1 + u) ^ d - 1) * r.absSum) * (1 + u) + (l.absSum + r.absSum) * u
            hd1 : 1 ≤ (1 + u) ^ d first, then rw [abs_mul, abs_mul], gcongr  R20, R19, R21
            three goals: R4 → R3 → R5 with el, er;  one_add_delta;  R4 → R3 → R5 with abs_exact_le
       c. = ((1 + u) ^ (d + 1) - 1) * (l.absSum + r.absSum)                 R22
-/
-- BEGIN SPEC
theorem tree_sum_error (u : ℝ) (hu : 0 ≤ u) (fl : ℝ → ℝ) (hfl : RelErr u fl) (t : STree) :
    |t.flSum fl - t.exact| ≤ ((1 + u) ^ t.depth - 1) * t.absSum :=
-- END SPEC
  sorry

/- SKELETON · fsum_error
  0. MILESTONES first: `abs_list_sum_le` (step 5b) and `one_add_delta` (step 5b).
  1. Induction on `xs`; nil: `simp [fsum]`:                                 R6, R10
  2. cons: take the rounding error, unfold, substitute:
       obtain ⟨δ, hδ, hs⟩ := hfl (x + fsum fl xs)                           R11
       unfold `fsum` and the list functions; rw [hs]                       R2, R7
  3. Facts:  hA : 0 ≤ (xs.map abs).sum,  hn1 : 1 ≤ (1 + u) ^ xs.length      R23, R20
  4. Split the error: … = (fsum fl xs - xs.sum) * (1 + δ) + (x + xs.sum) * δ   R17
  5. calc with three links:                                                 R18
       a. ≤ |… * (1 + δ)| + |… * δ|                                         R4
       b. ≤ ((1 + u) ^ xs.length - 1) * (xs.map abs).sum * (1 + u) + (|x| + (xs.map abs).sum) * u
            rw [abs_mul, abs_mul], gcongr (the IH goal closes by itself)    R19, R21
            two goals: one_add_delta;  R4 → R3 with R8 and abs_list_sum_le
       c. ≤ ((1 + u) ^ (xs.length + 1) - 1) * (|x| + (xs.map abs).sum)   (an inequality, not ring)
            rw [pow_succ], then nlinarith with the hint
            0 ≤ |x| * (1 + u) * ((1 + u) ^ xs.length - 1)                   R24, R27
            built from abs_nonneg x, 0 ≤ 1 + u (linarith) and hn1:          R25, R13, R8, R26
-/
-- BEGIN SPEC
theorem fsum_error (u : ℝ) (hu : 0 ≤ u) (fl : ℝ → ℝ) (hfl : RelErr u fl) (xs : List ℝ) :
    |fsum fl xs - xs.sum| ≤ ((1 + u) ^ xs.length - 1) * (xs.map abs).sum :=
-- END SPEC
  sorry

end H069

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Induction on the tree. At a node, the only thing you know about `fl` is `hfl s` for the sum
    `s = l.flSum fl + r.flSum fl` that is rounded: it gives `δ` with `|δ| ≤ u` and `fl s = s * (1 + δ)`.
    The new error is the children's errors times `(1 + δ)` plus the exact sum times `δ`.
H2. Prove the three milestones first. At a node, lift both IHs to the common depth `d = max l.depth r.depth`
    (`gcongr`, which needs `0 ≤ l.absSum` from `abs_exact_le`). Rewrite the error as
    propagated + new, then a `calc`: triangle inequality; `abs_mul` and `gcongr` against
    `|1 + δ| ≤ 1 + u` and `|exact| ≤ absSum`; and `ring`, by the identity
    `((1 + u) ^ d - 1) * (1 + u) + u = (1 + u) ^ (d + 1) - 1`. The list version is the same induction on `xs`.
H3. Node: `rw [show (l.flSum fl + r.flSum fl) * (1 + δ) - (l.exact + r.exact)
      = ((l.flSum fl - l.exact) + (r.flSum fl - r.exact)) * (1 + δ) + (l.exact + r.exact) * δ by ring]`;
    lift with `ihl.trans (by gcongr; exacts [by linarith, le_max_left _ _])`; before the middle link's
    `gcongr`, `have hd1 : (1 : ℝ) ≤ (1 + u) ^ d := one_le_pow₀ (by linarith)`.
    List, last link: `rw [pow_succ]`, then
    `nlinarith [mul_nonneg (mul_nonneg (abs_nonneg x) (by linarith : (0 : ℝ) ≤ 1 + u)) (sub_nonneg.mpr hn1)]`.
-/
