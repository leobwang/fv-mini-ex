/- H104 | Boosts along different axes do not compose to a boost | 45-75 min | boost, matrix entries, Fin d sums with ite, symmetric matrices, physlib
GOAL
  In any spatial dimension `d`, a boost along axis `i` times a boost along a different axis `j`
  (both speeds nonzero) is not a pure boost along any axis `k` at any speed `β` (the seed of the
  Thomas–Wigner rotation). Idea: pure boosts are symmetric matrices, the product is not.

GUIDE
  Entries R1–R28: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.Relativity.LorentzGroup.Boosts.Basic

open LorentzGroup Matrix

namespace H104

/- SKELETON · gamma_ne_zero   (milestone; prove it FIRST: the main theorem uses it in step 5)
  1. The fact `this : 0 < 1 - β ^ 2`, by a `have` whose proof turns hβ into two
     inequalities and multiplies them:                                                  R1, R2
  2. Open `γ`, then peel `1 / ·` and `√·` off the goal:                                 R3, R4, R5
     (one `simp` with `γ`, `Real.sqrt_ne_zero'` and `this` does all three)
-/
-- MILESTONE (optional: change or delete)
theorem gamma_ne_zero (β : ℝ) (hβ : |β| < 1) : γ β ≠ 0 := by
  sorry

/- SKELETON · entry_ij   (milestone; prove it SECOND: the main theorem rewrites with it in step 4)
  1. Entry of the group product → time term + spatial sum:                              R6, R7, R8
  2. Plain `simp`: the time term is evaluated and cancels the right side; left is
     `∑ l, (row i of boost i)ₗ * (column j of boost j)ₗ = 0`:                           R9, R10, R11
  3. Every term is 0:                                                                   R12, R13
  4. Split on `l = i`:                                                                  R14
       l = i:  R15, then the second factor is row `l ≠ j` of `boost j`:                 R16, R17 (with hij)
       l ≠ i:  the first factor is 0:                                                   R18 (with hl)
     In each case one `simp [entry lemma, …]` also clears the leftover `x * 0` / `0 * y`.
-/
-- MILESTONE (optional: change or delete)
theorem entry_ij {d : ℕ} {i j : Fin d} (hij : i ≠ j) {β₁ β₂ : ℝ} (h₁ : |β₁| < 1) (h₂ : |β₂| < 1) :
    (boost i β₁ h₁ * boost j β₂ h₂).1 (Sum.inr i) (Sum.inr j) = γ β₁ * β₁ * (γ β₂ * β₂) := by
  sorry

/- SKELETON · entry_ji   (milestone; prove it THIRD: the main theorem rewrites with it in step 4)
  1. Entry of the group product → time term + spatial sum:                              R6, R7, R8
  2. One `simp`, naming three entry lemmas: row `j` of `boost i` is an identity row
     (needs `j ≠ i`, i.e. `Ne.symm hij`), it picks the term `l = j`, and that entry
     `(Sum.inr j, Sum.inr i)` of `boost j` is 0 (with hij):                            R19, R20, R16, R21, R18
-/
-- MILESTONE (optional: change or delete)
theorem entry_ji {d : ℕ} {i j : Fin d} (hij : i ≠ j) {β₁ β₂ : ℝ} (h₁ : |β₁| < 1) (h₂ : |β₂| < 1) :
    (boost i β₁ h₁ * boost j β₂ h₂).1 (Sum.inr j) (Sum.inr i) = 0 := by
  sorry

/- SKELETON · boost_mul_boost_ne_boost
  0. Prove the milestones first: gamma_ne_zero (step 5), entry_ij and entry_ji (step 4).
  1. The hole is a term (`:= sorry`): replace it by `by` and tactics. Introduce k, β, hβ
     and the equation h : product = boost k β hβ:                                       R22
  2. The symmetry of `boost k β hβ` at entry (Sum.inr i, Sum.inr j), as `e`:           R23, R24
  3. In `e`, replace the boost by the product, then remove the transpose:              R25, R26
  4. Evaluate both sides of `e`:                                rw [entry_ij hij, entry_ji hij] at e
       now e : 0 = γ β₁ * β₁ * (γ β₂ * β₂)
  5. hne : γ β₁ * β₁ * (γ β₂ * β₂) ≠ 0, from gamma_ne_zero, h₁0, h₂0:                  R27
  6. Contradiction:                                                                     R28
-/
-- BEGIN SPEC
theorem boost_mul_boost_ne_boost {d : ℕ} {i j : Fin d} (hij : i ≠ j) {β₁ β₂ : ℝ}
    (h₁ : |β₁| < 1) (h₂ : |β₂| < 1) (h₁0 : β₁ ≠ 0) (h₂0 : β₂ ≠ 0) :
    ∀ (k : Fin d) (β : ℝ) (hβ : |β| < 1), boost i β₁ h₁ * boost j β₂ h₂ ≠ boost k β hβ :=
-- END SPEC
  sorry

end H104

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Suppose the product equals `boost k β hβ`. A boost's matrix equals its transpose (R23), so the
    product's `(Sum.inr i, Sum.inr j)` and `(Sum.inr j, Sum.inr i)` entries would agree. Compute both
    (the milestones `entry_ij`, `entry_ji`): one is `γ β₁ * β₁ * (γ β₂ * β₂) ≠ 0`, the other is `0`.
H2. Each entry: `simp only [lorentzGroupIsGroup_mul_coe, Matrix.mul_apply, Fintype.sum_sum_type]`, then `simp`
    with the named entry lemmas `boost_inr_other_inr`, `boost_inr_other_inl_0`, `boost_inr_self_inr_other`
    (each needs `j ≠ i`; use `Ne.symm hij` for `boost i`). In `entry_ij` a spatial sum is left:
    `apply Finset.sum_eq_zero; intro l _; by_cases hl : l = i`. `gamma_ne_zero`: `0 < 1 - β ^ 2` by
    `rw [abs_lt] at hβ; nlinarith`, then `simp [γ, Real.sqrt_ne_zero', this]`.
H3. Main: `intro k β hβ h`,
    `have e := congrFun (congrFun (boost_transpose_matrix_eq_self k hβ) (Sum.inr i)) (Sum.inr j)`,
    `rw [← h] at e`, `simp only [transpose_apply] at e`, `rw [entry_ij hij, entry_ji hij] at e`. Then
    `hne : γ β₁ * β₁ * (γ β₂ * β₂) ≠ 0` from nested `mul_ne_zero` and `gamma_ne_zero`, and `hne e.symm`.
-/
