/- E064 | simp_rw | 2 min | simp_rw, rewriting under binders, mathlib
GOAL
  Rewrite inside binders (`fun n => …`, `∀ n, …`, `∑ i ∈ s, …`), where `rw` cannot reach
  because the term mentions the bound variable.

BANNED: simp, simp_all, simpa, norm_num, ring, ring_nf, abel, abel_nf, noncomm_ring, push_cast, norm_cast, aesop, grind, funext, ext, congr, conv, forall_congr', Finset.sum_congr, Finset.sum_add_distrib, Finset.mul_sum, fun, intro, intros, rintro, constructor, exact?, apply?, try?

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E064

/- SKELETON · fun_rw
  One `simp_rw [r₁, r₂, r₃, r₄]` call; its rules act in this order, all under the `fun n`:
  1. Replace each `f n` using `h`; the body becomes `n + 1 + (n + 1)`:     R1
  2. Fold the two equal halves into a doubling: `2 * (n + 1)`:             R2 (right to left)
  3. Distribute the 2: `2 * n + 2 * 1`:                                     R3
  4. Clean up `2 * 1`; both sides now agree and the goal closes:           R4, R5
-/
-- BEGIN SPEC
theorem fun_rw (f : ℕ → ℕ) (h : ∀ n, f n = n + 1) :
    (fun n => f n + f n) = fun n => 2 * n + 2 :=
-- END SPEC
  sorry

/- SKELETON · forall_rw
  1. Rewrite `0 + n` under the `∀ n` on the left:                          R6
  2. Both sides of the `↔` are now the same; the goal closes:              R5
-/
-- BEGIN SPEC
theorem forall_rw (p : ℕ → Prop) : (∀ n, p (0 + n)) ↔ ∀ n, p n :=
-- END SPEC
  sorry

/- SKELETON · sum_two
  1. Rewrite each summand `2 * i` under the `∑ i ∈ Finset.range n`:        R7 (left to right)
  2. Both sides are now the same sum; the goal closes:                     R5
-/
-- BEGIN SPEC
theorem sum_two (n : ℕ) : ∑ i ∈ Finset.range n, 2 * i = ∑ i ∈ Finset.range n, (i + i) :=
-- END SPEC
  sorry

end E064

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Try `rw [h]` on `fun_rw` and read the error: `n` is bound by the `fun`, and `rw` never fills a
    pattern with a bound variable. `simp_rw` rewrites under binders (R1).
H2. Each theorem is one `simp_rw [...]` call that ends with both sides equal (R5). `fun_rw`: after `h`
    the body is `n + 1 + (n + 1)`; fold it with `two_mul` right to left (R2), then distribute (R3) and
    clean up `2 * 1` (R4). `forall_rw` and `sum_two` need one rule each (R6, R7).
H3. `fun_rw`: `simp_rw [h, ← two_mul, ?, ?]`, where the two holes are the lemmas of R3 and R4.
    `forall_rw`: `simp_rw [zero_add]`. `sum_two`: `simp_rw [two_mul]`.
-/
