/- E065 | contrapose! and by_contra! | 2-3 min | contrapose!, by_contra!, push Not, mathlib
GOAL
  Prove implications by contrapositive (`contrapose!`) and by contradiction (`by_contra!`).
  The `!` pushes negations inward, so `¬ a < b` arrives as `b ≤ a`.
BANNED: simp, simp_all, simpa, norm_num, grind, aesop, omega, intro, intros, rintro, fun, λ, ·, mt, absurd, Not.imp, not_imp_not, forall_gt_imp_ge_iff_le_of_dense, le_of_forall_pos_lt_add, le_of_forall_pos_le_add, le_of_forall_lt_imp_le_of_dense, le_of_forall_gt_imp_ge_of_dense, right_ne_zero_of_mul, left_ne_zero_of_mul, ne_of_apply_ne, ne_zero_pow, lt_imp_lt_of_le_imp_le, Monotone.reflect_lt, pow_ne_zero_iff, pow_eq_zero_iff, le_of_forall_lt, le_of_forall_le, forall_lt_iff_le, exact?, apply?, try?

GUIDE
  Entries R1–R9: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E065

/- SKELETON · ne_zero_contra
  1. Swap hypothesis and goal; the `!` cancels the two `≠`:                       R1
       h : x = 0  ⊢ x ^ 2 = 0
  2. Substitute the equation:                                                     rw [h]
  3. Close the numeric identity left over:                                        R2
-/
-- BEGIN SPEC
theorem ne_zero_contra (x : ℝ) (h : x ^ 2 ≠ 0) : x ≠ 0 :=
-- END SPEC
  by
    contrapose! h
    rw [h]
    ring

/- SKELETON · mono_contra
  1. Swap hypothesis and goal; `¬ (_ < _)` is pushed to `_ ≤ _` with sides swapped: R3
       h : b ≤ a  ⊢ f b ≤ f a
  2. Close it with the monotonicity hypothesis at the right two values:             R4
-/
-- BEGIN SPEC
theorem mono_contra (f : ℕ → ℕ) (hf : ∀ a b, a ≤ b → f a ≤ f b) (a b : ℕ) (h : f a < f b) : a < b :=
-- END SPEC
  by
    contrapose! h
    exact hf b a h

/- SKELETON · le_of_forall_pos
  1. Assume the negated goal, pushed (`¬ (x ≤ 0)` → `0 < x`); goal `False`:        R5
  2. Instantiate `h` at a positive value below `x`, proving positivity in place:   R6, R7
  3. The context is now linearly contradictory:                                   R8
-/
-- BEGIN SPEC
theorem le_of_forall_pos (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 :=
-- END SPEC
  by
    by_contra! hx
    have := h (x / 2) (by linarith)
    linarith

/- SKELETON · le_of_lt_imp
  1. Assume the negated goal, pushed (`¬ (a ≤ b)` → `b < a`); goal `False`:        R5
  2. `h` (shown as `∀ c < a, c < b`) at `c := b` with `h'` gives `b < b`, as in R6
     but written inside the `exact`; close `False` from it:                       R6, R9
-/
-- BEGIN SPEC
theorem le_of_lt_imp (a b : ℕ) (h : ∀ c, c < a → c < b) : a ≤ b :=
-- END SPEC
  by
    by_contra! h'
    exact lt_irrefl b (h b h')

end E065

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The first two have a hypothesis that becomes useful once negated: swap it with the goal (`contrapose! h`).
    The last two read best by contradiction (`by_contra! h'`): look at what `h'` says after the `!` pushed the
    negation.
H2. `ne_zero_contra`: after R1 you have `h : x = 0 ⊢ x ^ 2 = 0`; substitute, then `ring`. `mono_contra`: after
    R3 the goal is `f b ≤ f a`, which is `hf` at the right two values. `le_of_forall_pos`: with `hx : 0 < x`,
    use `h` at `x / 2` and finish with `linarith`. `le_of_lt_imp`: with `h' : b < a`, use `h` at `c := b`.
H3. `contrapose! h; rw [h]; ring`; `contrapose! h; exact hf b a h`;
    `by_contra! hx; have := h (x / 2) (by linarith); linarith`;
    `by_contra! h'`, then `exact lt_irrefl b …` applied to `h` at `b`.
-/
