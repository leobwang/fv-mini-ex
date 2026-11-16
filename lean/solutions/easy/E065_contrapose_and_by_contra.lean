/- E065 | contrapose! and by_contra! | 2-3 min | contrapose!, by_contra!, push Not, mathlib
GOAL
  Prove implications by contrapositive (`contrapose!`) and by contradiction (`by_contra!`).
  The `!` pushes negations inward, so `¬ a < b` arrives as `b ≤ a`.

REFERENCE
  example (a : ℕ) (h : ∀ n, n ≤ a → n ≠ 5) : a < 5 := by contrapose! h; exact ⟨5, h, rfl⟩
  example (n : ℕ) (h : n * n < 4) : n < 2 := by by_contra! hn; have := Nat.mul_le_mul hn hn; linarith
  `contrapose! h`: goal `Q` with `h : P` becomes goal `¬P` with `h : ¬Q`, negations pushed inward.
  `by_contra! h`: adds `h : ¬goal` (pushed: `¬ n < 2` becomes `2 ≤ n`), new goal `False`.
  #check lt_irrefl   -- ¬ a < a
BANNED: simp, simp_all, simpa, norm_num, grind, aesop, omega, intro, intros, rintro, fun, λ, ·, mt, absurd, Not.imp, not_imp_not, forall_gt_imp_ge_iff_le_of_dense, le_of_forall_pos_lt_add, le_of_forall_pos_le_add, le_of_forall_lt_imp_le_of_dense, le_of_forall_gt_imp_ge_of_dense, right_ne_zero_of_mul, left_ne_zero_of_mul, ne_of_apply_ne, ne_zero_pow, lt_imp_lt_of_le_imp_le, Monotone.reflect_lt, pow_ne_zero_iff, pow_eq_zero_iff, le_of_forall_lt, le_of_forall_le, forall_lt_iff_le, exact?, apply?, try?
NOTE: `intro`/`fun`/`λ`/`mt` and the `(f · x)` lambda shorthand are banned so you do not build the contrapositive
  by hand (this also bans `·` goal bullets; no proof here needs one). The banned lemmas are library one-liners
  for these exact statements.
-/
import Mathlib

namespace E065

-- BEGIN SPEC
theorem ne_zero_contra (x : ℝ) (h : x ^ 2 ≠ 0) : x ≠ 0 :=
-- END SPEC
  by
    contrapose! h
    rw [h]
    ring

-- BEGIN SPEC
theorem mono_contra (f : ℕ → ℕ) (hf : ∀ a b, a ≤ b → f a ≤ f b) (a b : ℕ) (h : f a < f b) : a < b :=
-- END SPEC
  by
    contrapose! h
    exact hf b a h

-- BEGIN SPEC
theorem le_of_forall_pos (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 :=
-- END SPEC
  by
    by_contra! hx
    have := h (x / 2) (by linarith)
    linarith

-- BEGIN SPEC
theorem le_of_lt_imp (a b : ℕ) (h : ∀ c, c < a → c < b) : a ≤ b :=
-- END SPEC
  by
    by_contra! h'
    exact lt_irrefl b (h b h')

end E065

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The first two have a hypothesis that becomes useful once negated: `contrapose! h`. The last two read best
    by contradiction: `by_contra! h'` and look at what `h'` says.
H2. `ne_zero_contra`: after `contrapose! h` you have `h : x = 0`, goal `x ^ 2 = 0`. `mono_contra`: after
    `contrapose! h` the goal is `f b ≤ f a`, which is `hf` at the right arguments. `le_of_forall_pos`: with
    `0 < x`, use `h` at `x / 2`. `le_of_lt_imp`: with `b < a`, use `h` at `c := b`.
H3. `contrapose! h; rw [h]; ring`; `contrapose! h; exact hf b a h`;
    `by_contra! hx; have := h (x / 2) (by linarith); linarith`.
-/
