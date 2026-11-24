/- E063 | Casts | 2-3 min | push_cast, norm_cast, exact_mod_cast, Nat.cast, mathlib
GOAL
  Move facts between `ℕ` and `ℝ`. `(n : ℝ)`, printed `↑n`, is the cast of `n : ℕ` into ℝ.
  Push casts inward, pull them outward, and transport hypotheses across the cast.

BANNED: simp, simp_all, simpa, norm_num, grind, aesop, gcongr, positivity, bound, exact?, apply?, try?, Nat.cast_sub, Nat.cast_lt, Nat.cast_le, Nat.cast_pos, Nat.cast_pos', Nat.mono_cast, Nat.strictMono_cast

GUIDE
  Entries R1–R6: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E063

/- SKELETON · cast_poly
  1. Push the single cast `↑(n * (n + 1))` down to `↑n`:                          R1
  2. What is left is real-number algebra in the unknown `↑n`:                    R2
-/
-- BEGIN SPEC
theorem cast_poly (n : ℕ) : ((n * (n + 1) : ℕ) : ℝ) = (n : ℝ) ^ 2 + n :=
-- END SPEC
  by push_cast; ring

/- SKELETON · lt_of_real_lt
  1. The goal is `h` with the casts removed: close it in one step.               R3
     (by hand: R4 on `h`; once `h` matches the goal, `norm_cast` closes it itself,
      so nothing follows it)
-/
-- BEGIN SPEC
theorem lt_of_real_lt (m n : ℕ) (h : (m : ℝ) < (n : ℝ)) : m < n :=
-- END SPEC
  by exact_mod_cast h

/- SKELETON · real_le_of_le
  1. The goal is `h` with casts added: close it in one step.                     R5
-/
-- BEGIN SPEC
theorem real_le_of_le (a b : ℕ) (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) :=
-- END SPEC
  by exact_mod_cast h

/- SKELETON · real_sub_of_le
  1. Split `↑(a - b)` into `↑a - ↑b`; this needs `h : b ≤ a`, so hand it over:     R6
  2. `push_cast` does not close the goal it leaves, even when both sides agree:   R2
-/
-- BEGIN SPEC
theorem real_sub_of_le (a b : ℕ) (h : b ≤ a) : ((a - b : ℕ) : ℝ) = (a : ℝ) - (b : ℝ) :=
-- END SPEC
  by push_cast [h]; ring   -- WHY: without `h`, `↑(a - b)` cannot be split (ℕ subtraction truncates)

/- SKELETON · real_pos_of_pos
  1. `(0 : ℝ)` is the cast of `(0 : ℕ)`, so the goal is `h` with casts added:     R5
-/
-- BEGIN SPEC
theorem real_pos_of_pos (n : ℕ) (h : 0 < n) : (0 : ℝ) < n :=
-- END SPEC
  by exact_mod_cast h

end E063

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. For each goal ask: should the casts move inward (`push_cast`, R1/R6), or is the goal a ℕ fact seen
    through the cast (`exact_mod_cast`, R3/R5; `norm_cast`, R4)?
H2. `cast_poly` and `real_sub_of_le`: push the casts down to the variables, then finish the ℝ algebra with
    `ring` (the subtraction one needs `h`, since ℕ subtraction truncates). The three order facts are `h`
    up to casts: `exact_mod_cast` in both directions, the `0` included.
H3. `cast_poly`: `push_cast; ring`. `real_sub_of_le`: `push_cast [h]`, then `ring`.
    `lt_of_real_lt`: `exact_mod_cast h`.
-/
