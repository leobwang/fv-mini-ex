/- E063 | Casts | 2-3 min | push_cast, norm_cast, exact_mod_cast, Nat.cast, mathlib
GOAL
  Move facts between `ℕ` and `ℝ`. `(n : ℝ)`, printed `↑n`, is the cast of `n : ℕ` into ℝ.
  Push casts inward, pull them outward, and transport hypotheses across the cast.

REFERENCE
  example (m n : ℕ) : ((m + n : ℕ) : ℝ) = n + m := by push_cast; ring      -- push ↑ down to the variables
  example (m n : ℕ) (h : m < n) : (m : ℝ) < n := by exact_mod_cast h         -- normalize casts, then `exact`
  example (m n : ℕ) (h : (m : ℝ) + 1 = n) : m + 1 = n := by norm_cast at h   -- pull ↑ out (also `norm_cast` on the goal)
  `push_cast [h]` lets push_cast use the fact `h` while it rewrites.
BANNED: simp, simp_all, simpa, norm_num, grind, aesop, gcongr, positivity, bound, exact?, apply?, try?, Nat.cast_sub, Nat.cast_lt, Nat.cast_le, Nat.cast_pos, Nat.cast_pos', Nat.mono_cast, Nat.strictMono_cast
NOTE: `↑(a - b) = ↑a - ↑b` needs `b ≤ a`: ℕ subtraction truncates at 0 (`2 - 5 = 0`), ℝ subtraction does not.
-/
import Mathlib

namespace E063

-- BEGIN SPEC
theorem cast_poly (n : ℕ) : ((n * (n + 1) : ℕ) : ℝ) = (n : ℝ) ^ 2 + n :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem lt_of_real_lt (m n : ℕ) (h : (m : ℝ) < (n : ℝ)) : m < n :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem real_le_of_le (a b : ℕ) (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem real_sub_of_le (a b : ℕ) (h : b ≤ a) : ((a - b : ℕ) : ℝ) = (a : ℝ) - (b : ℝ) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem real_pos_of_pos (n : ℕ) (h : 0 < n) : (0 : ℝ) < n :=
-- END SPEC
  sorry

end E063

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. For each goal ask: should the casts move inward (`push_cast`), or is this a ℕ fact seen through the cast
    (`exact_mod_cast`, `norm_cast`)?
H2. `cast_poly` and `real_sub_of_le`: push the casts to the variables, then finish the ℝ algebra with `ring`
    (the subtraction one needs `h`). The three order facts are `h` up to casts.
H3. `cast_poly`: `push_cast; ring`. `lt_of_real_lt`: `exact_mod_cast h`.
-/
