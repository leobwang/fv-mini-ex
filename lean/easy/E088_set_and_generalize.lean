/- E088 | set and generalize | 2-3 min | generalize, set, abbreviations, rcases rfl, mathlib
GOAL
  `gen_ex`: replace the compound term `n % 3` by a fresh variable `m` with `m < 3`, then check
  the three values. `set_ex`: practise `set y := x ^ 2 + 1 with hy`, see `h` become `y * 2 = 10`,
  then finish (`linarith` alone would also close it: `set` only renames, for readability).

REFERENCE
  example (n : ℕ) : n % 2 + 1 > 0 := by generalize n % 2 = m; omega  -- every `n % 2` becomes `m`
  -- `generalize e = m at h ⊢` also replaces `e` inside hypothesis `h`
  example (a b : ℕ) (h : (a + b) * (a + b) = 4) : a + b ≤ 2 := by
    set s := a + b with hs; nlinarith        -- h and the goal now say `s`; hs : s = a + b
  #check Nat.mod_lt   -- (x : ℕ) {y : ℕ} : 0 < y → x % y < y
  -- `rcases hm with rfl | rfl` on `hm : m = 0 ∨ m = 1` substitutes each value for `m`
BANNED: simp, simp_all, simpa, simp_rw, rw, rwa, rewrite, erw, nth_rw, nth_rewrite, conv, norm_num, interval_cases, mod_cases, subst, ▸, grind, Nat.mul_mod, exact?, try?
NOTE: `decide` needs a goal without free variables. `set` never changes what is provable: it only renames.
-/
import Mathlib

namespace E088

-- BEGIN SPEC
theorem gen_ex (n : ℕ) : (n % 3) * (n % 3) % 3 ≠ 2 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem set_ex (x : ℝ) (h : (x ^ 2 + 1) * 2 = 10) : x ^ 2 + 1 = 5 :=
-- END SPEC
  sorry

end E088

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `omega` cannot multiply two unknowns, and `n` is unbounded. But `n % 3` takes only 3 values.
H2. Record `n % 3 < 3` as a hypothesis first, `generalize` `n % 3` to `m` in it and in the goal,
    then split `m = 0 ∨ m = 1 ∨ m = 2` (which `omega` proves) with `rfl` patterns and `decide`.
    For `set_ex`: after `set y := x ^ 2 + 1 with hy`, `h` reads `y * 2 = 10` and the goal `y = 5`:
    a linear fact about the new name `y`, so `linarith` finishes.
H3. `have h := Nat.mod_lt n (by omega : 3 > 0)`, `generalize n % 3 = m at h ⊢`,
    `rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | rfl | rfl <;> ...`.
-/
