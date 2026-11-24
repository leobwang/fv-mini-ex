/- E088 | set and generalize | 2-3 min | generalize, set, abbreviations, rcases rfl, mathlib
GOAL
  `gen_ex`: replace the compound term `n % 3` by a fresh variable `m` with `m < 3`, then check
  the three values. `set_ex`: practise `set y := x ^ 2 + 1 with hy`, see `h` become `y * 2 = 10`,
  then finish (`linarith` alone would also close it: `set` only renames, for readability).

BANNED: simp, simp_all, simpa, simp_rw, rw, rwa, rewrite, erw, nth_rw, nth_rewrite, conv, norm_num, interval_cases, mod_cases, subst, ▸, grind, Nat.mul_mod, exact?, try?

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E088

/- SKELETON · gen_ex
  1. Bound the remainder first, as a hypothesis:                                R1
       h : n % 3 < 3          (the side fact `3 > 0` inline, by omega)
  2. Name the remainder `m`, in `h` AND in the goal (`at h ⊢`):                  R2
       h : m < 3  ⊢  m * m % 3 ≠ 2
  3. Split `m` into its three values, substituting each (`rfl` patterns);
     the disjunction itself comes from `h`:                                     R3 → R4
  4. On every resulting goal (`<;>`): only numerals are left, so compute.        R5
-/
-- BEGIN SPEC
theorem gen_ex (n : ℕ) : (n % 3) * (n % 3) % 3 ≠ 2 :=
-- END SPEC
  by
    have h := Nat.mod_lt n (by omega : 3 > 0)
    generalize n % 3 = m at h ⊢
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | rfl | rfl <;> decide

/- SKELETON · set_ex
  1. Abbreviate `x ^ 2 + 1` as `y`, keeping `hy`:                                R6
       h : y * 2 = 10  ⊢  y = 5
  2. A linear fact about `y`: finish from `h`.                                   R7
-/
-- BEGIN SPEC
theorem set_ex (x : ℝ) (h : (x ^ 2 + 1) * 2 = 10) : x ^ 2 + 1 = 5 :=
-- END SPEC
  by
    set y := x ^ 2 + 1 with hy
    linarith

end E088

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `omega` cannot multiply two unknowns, and `n` is unbounded. But `n % 3` takes only 3 values:
    turn it into a variable you can case-split on. In `set_ex`, look at `h` and the goal after naming
    `x ^ 2 + 1`.
H2. `gen_ex`: record `n % 3 < 3` first (`Nat.mod_lt`), then `generalize` `n % 3` to `m` in that
    hypothesis and in the goal; `omega` proves `m = 0 ∨ m = 1 ∨ m = 2`, `rcases` with `rfl` patterns
    substitutes each value, and `decide` checks each numeral goal.
    `set_ex`: after `set y := x ^ 2 + 1 with hy`, `h` reads `y * 2 = 10` and the goal `y = 5`:
    a linear fact about the new name `y`, so `linarith` finishes.
H3. `have h := Nat.mod_lt n (by omega : 3 > 0)`, `generalize n % 3 = m at h ⊢`,
    `rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | rfl | rfl <;> ...`.
-/
