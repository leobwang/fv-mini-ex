/- E060 | Int division conventions | 2-3 min | Int.ediv, Int.emod, tdiv, toNat, natAbs, omega
GOAL
  Pin down how `Int` `/` and `%` round (remainder always ≥ 0), how C-style `tdiv` differs, what
  `toNat`/`natAbs` do to negatives, and use this to write a weekday function that works for negative days.

GUIDE
  Entries R1–R14: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E060

/- SKELETON · div_floor
  1. Both sides are concrete integers: let the kernel evaluate `Int.ediv`.     R1
-/
-- BEGIN SPEC
theorem div_floor : (-7 : Int) / 2 = -4 :=
-- END SPEC
  by decide

/- SKELETON · mod_nonneg_lit
  1. Concrete integers again: evaluate `Int.emod`.                             R2
-/
-- BEGIN SPEC
theorem mod_nonneg_lit : (-7 : Int) % 2 = 1 :=
-- END SPEC
  by decide

/- SKELETON · tdiv_trunc
  1. Concrete integers: evaluate `Int.tdiv`.                                   R3
-/
-- BEGIN SPEC
theorem tdiv_trunc : (-7 : Int).tdiv 2 = -3 :=
-- END SPEC
  by decide

/- SKELETON · div_by_zero
  1. `x` is a variable, so no `decide`. Rewrite `x / 0`:                       R4
  2. Rewrite `x % 0`:                                                          R5
  3. Close the `0 + x = x` that is left:                                       R6
-/
-- BEGIN SPEC
theorem div_by_zero (x : Int) : x / 0 + x % 0 = x :=
-- END SPEC
  by rw [Int.ediv_zero, Int.emod_zero]; simp

/- SKELETON · toNat_natAbs
  1. Both conjuncts are concrete: evaluate `toNat` and `natAbs` together
     (no need to split the `∧`).                                               R7, R8
-/
-- BEGIN SPEC
theorem toNat_natAbs : (-5 : Int).toNat = 0 ∧ (-5 : Int).natAbs = 5 :=
-- END SPEC
  by decide

/- SKELETON · neg_odd_div_two
  1. Linear in `k`, divided by the literal 2: one decision procedure.          R9
-/
-- BEGIN SPEC
theorem neg_odd_div_two (k : Int) : (-(2 * k + 1)) / 2 = -k - 1 :=
-- END SPEC
  by omega

-- `weekday d`: day `d` counted from a Monday (day 0, negative = in the past); Monday = 0, …, Sunday = 6.
/- SKELETON · weekday (definition body)
  1. Take the remainder of `d` by 7 that lies in 0..6 even for negative `d`:   R2
  2. Turn that non-negative `Int` into a `Nat`, losing nothing:                R7
-/
-- BEGIN SPEC
def weekday (d : Int) : Nat :=
-- END SPEC
  -- WHY: `d % 7` is `Int.emod`, so it is in `0..6` even for negative `d`; `toNat` loses nothing.
  (d % 7).toNat

/- SKELETON · weekday_spec
  1. Expose the body you wrote:                                                R12
  2. Either: add the fact  h : 0 ≤ d % 7  (state its type; `7 ≠ 0`: decide) R10
             and rewrite `↑(d % 7).toNat` to `d % 7` with it:                  R11
     Or:     close the unfolded goal in one step:                              R13
  (Term-mode alternative, no unfold: R11's lemma applied to R10's fact proves
   the goal directly, since Lean unfolds `weekday` when it checks the term.   R10 → R11)
-/
-- BEGIN SPEC
theorem weekday_spec (d : Int) : (weekday d : Int) = d % 7 :=
-- END SPEC
  Int.toNat_of_nonneg (Int.emod_nonneg d (by decide))

/- SKELETON · weekday_neg_one
  1. Evaluate your `weekday` on the literal `-1`:                              R14
-/
-- BEGIN SPEC
theorem weekday_neg_one : weekday (-1) = 6 :=
-- END SPEC
  by decide

end E060

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The literal facts compute: let the kernel evaluate them (R1–R3, R7, R8, R14). `div_by_zero` has a variable,
    so rewrite instead (R4, R5). `weekday` needs the `Int` remainder (always ≥ 0) turned into a `Nat`.
H2. `div_by_zero`: rewrite with `Int.ediv_zero` and `Int.emod_zero`, then `simp`. `neg_odd_div_two` is linear
    arithmetic with `/` by a literal: `omega`. `weekday_spec`: unfold, get `0 ≤ d % 7` from `Int.emod_nonneg`,
    then `Int.toNat_of_nonneg` (or unfold and `omega`).
H3. `weekday d := (d % 7).toNat`; `weekday_spec`: `Int.toNat_of_nonneg (Int.emod_nonneg d (by decide))` (or `by
    unfold weekday; omega`); `weekday_neg_one`: `by decide`; `neg_odd_div_two`: `by omega`.
-/
