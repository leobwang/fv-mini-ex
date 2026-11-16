/- E060 | Int division conventions | 2-3 min | Int.ediv, Int.emod, tdiv, toNat, natAbs, omega
GOAL
  Pin down how `Int` `/` and `%` round (remainder always ≥ 0), how C-style `tdiv` differs, what
  `toNat`/`natAbs` do to negatives, and use this to write a weekday function that works for negative days.

REFERENCE
  example : (-9 : Int) / 4 = -3 ∧ (-9 : Int) % 4 = 3 := by decide   -- `/` = `Int.ediv` (rounds down), `%` = `Int.emod`
  example : (-9 : Int).tdiv 4 = -2 ∧ (-9 : Int).tmod 4 = -1 := by decide   -- truncation toward 0, like C/Rust
  example : (-2 : Int).toNat = 0 := rfl       -- `toNat` clamps negatives to 0; `natAbs` is |x| as a Nat
  #check Int.ediv_zero          -- (a : Int) : a / 0 = 0      (`Int.emod_zero`: a % 0 = a)
  #check Int.emod_nonneg        -- (a : Int) : b ≠ 0 → 0 ≤ a % b    (`Int.emod_lt_of_pos`: 0 < b → a % b < b)
  #check @Int.toNat_of_nonneg   -- 0 ≤ a → (a.toNat : Int) = a
  example (x : Int) : 0 ≤ x % 3 ∧ x % 3 < 3 := by omega   -- omega knows `/`, `%` by literals, `toNat`
NOTE: `((d : Nat) : Int)` coerces back to `Int`; write the cast to compare a `Nat` result with an `Int`.
-/

namespace E060

-- BEGIN SPEC
theorem div_floor : (-7 : Int) / 2 = -4 :=
-- END SPEC
  by decide

-- BEGIN SPEC
theorem mod_nonneg_lit : (-7 : Int) % 2 = 1 :=
-- END SPEC
  by decide

-- BEGIN SPEC
theorem tdiv_trunc : (-7 : Int).tdiv 2 = -3 :=
-- END SPEC
  by decide

-- BEGIN SPEC
theorem div_by_zero (x : Int) : x / 0 + x % 0 = x :=
-- END SPEC
  by rw [Int.ediv_zero, Int.emod_zero]; simp

-- BEGIN SPEC
theorem toNat_natAbs : (-5 : Int).toNat = 0 ∧ (-5 : Int).natAbs = 5 :=
-- END SPEC
  by decide

-- BEGIN SPEC
theorem neg_odd_div_two (k : Int) : (-(2 * k + 1)) / 2 = -k - 1 :=
-- END SPEC
  by omega

-- `weekday d`: day `d` counted from a Monday (day 0, negative = in the past); Monday = 0, …, Sunday = 6.
-- BEGIN SPEC
def weekday (d : Int) : Nat :=
-- END SPEC
  -- WHY: `d % 7` is `Int.emod`, so it is in `0..6` even for negative `d`; `toNat` loses nothing.
  (d % 7).toNat

-- BEGIN SPEC
theorem weekday_spec (d : Int) : (weekday d : Int) = d % 7 :=
-- END SPEC
  Int.toNat_of_nonneg (Int.emod_nonneg d (by decide))

-- BEGIN SPEC
theorem weekday_neg_one : weekday (-1) = 6 :=
-- END SPEC
  by decide

end E060

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The literal facts compute: let the kernel evaluate them. `weekday` needs an `Int` remainder turned into a `Nat`.
H2. Because `d % 7` is never negative in Lean, turning it into a `Nat` loses nothing. `div_by_zero`: rewrite
    with the two by-zero lemmas, then `simp`. `neg_odd_div_two` is linear arithmetic with `/` by a literal.
H3. `weekday d := (d % 7).toNat`; `weekday_spec`: `Int.toNat_of_nonneg (Int.emod_nonneg d (by decide))` (or `by
    unfold weekday; omega`); `weekday_neg_one`: `by decide`;
    `neg_odd_div_two`: `by omega`.
-/
