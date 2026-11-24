/- E083 | Bit vectors | 2-3 min | BitVec, literals, wraparound, bitwise ops, bv_omega
GOAL
  Reason about fixed-width machine integers `BitVec w` (w-bit words, arithmetic mod `2 ^ w`): literals,
  wraparound, bitwise operations, and `bv_omega` for linear facts.

BANNED: bv_decide, grind, try?, exact?

GUIDE
  Entries R1–R11: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E083

/- SKELETON · lit_wrap
  1. Only literals: `0xFF#8` is 255, and `+` wraps mod 2 ^ 8. Evaluate,
     do not prove:                                                      R1, R2
-/
-- BEGIN SPEC
theorem lit_wrap : 0xFF#8 + 1#8 = 0#8 :=
-- END SPEC
  sorry

/- SKELETON · shift_lit
  1. Only literals again: a shift of a literal is a computation:        R3
-/
-- BEGIN SPEC
theorem shift_lit : 1#8 <<< 3 = 8#8 :=
-- END SPEC
  sorry

/- SKELETON · xor_self
  `x` is a variable, so `decide` cannot evaluate this.
  1. A known bitwise identity: close it with the simplifier, which
     knows the library lemma (or rewrite with it yourself):            R5 (uses R4)
-/
-- BEGIN SPEC
theorem xor_self (x : BitVec 16) : x ^^^ x = 0#16 :=
-- END SPEC
  sorry

/- SKELETON · toNat_lt
  1. A linear fact about `BitVec`: close it in one step:                R11
  By hand instead: add the built-in bound `x.toNat < 2 ^ 8`, then close
  the `Nat` goal (`2 ^ 8` is the numeral 256 to it):                    R6 → R10
-/
-- BEGIN SPEC
theorem toNat_lt (x : BitVec 8) : x.toNat < 256 :=
-- END SPEC
  sorry

/- SKELETON · add_no_overflow
  1. A linear fact about `BitVec`: close it in one step:                R11
  By hand instead: turn `(x + y).toNat` into a `Nat` sum mod 2 ^ 8,
  then drop the `%` using `h`:                                          R7 → R10
-/
-- BEGIN SPEC
theorem add_no_overflow (x y : BitVec 8) (h : x.toNat + y.toNat < 256) :
    (x + y).toNat = x.toNat + y.toNat :=
-- END SPEC
  sorry

/- SKELETON · succ_ne_zero
  1. `<` and `≠` on `BitVec` with literals: the translation to `.toNat`
     (R8, R7, R9) and the final `omega` (R10) are what one tactic does:   R11
-/
-- BEGIN SPEC
theorem succ_ne_zero (x : BitVec 8) (h : x < 10#8) : x + 1#8 ≠ 0#8 :=
-- END SPEC
  sorry

end E083

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two statements are about literals only (evaluate them); one is a bitwise identity on a variable;
    three are linear facts once every `BitVec` is read through `.toNat`.
H2. `lit_wrap`, `shift_lit`: `decide` (R1–R3). `xor_self`: `simp` (R5, which knows `BitVec.xor_self`).
    The last three: `bv_omega` (R11), which turns `<`, `+`, `≠` and literals into `.toNat` facts and
    runs `omega`.
H3. `bv_omega` for `toNat_lt`, `add_no_overflow` and `succ_ne_zero`. By hand:
    `have h := x.isLt; omega` (R6, R10) and `rw [BitVec.toNat_add]; omega` (R7, R10).
-/
