/- E083 | Bit vectors | 2-3 min | BitVec, literals, wraparound, bitwise ops, bv_omega
GOAL
  Reason about fixed-width machine integers `BitVec w` (w-bit words, arithmetic mod `2 ^ w`): literals,
  wraparound, bitwise operations, and `bv_omega` for linear facts.

REFERENCE
  example : (0xFF#8).toNat = 255 := rfl         -- `n#w` is the w-bit literal n (taken mod 2^w)
  example : 5#4 + 12#4 = 1#4 := by decide       -- + - * wrap around mod 2^w; closed terms: `decide`
  example : (6#8 &&& 3#8) = 2#8 := by decide    -- bitwise and/or/xor: &&&  |||  ^^^
  example : (6#8 >>> 1) = 3#8 := by decide      -- shifts: <<<  >>>
  #check @BitVec.toNat_add    -- (x + y).toNat = (x.toNat + y.toNat) % 2 ^ w
  #check @BitVec.isLt         -- x.toNat < 2 ^ w
  example (x : BitVec 8) (h : x < 5#8) : x.toNat < 5 := by bv_omega   -- translate to ℕ, then omega
    -- `<` / `≤` on BitVec compare unsigned values: `x < y ↔ x.toNat < y.toNat`
  example (x : BitVec 8) : x &&& x = x := by simp   -- simp knows the bitwise identities
BANNED: bv_decide, grind, try?, exact?
NOTE: `bv_omega` handles + - < ≤ = and toNat; it does not understand &&&, |||, ^^^ on variables.
-/

namespace E083

-- BEGIN SPEC
theorem lit_wrap : 0xFF#8 + 1#8 = 0#8 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem shift_lit : 1#8 <<< 3 = 8#8 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem xor_self (x : BitVec 16) : x ^^^ x = 0#16 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem toNat_lt (x : BitVec 8) : x.toNat < 256 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem add_no_overflow (x y : BitVec 8) (h : x.toNat + y.toNat < 256) :
    (x + y).toNat = x.toNat + y.toNat :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem succ_ne_zero (x : BitVec 8) (h : x < 10#8) : x + 1#8 ≠ 0#8 :=
-- END SPEC
  sorry

end E083

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two statements are about literals only; one is a bitwise identity; three are linear facts.
H2. Closed literal facts: `decide`. The xor identity: `simp`. The rest live in `toNat`-land.
H3. `bv_omega` for `toNat_lt`, `add_no_overflow` and `succ_ne_zero` (by hand: `BitVec.isLt x`, and
    `rw [BitVec.toNat_add]; omega`).
-/
