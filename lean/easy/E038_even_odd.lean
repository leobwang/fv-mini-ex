/- E038 | Even and Odd | 3 min | Even, Odd, obtain rfl, mathlib
GOAL
  Prove parity facts by unpacking the definitions of `Even` and `Odd`.

REFERENCE
  -- Even n ↔ ∃ r, n = r + r        Odd n ↔ ∃ k, n = 2 * k + 1   (definitions)
  example (n : ℕ) (h : Even n) : Even (n + 2) := by
    obtain ⟨r, rfl⟩ := h; exact ⟨r + 1, by ring⟩   -- `rfl` replaces n by r + r everywhere
  example : Odd (7 : ℤ) := ⟨3, by norm_num⟩
  #check even_iff_two_dvd   -- Even a ↔ 2 ∣ a
BANNED: Even.mul_right, Odd.add_odd, Odd.pow, parity_simps
-/
import Mathlib

-- BEGIN SPEC
theorem even_mul_any (m n : ℕ) (h : Even m) : Even (m * n) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem odd_add_odd_even (m n : ℕ) (hm : Odd m) (hn : Odd n) : Even (m + n) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem odd_square (n : ℤ) (h : Odd n) : Odd (n ^ 2) :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unpack each hypothesis with `obtain ⟨k, rfl⟩ := h`, then give a witness.
H2. Find the witness by expanding: (2a+1) + (2b+1) = (a+b+1) + (a+b+1).
H3. Witnesses: `k * n`, `a + b + 1`, `2 * k ^ 2 + 2 * k`; each equation by `ring`.
-/
