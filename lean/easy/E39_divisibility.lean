/- E39 | Divisibility | 3 min | Dvd, dvd_add, Dvd.intro, mathlib
GOAL
  Prove divisibility facts from the definition `a ∣ b ↔ ∃ c, b = a * c` and library lemmas.

REFERENCE
  -- `∣` is typed `\mid` (not the keyboard bar).  a ∣ b  unfolds to  ∃ c, b = a * c
  example (a : ℤ) : a ∣ 3 * a := ⟨3, by ring⟩                 -- give the cofactor
  example (a b : ℕ) (h : a ∣ b) : a ∣ 2 * b := by obtain ⟨c, rfl⟩ := h; exact ⟨2 * c, by ring⟩
  #check dvd_add                -- a ∣ b → a ∣ c → a ∣ b + c   (also dvd_sub)
  #check dvd_mul_of_dvd_right   -- a ∣ b → ∀ (c : α), a ∣ c * b
  example : (6 : ℤ) ∣ 42 := by norm_num
BANNED: dvd_trans, Dvd.dvd.trans
-/
import Mathlib

-- BEGIN SPEC
theorem dvd_chain (a b c : ℕ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem dvd_combo (a b c : ℤ) (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ 3 * b - 2 * c :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem dvd_square (a b : ℕ) (h : a ∣ b) : a ^ 2 ∣ b ^ 2 :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Either unpack `h : a ∣ b` as `⟨k, rfl⟩` and give a new cofactor, or combine library lemmas.
H2. `dvd_combo`: a ∣ 3b and a ∣ 2c, then subtract.
H3. Cofactors `k * m` and `k ^ 2` (proofs by `ring`); `dvd_sub (dvd_mul_of_dvd_right h1 3) (dvd_mul_of_dvd_right h2 2)`.
-/
