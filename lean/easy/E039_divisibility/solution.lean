/- E039 | Divisibility | 3 min | Dvd, dvd_add, Dvd.intro, mathlib
GOAL
  Prove divisibility facts from the definition `a ∣ b ↔ ∃ c, b = a * c` and library lemmas.

BANNED: dvd_trans, Dvd.dvd.trans

GUIDE
  Entries R1–R6: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

/- SKELETON · dvd_chain
  1. Unpack `h1 : a ∣ b` into a cofactor `k`, substituting `b := a * k`
     (now `h2 : a * k ∣ c`).                                                    R2
  2. Unpack `h2` the same way: cofactor `m`, `c := a * k * m`.                  R2
  3. Goal `a ∣ a * k * m`: name the cofactor (built from `k` and `m`).          R3
  4. Close the remaining equation.                                              R4
-/
-- BEGIN SPEC
theorem dvd_chain (a b c : ℕ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c :=
-- END SPEC
  by
    obtain ⟨k, rfl⟩ := h1
    obtain ⟨m, rfl⟩ := h2
    exact ⟨k * m, by ring⟩

/- SKELETON · dvd_combo
  No unpacking: one term built from two lemmas.
  1. From `h1`: `a ∣ 3 * b`; from `h2`: `a ∣ 2 * c` (two `have`s).            R5
  2. Subtract the two facts (ℤ is a ring): `apply` leaves the goals
     `a ∣ 3 * b`, `a ∣ 2 * c`; close each with its fact from step 1.            R6
     (Or skip the `have`s: pass both R5 terms straight to R6 in one `exact`.)
-/
-- BEGIN SPEC
theorem dvd_combo (a b c : ℤ) (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ 3 * b - 2 * c :=
-- END SPEC
  dvd_sub (dvd_mul_of_dvd_right h1 3) (dvd_mul_of_dvd_right h2 2)

/- SKELETON · dvd_square
  1. Unpack `h : a ∣ b` into a cofactor `k`, substituting `b := a * k`;
     the goal becomes `a ^ 2 ∣ (a * k) ^ 2`.                                    R2
  2. Name the new cofactor (a power of `k`).                                    R3
  3. Close the remaining equation (`ring` expands powers of products).          R4
-/
-- BEGIN SPEC
theorem dvd_square (a b : ℕ) (h : a ∣ b) : a ^ 2 ∣ b ^ 2 :=
-- END SPEC
  by
    obtain ⟨k, rfl⟩ := h
    exact ⟨k ^ 2, by ring⟩

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `a ∣ b` is `∃ c, b = a * c`: unpack a hypothesis with `obtain ⟨k, rfl⟩ := h` and prove a goal by
    giving a cofactor, `⟨k', by ring⟩`. Or skip the unpacking and combine library lemmas.
H2. `dvd_chain`, `dvd_square`: unpack, then cofactor + `ring`. `dvd_combo`: `a ∣ 3 * b` and `a ∣ 2 * c`
    by `dvd_mul_of_dvd_right`, then subtract with `dvd_sub`.
H3. Cofactors `k * m` (chain) and `k ^ 2` (square): `exact ⟨k * m, by ring⟩`.
    `dvd_combo`: `dvd_sub (dvd_mul_of_dvd_right h1 3) (dvd_mul_of_dvd_right h2 2)`.
-/
