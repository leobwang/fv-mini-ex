/- M055 | Primes and products | 10 min | Nat.Prime, Euclid's lemma, divisibility, mathlib
GOAL
  Use Euclid's lemma (`p ∣ m * n → p ∣ m ∨ p ∣ n`) to reason about prime divisors of products
  and squares.
BANNED: Nat.Prime.dvd_of_dvd_pow, Prime.dvd_of_dvd_pow, Nat.Prime.dvd_mul_of_dvd_left

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M055

/- SKELETON · prime_dvd_sq
  1. Write the square in `h` as a product:       h : p ∣ a * a          R1
  2. Euclid's lemma on `h`, then split the `∨`:  two goals, h : p ∣ a   R2 → R3
     (a term works in `rcases`, so this is one line)
  3. Each goal is closed by its new `h`; `<;>` does both at once.
-/
-- BEGIN SPEC
theorem prime_dvd_sq (p a : ℕ) (hp : p.Prime) (h : p ∣ a ^ 2) : p ∣ a :=
-- END SPEC
  sorry

/- SKELETON · prime_sq_dvd_sq
  1. Get `ha : p ∣ a` from `prime_dvd_sq` (Part 1), arguments `p a hp h`:  R4
  2. Write both squares of the goal as products:  ⊢ p * p ∣ a * a       R5 (twice)
  3. Multiply `ha` by itself:                                            R6
-/
-- BEGIN SPEC
theorem prime_sq_dvd_sq (p a : ℕ) (hp : p.Prime) (h : p ∣ a ^ 2) : p ^ 2 ∣ a ^ 2 :=
-- END SPEC
  sorry

/- SKELETON · prime_dvd_three
  1. `h : p ∣ a * b * c` is `p ∣ (a * b) * c`. Euclid's lemma, split:    R2 → R3
       case 1: p ∣ a * b        case 2: p ∣ c
  2. Case 1: Euclid's lemma again, split:                                R2 → R3
       p ∣ a  → first side of `A ∨ B ∨ C`                                R7
       p ∣ b  → second side                                              R7
  3. Case 2: p ∣ c → third side                                          R7
  Focus each case with `·` (TACTIC_STATES.md, "Structure").
-/
-- BEGIN SPEC
theorem prime_dvd_three (p a b c : ℕ) (hp : p.Prime) (h : p ∣ a * b * c) :
    p ∣ a ∨ p ∣ b ∨ p ∣ c :=
-- END SPEC
  sorry

end M055

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Euclid's lemma `hp.dvd_mul` (R2) is about products, so write each square as a product with
    `pow_two` (R1, R5). Part 2 can reuse Part 1; Part 3 is Euclid's lemma twice.
H2. Part 1: rewrite `h`, apply Euclid, split with `rcases`: both cases say `p ∣ a`. Part 2: `p ∣ a`
    from Part 1, both squares to products, then `mul_dvd_mul` (R6). Part 3: `a * b * c` is
    `(a * b) * c`, so split off `c` first, then split `p ∣ a * b`; pick the side with `Or.inl`/`Or.inr`.
H3. Part 1: `rw [pow_two] at h; rcases hp.dvd_mul.mp h with h | h <;> exact h`.
    Part 2: `have ha := prime_dvd_sq p a hp h`, `rw [pow_two, pow_two]`, `exact mul_dvd_mul ha ha`.
    Part 3: `p ∣ b` closes `p ∣ a ∨ p ∣ b ∨ p ∣ c` by `exact Or.inr (Or.inl h)`.
-/
