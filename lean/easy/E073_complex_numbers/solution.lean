/- E073 | Complex numbers | 2-3 min | Complex, re, im, I, conj, Complex.ext, normSq, ring_nf, mathlib
GOAL
  Compute in `ℂ`: compare real and imaginary parts, use `I ^ 2 = -1`, and work with the conjugate
  `conj z` (= `z.re - z.im * I`) and `Complex.normSq z` (= `z.re ^ 2 + z.im ^ 2`, the squared modulus).
BANNED: add_conj

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E073

/- SKELETON · mul_conj_lit
  1. Equation in `ℂ` → a `re` goal and an `im` goal (run step 2 on both with `<;>`):      R1
  2. Compute the parts of the sum, difference and product, of `1`, `I` and `2`,
     and close the numerals; `norm_num` does all of it in one call:                     R2, R3, R4, R5 → R6
-/
-- BEGIN SPEC
open Complex ComplexConjugate

theorem mul_conj_lit : (1 + I) * (1 - I) = 2 :=
-- END SPEC
  by apply Complex.ext <;> norm_num

/- SKELETON · sq_one_add_I
  1. Expand the square as a polynomial in the unknown `I` (this makes `I ^ 2` appear):  R7
  2. Replace `I ^ 2` by `-1`:                                                            R8
  3. Close the remaining ring identity:                                                  R9
-/
-- BEGIN SPEC
theorem sq_one_add_I : (1 + I) ^ 2 = 2 * I :=
-- END SPEC
  by
    ring_nf
    rw [I_sq]
    ring

/- SKELETON · add_conj'
  1. Equation in `ℂ` → a `re` goal and an `im` goal:                                     R1
  2. On both (`<;>`), one `simp` computes the parts of `z + conj z` and of `2 * ↑z.re`:   R2, R10, R4, R5, R11
     it closes the `im` goal and leaves `z.re + z.re = 2 * z.re`
  3. Close that ring identity:                                                           R9
-/
-- BEGIN SPEC
theorem add_conj' (z : ℂ) : z + conj z = 2 * z.re :=
-- END SPEC
  by
    apply Complex.ext <;> simp
    ring

/- SKELETON · normSq_lit
  1. Unfold `normSq` into real and imaginary parts:                                      R12
  2. Compute the parts of `3 + 4 * I` with `simp`; it leaves `3 * 3 + 4 * 4 = 25`:        R2, R4, R5
  3. Close the numerals:                                                                 R6
-/
-- BEGIN SPEC
theorem normSq_lit : Complex.normSq (3 + 4 * I) = 25 :=
-- END SPEC
  by
    rw [Complex.normSq_apply]
    simp
    norm_num

end E073

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two complex numbers are equal when their real parts and their imaginary parts are equal (R1), and
    `simp`/`norm_num` know the parts of sums, products, `I`, numerals, `conj` and real casts (R2–R5, R10, R11).
    Only `sq_one_add_I` is better done without parts: expand, then use `I ^ 2 = -1` (R7, R8).
H2. `mul_conj_lit`: split with `Complex.ext`, compute both parts down to numerals. `sq_one_add_I`: `ring_nf`,
    rewrite `I ^ 2`, `ring`. `add_conj'`: split, `simp` both parts, `ring` on the `re` goal that is left.
    `normSq_lit`: unfold with `Complex.normSq_apply`, `simp`, `norm_num`.
H3. `apply Complex.ext <;> norm_num`; `ring_nf; rw [Complex.I_sq]; ring`; `apply Complex.ext <;> simp` then
    `ring`; `rw [Complex.normSq_apply]` then `simp` then `norm_num`.
-/
