/- E073 | Complex numbers | 2-3 min | Complex, re, im, I, conj, Complex.ext, normSq, ring_nf, mathlib
GOAL
  Compute in `ℂ`: compare real and imaginary parts, use `I ^ 2 = -1`, and work with the conjugate
  `conj z` (= `z.re - z.im * I`) and `Complex.normSq z` (= `z.re ^ 2 + z.im ^ 2`, the squared modulus).

REFERENCE
  #check Complex.ext           -- z.re = w.re → z.im = w.im → z = w
  #check Complex.I_sq          -- I ^ 2 = -1
  #check Complex.conj_re       -- ((starRingEnd ℂ) z).re = z.re   (`conj z` is displayed `(starRingEnd ℂ) z`)
  #check Complex.normSq_apply  -- normSq z = z.re * z.re + z.im * z.im
  example : (2 + 3 * Complex.I).re = 2 := by simp   -- simp knows `re`/`im` of sums, products, `I`
  `apply Complex.ext <;> simp` splits `z = w` into a `re` goal and an `im` goal and computes both.
  `ring_nf` puts a ring expression in normal form without needing to close the goal; then rewrite
  `I ^ 2` with `I_sq` and finish with `ring`. `↑x` is the real number `x` viewed in ℂ.
BANNED: add_conj
NOTE: `add_conj` (the library's `z + conj z = ↑(2 * z.re)`) is banned so you practise `Complex.ext`.
NOTE: `conj` needs `open ComplexConjugate` (already in the spec); `open Complex` lets you write `I`.
-/
import Mathlib

namespace E073

-- BEGIN SPEC
open Complex ComplexConjugate

theorem mul_conj_lit : (1 + I) * (1 - I) = 2 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem sq_one_add_I : (1 + I) ^ 2 = 2 * I :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem add_conj' (z : ℂ) : z + conj z = 2 * z.re :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem normSq_lit : Complex.normSq (3 + 4 * I) = 25 :=
-- END SPEC
  sorry

end E073

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two complex numbers are equal when their real parts and their imaginary parts are equal.
H2. For `=` goals, `apply Complex.ext <;> simp` and tidy what is left (`norm_num` for numerals, `ring`
    for `z.re + z.re = 2 * z.re`). For `sq_one_add_I`, expand with `ring_nf` first. For `normSq_lit`,
    unfold with `normSq_apply` and let `simp` compute the parts.
H3. `apply Complex.ext <;> norm_num` (norm_num includes simp); `ring_nf; rw [I_sq]; ring`; `apply Complex.ext <;> simp; ring`;
    `rw [Complex.normSq_apply]; simp; norm_num`.
-/
