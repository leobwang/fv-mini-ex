/- Guide for E073 (Complex numbers).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other complex numbers).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Complex ComplexConjugate

namespace E073Guide

/-! # Part R · Reference entries -/

/-! ## An equation in `ℂ` → two real equations -/

/-! ### R1. `apply Complex.ext` · goal list: `z = w` → `z.re = w.re` and `z.im = w.im`
A complex number is a structure with two real fields `re` and `im`; equal fields give equal numbers. -/
example (z w : ℂ) (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  apply Complex.ext
  exacts [hre, him]

/-! ## Real and imaginary parts (`simp` and `norm_num` apply these by themselves) -/

/-! ### R2. `Complex.add_re`, `Complex.add_im` · goal: parts of a sum → sum of parts -/
example (z w : ℂ) (P : ℝ → ℝ → Prop) (h : P (z.re + w.re) (z.im + w.im)) :
    P (z + w).re (z + w).im := by
  rw [Complex.add_re, Complex.add_im]
  exact h

/-! ### R3. `Complex.sub_re`, `Complex.sub_im` · goal: parts of a difference → difference of parts -/
example (z w : ℂ) (P : ℝ → ℝ → Prop) (h : P (z.re - w.re) (z.im - w.im)) :
    P (z - w).re (z - w).im := by
  rw [Complex.sub_re, Complex.sub_im]
  exact h

/-! ### R4. `Complex.mul_re`, `Complex.mul_im` · goal: parts of a product → the product formula
`(a + bi)(c + di) = (ac - bd) + (ad + bc)i`. -/
example (z w : ℂ) (P : ℝ → ℝ → Prop)
    (h : P (z.re * w.re - z.im * w.im) (z.re * w.im + z.im * w.re)) :
    P (z * w).re (z * w).im := by
  rw [Complex.mul_re, Complex.mul_im]
  exact h

/-! ### R5. `Complex.I_re`, `I_im`, `re_ofNat`, `im_ofNat` · goal: parts of `I` and of numerals
`I = 0 + 1i`, a numeral `n = n + 0i`. Also `one_re`, `one_im`, `zero_re`, `zero_im` for `1` and `0`. -/
example (P : ℝ → ℝ → ℝ → ℝ → Prop) (h : P 0 1 2 0) : P I.re I.im (2 : ℂ).re (2 : ℂ).im := by
  simp
  exact h

/-! ### R6. `norm_num` · runs `simp`'s lemmas (R2–R5 included), then closes numeric goals -/
example : (1 : ℝ) * 2 - 3 * (-1) = 5 := by
  norm_num

/-! ## Powers of `I` -/

/-! ### R7. `ring_nf` · goal: expand a polynomial expression into normal form, without closing it
`ring_nf` treats `I` as an unknown: it expands `(1 + a) ^ 2` but does not know `a ^ 2` for `a = I`. -/
example (a : ℂ) (P : ℂ → Prop) (h : P (1 + a * 2 + a ^ 2)) : P ((1 + a) ^ 2) := by
  ring_nf
  exact h

/-! ### R8. `Complex.I_sq` · `I ^ 2 = -1` · goal: `I ^ 2` → `-1` -/
example (P : ℂ → Prop) (h : P (-1)) : P (I ^ 2) := by
  rw [Complex.I_sq]
  exact h

/-! ### R9. `ring` · closes an identity of commutative rings (in `ℝ` or `ℂ`, `I` as an unknown) -/
example (a : ℂ) : 1 + a * 2 + -1 = a * 2 := by
  ring

/-! ## Conjugate and real casts -/

/-! ### R10. `Complex.conj_re`, `Complex.conj_im` · goal: parts of `conj z` → `z.re` and `-z.im`
`conj z` (needs `open ComplexConjugate`) is displayed `(starRingEnd ℂ) z`. -/
example (z : ℂ) (P : ℝ → ℝ → Prop) (h : P z.re (-z.im)) : P (conj z).re (conj z).im := by
  rw [Complex.conj_re, Complex.conj_im]
  exact h

/-! ### R11. `Complex.ofReal_re`, `Complex.ofReal_im` · goal: parts of a real cast `↑x` → `x` and `0`
A real `x` used where a complex number is expected is cast to `(x : ℂ)`, displayed `↑x`. -/
example (x : ℝ) (P : ℝ → ℝ → Prop) (h : P x 0) : P (x : ℂ).re (x : ℂ).im := by
  rw [Complex.ofReal_re, Complex.ofReal_im]
  exact h

/-! ## The squared modulus -/

/-! ### R12. `Complex.normSq_apply` · goal: `normSq z` → `z.re * z.re + z.im * z.im` -/
example (z : ℂ) (P : ℝ → Prop) (h : P (z.re * z.re + z.im * z.im)) : P (Complex.normSq z) := by
  rw [Complex.normSq_apply]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A product of literals: `apply Complex.ext <;> simp` (R1, R2–R5) leaves numerals, `norm_num` (R6) closes -/
example : (2 + I) * (2 - I) = 5 := by
  apply Complex.ext <;> simp
  norm_num

/-! ### W2. A square: R7, R8, R9 -/
example : (1 - I) ^ 2 = -2 * I := by
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ### W3. With a variable and a conjugate: `apply Complex.ext <;> simp` (R1; R2–R5, R10, R11), then R9 -/
example (z : ℂ) : z - conj z = 2 * z.im * I := by
  apply Complex.ext <;> simp
  ring

/-! ### W4. A squared modulus: R12, `simp` (R2, R4, R5), then R6 -/
example : Complex.normSq (1 + 2 * I) = 5 := by
  rw [Complex.normSq_apply]
  simp
  norm_num

end E073Guide
