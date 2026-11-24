/- M127 | Z-rotations and the 2π sign | 10-15 min | Complex.exp, exp_add, push_cast, unitary group, mathlib
GOAL
  The rotation `Rz θ = diag(e^{-iθ/2}, e^{iθ/2})` composes additively (`Rz a · Rz b = Rz (a + b)`),
  a full turn gives the spinor sign `Rz (2π) = -1`, and every `Rz θ` is unitary.

GUIDE
  Entries R1–R21: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Matrix Complex

namespace M127

-- BEGIN SPEC
noncomputable def Rz (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-(θ / 2 : ℂ) * I), 0; 0, Complex.exp ((θ / 2 : ℂ) * I)]
-- END SPEC

/- SKELETON · Rz_add
  1. Unfold `Rz` on both sides, multiply the two diagonal literals, and merge
     each product of exponentials into one exponential (one `simp only`):    R1, R2, R3
  2. Split the cast of the real sum, `↑(a + b)` → `↑a + ↑b`:                 R4
  3. The exponents now agree up to ring arithmetic, and the off-diagonal
     entries are `x * 0 + 0 * y` junk: normalise both sides and close:       R5
-/
-- BEGIN SPEC
theorem Rz_add (a b : ℝ) : Rz a * Rz b = Rz (a + b) :=
-- END SPEC
  by
    simp only [Rz, Matrix.mul_fin_two, ← Complex.exp_add]
    push_cast
    ring_nf

/- SKELETON · Rz_two_pi
  1. Unfold `Rz` (rw [Rz]) and write the `1` in `-1` as a literal:           R1, R6
  2. Push the cast `↑(2 * Real.pi)` → `2 * ↑Real.pi`:                        R4
  3. Prove the two diagonal entries are -1, as `have`s copied from the goal:
       h1 : cexp (-(2 * ↑Real.pi / 2) * I) = -1     proof: R7 → R8 → R9 → norm_num
       h2 : cexp (2 * ↑Real.pi / 2 * I) = -1        proof: R7 → R9
  4. rw [h1, h2]; the goal is now `!![-1, 0; 0, -1] = -!![1, 0; 0, 1]`.
  5. Matrix equation → four entry goals (ext i j, fin_cases), then `simp`:   R10
-/
-- BEGIN SPEC
theorem Rz_two_pi : Rz (2 * Real.pi) = -1 :=
-- END SPEC
  by
    rw [Rz, Matrix.one_fin_two]
    push_cast
    have h1 : Complex.exp (-(2 * ↑Real.pi / 2) * I) = -1 := by
      rw [show -(2 * (Real.pi : ℂ) / 2) * I = -(Real.pi * I) by ring, Complex.exp_neg,
        Complex.exp_pi_mul_I]
      norm_num
    have h2 : Complex.exp ((2 * ↑Real.pi / 2) * I) = -1 := by
      rw [show (2 * (Real.pi : ℂ) / 2) * I = Real.pi * I by ring, Complex.exp_pi_mul_I]
    rw [h1, h2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/- SKELETON · Rz_unitary
  1. Membership → the equation `Rz θ * (Rz θ)ᴴ = 1`:                         R11, R12
  2. Matrix equation → four entry goals (ext i j, fin_cases).
  3. One `simp` per entry. Name `Rz` and R13, R14 (or `simp` stops at
     `v ᵥ* Mᴴ`); R15, R17, R18 are applied by `simp` itself. Also name the
     three it will not find alone:
       move `conj` inside `cexp`                                             R16
       `conj 2` → `2`                                                        R19
       merge the product of exponentials                                     R3
     The merged exponent is `-x + x` or `x + -x`, which `simp` cancels:      R20 → R21
-/
-- BEGIN SPEC
theorem Rz_unitary (θ : ℝ) : Rz θ ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
-- END SPEC
  by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Rz, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_conj, ← Complex.exp_add, map_ofNat]

end M127

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `Rz` is diagonal, so products and conjugate transposes are computed entry by entry, and every
    goal becomes an identity between exponentials. Merge products into one exponential
    (`← Complex.exp_add`) and compare exponents.
H2. `Rz_add`: unfold, `Matrix.mul_fin_two`, `← Complex.exp_add` in one `simp only`, then `push_cast` so
    `↑(a + b)` becomes `↑a + ↑b`, then `ring_nf` makes both sides identical.
    `Rz_two_pi`: `rw [Rz, Matrix.one_fin_two]; push_cast`, prove both diagonal entries equal `-1` as
    `have`s (reshape the exponent to `↑Real.pi * I` or `-(↑Real.pi * I)`), `rw` them, then entry by entry.
    `Rz_unitary`: `rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]`, then entry by entry
    with a `simp` that knows how to push `conj` inside `cexp`.
H3. `Rz_two_pi`: `have h2 : Complex.exp ((2 * ↑Real.pi / 2) * I) = -1 := by
      rw [show (2 * (Real.pi : ℂ) / 2) * I = Real.pi * I by ring, Complex.exp_pi_mul_I]`
    (`h1` is the same with `-(Real.pi * I)` and `Complex.exp_neg` before `Complex.exp_pi_mul_I`, then `norm_num`).
    `Rz_unitary`: the simp set is `[Rz, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_conj,
    ← Complex.exp_add, map_ofNat]`; without `map_ofNat` it stops at `(starRingEnd ℂ) 2`.
-/
