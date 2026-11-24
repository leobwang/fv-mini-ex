/- H084 | The quantum Fourier transform is unitary | 1-1.5 h | roots of unity, geometric sums, IsPrimitiveRoot, unitary group, mathlib
GOAL
  The N-point QFT matrix `F j k = ω^{jk} / √N`, with `ω = e^{2πi/N}`, is unitary: `F * star F = 1`.
  The heart is root-of-unity orthogonality: `∑ₖ ω^{jk} · conj(ω^{lk}) = N` if `j = l`, else `0`.

BANNED: dft_dft

GUIDE
  Entries R1–R58: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Matrix Complex

namespace H084

-- BEGIN SPEC
/-- the QFT matrix: `F j k = ω^{jk} / √N` with `ω = exp (2πi / N)` -/
noncomputable def qft (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k =>
    (Real.sqrt N : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ) : ℕ) / N)
-- END SPEC

/- SKELETON · exp_eq_zeta_pow   (MILESTONE 1: used in `root_orthogonality` to write every entry as `ζ ^ m`)
  1. Turn the power on the right into one exponential:                    R1 (`rw [← …]`)
       goal: `cexp (2 * ↑Real.pi * I * ↑m / ↑N) = cexp (↑m * (2 * ↑Real.pi * I / ↑N))`
  2. Strip `cexp` from both sides:                                         R2
  3. The two exponents agree as field expressions:                         R3
-/
-- MILESTONE (optional: change or delete)
theorem exp_eq_zeta_pow (N m : ℕ) :
    Complex.exp (2 * Real.pi * I * (m : ℕ) / N) = Complex.exp (2 * Real.pi * I / N) ^ m := by
  sorry

/- SKELETON · conj_zeta   (MILESTONE 2: used in `root_orthogonality` to turn `conj (ζ ^ m)` into `ζ⁻¹ ^ m`)
  1. Move `conj` inside `cexp`; write `(cexp x)⁻¹` as `cexp (-x)`:          R4, R5 (both `rw [← …]`)
  2. Strip `cexp`:                                                         R2
       goal: `(starRingEnd ℂ) (2 * ↑Real.pi * I / ↑N) = -(2 * ↑Real.pi * I / ↑N)`
  3. Push `conj` through `/`, `*`, `2`, `↑Real.pi`, `I`, `↑N` (one `simp [..]`): R6, R7, R8, R9, R10, R11
       goal: `-(2 * ↑Real.pi * I) / ↑N = -(2 * ↑Real.pi * I / ↑N)`
  4. Finish:                                                               R3
-/
-- MILESTONE (optional: change or delete)
theorem conj_zeta (N : ℕ) :
    starRingEnd ℂ (Complex.exp (2 * Real.pi * I / N)) = (Complex.exp (2 * Real.pi * I / N))⁻¹ := by
  sorry

/- SKELETON · root_orthogonality   (MILESTONE 3: used in `qft_unitary`; prove MILESTONES 1 and 2 first)
  1. `hN : N ≠ 0` (the index `j : Fin N` exists):                           R12, R13
  2. Name the root `ζ := Complex.exp (2 * Real.pi * I / N)`:                R14
  3. `hprim : IsPrimitiveRoot ζ N`, then `hne : ζ ≠ 0`:                      R15, R16
  4. Restate MILESTONES 1 and 2 with `ζ` (a `have` each):
       `hpow : ∀ m : ℕ, Complex.exp (2 * Real.pi * I * (m : ℕ) / N) = ζ ^ m`, `hconj : starRingEnd ℂ ζ = ζ⁻¹`
  5. Rewrite under `∑ k` with `hpow`, R18, `hconj` (one `simp only`):         R17, R18
       goal: `∑ x, ζ ^ (↑j * ↑x) * ζ⁻¹ ^ (↑l * ↑x) = if j = l then ↑N else 0`
  6. `hk : ∀ k : Fin N, ζ ^ ((j : ℕ) * k) * ζ⁻¹ ^ ((l : ℕ) * k) = (ζ ^ (j : ℕ) * ζ⁻¹ ^ (l : ℕ)) ^ (k : ℕ)`
       (type the casts as `(j : ℕ)`; the infoview's `↑j` does not elaborate in a `have`):
       proof: `intro k`, R19, R20 (`←`, twice); then rewrite with it under `∑`:   R17
  7. `Fin N` sum → `range N` sum, function `fun k => (ζ ^ (j : ℕ) * ζ⁻¹ ^ (l : ℕ)) ^ k`:   R21
  8. Split the `if`:                                                        R22
     `j = l`:  R23, then `simp` with R26 applied to R25 (it also uses R24, R27–R29)
     `j ≠ l`:  name `r := ζ ^ (j : ℕ) * ζ⁻¹ ^ (l : ℕ)` (R14), then
       a. `hrN : r ^ N = 1`:   `rw [hr]`, R19, R20 (`←` ×2), R24, R30 (×2), R20 (×2), R31; then `simp`
       b. `hr1 : r ≠ 1`:       `intro h1`, R32; `ζ ^ (j : ℕ) = ζ ^ (l : ℕ)` from `h1` by R33 (`hr`, R24), R34;
                               then R37 applied to R35 (bounds: R36)
       c. `rw`:                R38 (with `hr1`), `hrN`, R39, R40
-/
-- MILESTONE (optional: change or delete)
/-- orthogonality of the characters `k ↦ ω^{jk}` -/
theorem root_orthogonality (N : ℕ) (j l : Fin N) :
    ∑ k : Fin N, Complex.exp (2 * Real.pi * I * ((j : ℕ) * (k : ℕ) : ℕ) / N) *
      starRingEnd ℂ (Complex.exp (2 * Real.pi * I * ((l : ℕ) * (k : ℕ) : ℕ) / N)) =
      if j = l then (N : ℂ) else 0 := by
  sorry

/- SKELETON · qft_unitary   (uses MILESTONE 3)
  1. Membership → equation → entries:                                       R41, then `ext j l`
  2. `hN : (N : ℂ) ≠ 0`:                                                     R43 (`.mpr`) with R42
  3. Expand the entry (one `simp only`): R44, R45, unfold `qft`, R46, R47, R48, R49, R9
       goal: `∑ x, (↑√↑N)⁻¹ * cexp (…) * ((↑√↑N)⁻¹ * (starRingEnd ℂ) (cexp (…))) = 1 j l`
  4. Factor out `(√N)⁻¹ ^ 2`:  R50 with middle term
       `(Real.sqrt N : ℂ)⁻¹ ^ 2 * <the left side of MILESTONE 3>` (copy the source text of
       `root_orthogonality`'s sum, so the later `rw [root_orthogonality]` matches it)
     first goal: R51, then R52 and `ring` per summand
  5. Second goal, `rw`: MILESTONE 3, R24, R53 (`←`), R54 (its hypothesis: R55), R56
       goal: `((↑↑N)⁻¹ * if j = l then ↑N else 0) = if j = l then 1 else 0`
  6. R22;  `j = l`: R57, then R58 with `hN`;  `j ≠ l`: `simp`
-/
-- BEGIN SPEC
theorem qft_unitary (N : ℕ) : qft N ∈ Matrix.unitaryGroup (Fin N) ℂ :=
-- END SPEC
  sorry

end H084

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write every entry as a power of the primitive root `ζ = exp (2πi/N)`: `exp (2πi·m/N) = ζ ^ m` and
    `conj ζ = ζ⁻¹` (MILESTONES 1, 2). Then the orthogonality sum (MILESTONE 3) is a geometric sum in
    `r = ζ^j · (ζ⁻¹)^l`, and each entry of `F * star F` is `(1/N)` times that sum.
H2. MILESTONE 3: `N ≠ 0` because `j : Fin N` exists; `set ζ`, restate MILESTONES 1, 2 with `ζ`, rewrite under
    the sum, regroup to `r ^ k`, convert the sum to `range N`, `split_ifs`. If `j = l`, every term is 1. Otherwise
    `r ^ N = 1` (from `ζ ^ N = 1`) and `r ≠ 1` (else `ζ^j = ζ^l`, so `j = l` by `pow_inj`), so `geom_sum_eq`
    gives `0 / (r - 1)`. `qft_unitary`: `rw [Matrix.mem_unitaryGroup_iff]; ext j l`, expand the entry, factor
    `(√N)⁻¹ ^ 2` out with `trans`, then MILESTONE 3 and `(√N)⁻¹ ^ 2 = N⁻¹`.
H3. Key lines: `rw [Fin.sum_univ_eq_sum_range (fun k => (ζ ^ (j : ℕ) * ζ⁻¹ ^ (l : ℕ)) ^ k)]`;
    `r ≠ 1` ends with `exact Fin.ext (hprim.pow_inj j.isLt l.isLt this)`; `conj_zeta` starts with
    `rw [← Complex.exp_conj, ← Complex.exp_neg]; congr 1`. In `qft_unitary`:
    `simp only [Matrix.mul_apply, Matrix.star_apply, qft, Matrix.of_apply, star_mul', RCLike.star_def, map_inv₀, Complex.conj_ofReal]`,
    then after the `trans` step `rw [root_orthogonality, inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg N), Matrix.one_apply]`.
-/
