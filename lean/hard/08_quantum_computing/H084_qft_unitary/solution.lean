/- H084 | The quantum Fourier transform is unitary | 1-1.5 h | roots of unity, geometric sums, IsPrimitiveRoot, unitary group, mathlib
GOAL
  The N-point QFT matrix `F j k = ω^{jk} / √N`, with `ω = e^{2πi/N}`, is unitary: `F * star F = 1`.
  The heart is root-of-unity orthogonality: `∑ₖ ω^{jk} · conj(ω^{lk}) = N` if `j = l`, else `0`.

REFERENCE
  -- `starRingEnd ℂ z` = complex conjugate of z;  `star M` = conjugate transpose (`Matrix.star_apply`: star M i j = star (M j i))
  #check Matrix.mem_unitaryGroup_iff  -- A ∈ unitaryGroup n α ↔ A * star A = 1
  #check Complex.isPrimitiveRoot_exp  -- (n : ℕ) (h0 : n ≠ 0) : IsPrimitiveRoot (exp (2 * π * I / n)) n
  #check IsPrimitiveRoot.pow_eq_one   -- (h : IsPrimitiveRoot ζ k) : ζ ^ k = 1     (also `h.ne_zero : k ≠ 0 → ζ ≠ 0`)
  #check IsPrimitiveRoot.pow_inj      -- (h : IsPrimitiveRoot ζ k) (hi : i < k) (hj : j < k) : ζ ^ i = ζ ^ j → i = j
  #check Complex.exp_nat_mul          -- exp (n * x) = exp x ^ n
  #check Complex.exp_conj             -- exp (conj x) = conj (exp x)      (and `Complex.exp_neg`: exp (-x) = (exp x)⁻¹)
  #check geom_sum_eq                  -- x ≠ 1 → ∑ i ∈ range n, x ^ i = (x ^ n - 1) / (x - 1)
  #check Fin.sum_univ_eq_sum_range    -- (f : ℕ → α) (n : ℕ) : ∑ i : Fin n, f ↑i = ∑ i ∈ range n, f i
  example (N : ℕ) : ((Real.sqrt N : ℂ)⁻¹) ^ 2 = (N : ℂ)⁻¹ := by rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg N)]; push_cast; rfl
  -- `set ζ := Complex.exp (2 * Real.pi * I / N) with hζ` names the root;  `ext j l` proves a matrix equality entrywise
BANNED: dft_dft
NOTE: Mathlib's `ZMod.dft` (notation `𝓕`) acts on `ZMod N → E`, not on this matrix; tying it to this statement
  is the same work as the direct proof. Only `dft_dft` is banned.
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

-- MILESTONE (optional: change or delete)
theorem exp_eq_zeta_pow (N m : ℕ) :
    Complex.exp (2 * Real.pi * I * (m : ℕ) / N) = Complex.exp (2 * Real.pi * I / N) ^ m := by
  rw [← Complex.exp_nat_mul]; congr 1; ring

-- MILESTONE (optional: change or delete)
theorem conj_zeta (N : ℕ) :
    starRingEnd ℂ (Complex.exp (2 * Real.pi * I / N)) = (Complex.exp (2 * Real.pi * I / N))⁻¹ := by
  rw [← Complex.exp_conj, ← Complex.exp_neg]; congr 1
  simp [Complex.conj_ofReal, map_div₀, map_ofNat]; ring

-- MILESTONE (optional: change or delete)
/-- orthogonality of the characters `k ↦ ω^{jk}` -/
theorem root_orthogonality (N : ℕ) (j l : Fin N) :
    ∑ k : Fin N, Complex.exp (2 * Real.pi * I * ((j : ℕ) * (k : ℕ) : ℕ) / N) *
      starRingEnd ℂ (Complex.exp (2 * Real.pi * I * ((l : ℕ) * (k : ℕ) : ℕ) / N)) =
      if j = l then (N : ℂ) else 0 := by
  have hN : N ≠ 0 := by rintro rfl; exact j.elim0
  set ζ := Complex.exp (2 * Real.pi * I / N) with hζ
  have hprim : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hN
  have hne : ζ ≠ 0 := hprim.ne_zero hN
  -- WHY: after `set`, the milestones no longer match syntactically; restate them with `ζ`
  have hpow : ∀ m : ℕ, Complex.exp (2 * Real.pi * I * (m : ℕ) / N) = ζ ^ m := exp_eq_zeta_pow N
  have hconj : starRingEnd ℂ ζ = ζ⁻¹ := conj_zeta N
  simp only [hpow, map_pow, hconj]
  have hk : ∀ k : Fin N, ζ ^ ((j : ℕ) * k) * ζ⁻¹ ^ ((l : ℕ) * k) = (ζ ^ (j : ℕ) * ζ⁻¹ ^ (l : ℕ)) ^ (k : ℕ) := by
    intro k; rw [mul_pow, ← pow_mul, ← pow_mul]
  simp only [hk]
  rw [Fin.sum_univ_eq_sum_range (fun k => (ζ ^ (j : ℕ) * ζ⁻¹ ^ (l : ℕ)) ^ k)]
  split_ifs with h
  · subst h
    simp [mul_inv_cancel₀ (pow_ne_zero _ hne)]
  · set r := ζ ^ (j : ℕ) * ζ⁻¹ ^ (l : ℕ) with hr
    have hrN : r ^ N = 1 := by
      rw [hr, mul_pow, ← pow_mul, ← pow_mul, inv_pow, mul_comm (j : ℕ) N, mul_comm (l : ℕ) N,
        pow_mul, pow_mul, hprim.pow_eq_one]
      simp
    have hr1 : r ≠ 1 := by
      intro h1
      apply h
      have : ζ ^ (j : ℕ) = ζ ^ (l : ℕ) := by
        rw [hr, inv_pow] at h1; exact (mul_inv_eq_one₀ (pow_ne_zero _ hne)).mp h1
      exact Fin.ext (hprim.pow_inj j.isLt l.isLt this)
    rw [geom_sum_eq hr1, hrN, sub_self, zero_div]

-- BEGIN SPEC
theorem qft_unitary (N : ℕ) : qft N ∈ Matrix.unitaryGroup (Fin N) ℂ :=
-- END SPEC
  by
    rw [Matrix.mem_unitaryGroup_iff]
    ext j l
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.pos j).ne'
    simp only [Matrix.mul_apply, Matrix.star_apply, qft, Matrix.of_apply, star_mul', RCLike.star_def,
      map_inv₀, Complex.conj_ofReal]
    trans ((Real.sqrt N : ℂ)⁻¹ ^ 2 * ∑ k : Fin N,
        Complex.exp (2 * Real.pi * I * ((j : ℕ) * (k : ℕ) : ℕ) / N) *
          starRingEnd ℂ (Complex.exp (2 * Real.pi * I * ((l : ℕ) * (k : ℕ) : ℕ) / N)))
    · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [root_orthogonality, inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg N),
      Matrix.one_apply]
    split_ifs
    · push_cast; exact inv_mul_cancel₀ hN
    · simp

end H084

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write every entry as a power of the primitive root `ζ = exp (2πi/N)`; then `conj ζ = ζ⁻¹` and the orthogonality sum is a geometric sum in `r = ζ^j · (ζ⁻¹)^l`.
H2. In `root_orthogonality`: `N ≠ 0` because `j : Fin N` exists. If `j = l`, every term is 1. Otherwise `r ^ N = 1` (from `ζ ^ N = 1`), and `r ≠ 1` (else `ζ^j = ζ^l`, so `j = l` by `pow_inj`), so `geom_sum_eq` gives `0 / (r - 1)`. For `qft_unitary`: `rw [Matrix.mem_unitaryGroup_iff]; ext j l`, pull out `(√N)⁻¹ · conj (√N)⁻¹ = 1/N`, apply milestone 3.
H3. Regroup with `ζ ^ (j * k) * ζ⁻¹ ^ (l * k) = (ζ ^ j * ζ⁻¹ ^ l) ^ k` (`mul_pow`, `pow_mul`), then `rw [Fin.sum_univ_eq_sum_range (fun k => (ζ ^ (j : ℕ) * ζ⁻¹ ^ (l : ℕ)) ^ k)]`. `conj_zeta`: `rw [← Complex.exp_conj, ← Complex.exp_neg]; congr 1`, then `simp [map_div₀, map_ofNat]` and `ring`.
-/
