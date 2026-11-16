/- H099 | Tight-binding sum rules | 1-1.5 h | roots of unity, geometric sums, Complex.re, cos², physlib
GOAL
  For the periodic tight-binding chain (energies `E(k) = E0 - 2t cos (k a)` at the `N` allowed `k`):
  (1) for `N ≥ 2` the band energies sum to `N E0` (the band is centred on `E0`: `tr H = N E0`);
  (2) for `N ≥ 3` the squared deviations sum to `2 N t²` (`tr (H - E0)² = 2 N t²`).

REFERENCE
  #check Complex.isPrimitiveRoot_exp  -- n ≠ 0 → IsPrimitiveRoot (exp (2 * π * I / n)) n   (`I` = `Complex.I`, `π` = `Real.pi`)
  #check IsPrimitiveRoot.pow_eq_one_iff_dvd  -- IsPrimitiveRoot ζ k → (ζ ^ l = 1 ↔ k ∣ l)
  #check geom_sum_mul               -- (∑ i ∈ range n, x ^ i) * (x - 1) = x ^ n - 1
  #check Fin.sum_univ_eq_sum_range  -- ∑ i : Fin n, f ↑i = ∑ i ∈ range n, f i
  #check Complex.re_sum             -- (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re
  #check Complex.exp_ofReal_mul_I_re  -- (exp (↑x * I)).re = Real.cos x
  #check Complex.exp_nat_mul        -- exp (↑n * x) = exp x ^ n    (and `Complex.exp_add`)
  #check Real.cos_sq                -- cos x ^ 2 = 1 / 2 + cos (2 * x) / 2
  #check TightBindingChain.energyEigenvalue  -- T.energyEigenvalue k = T.E0 - 2 * T.t * Real.cos (k * T.a)
  #check TightBindingChain.a_pos    -- 0 < T.a     (`NeZero.pos T.N : 0 < T.N`)
NOTE: `T.N / 2 : ℕ` rounds down; rule (1) fails for `N = 1`, rule (2) for `N = 2` (`cos² = 1` at both k).
-/
import Physlib.CondensedMatter.TightBindingChain.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

open CondensedMatter

namespace H099

-- BEGIN SPEC
/-- The `n`-th allowed wavenumber `2π/(aN) · (n − ⌊N/2⌋)`, as an element of `T.QuantaWaveNumber`. -/
noncomputable def kOf (T : TightBindingChain) (n : Fin T.N) : T.QuantaWaveNumber :=
  ⟨2 * Real.pi / (T.a * T.N) * ((n : ℝ) - (T.N / 2 : ℕ)), n, rfl⟩
-- END SPEC

-- MILESTONE (optional: change or delete)
/-- Discrete Fourier orthogonality: `∑ₙ cos (2πj/N · (n − m)) = 0` unless `N ∣ j`. -/
theorem sum_cos (N m j : ℕ) (hj : ¬ N ∣ j) :
    ∑ n : Fin N, Real.cos (2 * Real.pi * j / N * ((n : ℝ) - m)) = 0 := by
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp
  have hN0 : N ≠ 0 := hNpos.ne'
  have hω := Complex.isPrimitiveRoot_exp N hN0
  set ζ := Complex.exp (2 * Real.pi * Complex.I / N) ^ j with hζ
  -- ζ is an N-th root of unity different from 1, so its geometric sum vanishes
  have hζ1 : ζ ≠ 1 := fun h => hj ((hω.pow_eq_one_iff_dvd j).mp h)
  have hζN : ζ ^ N = 1 := by rw [hζ, ← pow_mul, mul_comm j N, pow_mul, hω.pow_eq_one, one_pow]
  have hgeom : ∑ n ∈ Finset.range N, ζ ^ n = 0 := by
    have h := geom_sum_mul ζ N
    rw [hζN, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hζ1)
  calc ∑ n : Fin N, Real.cos (2 * Real.pi * j / N * ((n : ℝ) - m))
      = (∑ n : Fin N,
          Complex.exp (((2 * Real.pi * j / N * ((n : ℝ) - m) : ℝ) : ℂ) * Complex.I)).re := by
        rw [Complex.re_sum]
        simp only [Complex.exp_ofReal_mul_I_re]
    _ = (Complex.exp (-(2 * Real.pi * Complex.I * j / N) * m) *
          ∑ n ∈ Finset.range N, ζ ^ n).re := by
        rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range
          (fun n => Complex.exp (-(2 * Real.pi * Complex.I * j / N) * m) * ζ ^ n)]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [hζ, ← pow_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
        congr 1
        push_cast
        ring
    _ = 0 := by rw [hgeom]; simp

-- MILESTONE (optional: change or delete)
theorem ka_eq (T : TightBindingChain) (n : Fin T.N) :
    (kOf T n : ℝ) * T.a = 2 * Real.pi / T.N * ((n : ℝ) - (T.N / 2 : ℕ)) := by
  have ha := T.a_pos.ne'
  simp only [kOf]
  field_simp

-- BEGIN SPEC
theorem band_sum_rule (T : TightBindingChain) (hN : 2 ≤ T.N) :
    ∑ n, T.energyEigenvalue (kOf T n) = T.N * T.E0 :=
-- END SPEC
  by
    have hcos := sum_cos T.N (T.N / 2) 1 (Nat.not_dvd_of_pos_of_lt one_pos (by omega))
    simp only [Nat.cast_one, mul_one] at hcos
    simp only [TightBindingChain.energyEigenvalue, ka_eq, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hcos]
    ring

-- BEGIN SPEC
theorem band_second_moment (T : TightBindingChain) (hN : 3 ≤ T.N) :
    ∑ n, (T.energyEigenvalue (kOf T n) - T.E0) ^ 2 = 2 * T.N * T.t ^ 2 :=
-- END SPEC
  by
    -- WHY: N ∤ 2 needs N ≥ 3; for N = 2 the doubled angles are multiples of 2π
    have hcos := sum_cos T.N (T.N / 2) 2 (Nat.not_dvd_of_pos_of_lt two_pos (by omega))
    have hterm : ∀ n : Fin T.N, (T.energyEigenvalue (kOf T n) - T.E0) ^ 2 =
        2 * T.t ^ 2 + 2 * T.t ^ 2 *
          Real.cos (2 * Real.pi * (2 : ℕ) / T.N * ((n : ℝ) - (T.N / 2 : ℕ))) := by
      intro n
      simp only [TightBindingChain.energyEigenvalue, ka_eq]
      rw [show (T.E0 - 2 * T.t * Real.cos (2 * Real.pi / T.N * ((n : ℝ) - (T.N / 2 : ℕ))) - T.E0) ^ 2
          = 4 * T.t ^ 2 * Real.cos (2 * Real.pi / T.N * ((n : ℝ) - (T.N / 2 : ℕ))) ^ 2 by ring,
        Real.cos_sq]
      push_cast
      ring_nf
    simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, hcos, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

end H099

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. With `θₙ = k a = 2π/N · (n − m)` (`m = ⌊N/2⌋`), both rules reduce to `∑ₙ cos (j θₙ) = 0` for
    `j = 1` and `j = 2`; for (2) first use `cos² x = 1/2 + cos (2x)/2`.
H2. `cos (j θₙ)` is the real part of `exp (i j θₙ) = exp (-2πi j m / N) · ζⁿ` with `ζ = ωʲ`,
    `ω = exp (2πi/N)` a primitive `N`-th root of unity. `ζ ≠ 1` (because `¬ N ∣ j`) and `ζᴺ = 1`, so
    `(∑ₙ ζⁿ) (ζ - 1) = ζᴺ - 1 = 0` forces `∑ₙ ζⁿ = 0`.
H3. In `sum_cos`, aim for `(exp (-(2π I j / N) * m) * ∑ n ∈ range N, ζ ^ n).re` (the REFERENCE
    lemmas get you there). Main theorems: unfold `energyEigenvalue`, rewrite with `ka_eq`, split the
    sum, and feed in `sum_cos T.N (T.N / 2) 1 (Nat.not_dvd_of_pos_of_lt one_pos (by omega))`; for (2)
    rewrite each term as `2t² + 2t² cos (2·2π/N · x)`.
-/
