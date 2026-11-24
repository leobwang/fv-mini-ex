/- H099 | Tight-binding sum rules | 1-1.5 h | roots of unity, geometric sums, Complex.re, cos², physlib
GOAL
  For the periodic tight-binding chain (energies `E(k) = E0 - 2t cos (k a)` at the `N` allowed `k`):
  (1) for `N ≥ 2` the band energies sum to `N E0` (the band is centred on `E0`: `tr H = N E0`);
  (2) for `N ≥ 3` the squared deviations sum to `2 N t²` (`tr (H - E0)² = 2 N t²`).

GUIDE
  Entries R1–R40: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · sum_cos   (milestone 1: prove it first; band_sum_rule uses it with j = 1,
                        band_second_moment with j = 2)
  1. Split off `N = 0` (an empty sum; `simp` closes it):                           R1, R2
  2. Name three facts, in this order:
       hN0 : N ≠ 0                                                                 R3
       hω  : IsPrimitiveRoot (Complex.exp (2 * ↑Real.pi * Complex.I / ↑N)) N       R4
       ζ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑N) ^ j   (with hζ)            R5
  3. hζ1 : ζ ≠ 1   (otherwise `N ∣ j`, against `hj`):                              R6
     hζN : ζ ^ N = 1   by one `rw`: hζ, then                                       R7 (←), R8, R7, R9, R10
  4. hgeom : ∑ n ∈ Finset.range N, ζ ^ n = 0
       the geometric-sum identity, then `rw [hζN, sub_self] at h`:                 R11, R12
       "a product is 0 and its second factor is not":                              R13, R14, R15
  5. A three-step `calc`:
       ∑ cos (…) = (∑ n : Fin N, Complex.exp (↑(…) * Complex.I)).re               R16, R17
       _ = (Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑j / ↑N) * ↑m) *
              ∑ n ∈ Finset.range N, ζ ^ n).re
             factor in, back to a `Fin` sum, strip `.re`, go under `∑`:           R18, R19 (←), R20, R21
             one term: rw [hζ], then R7 (←), R22 (←), R23 (←); R20; R24; `ring`
       _ = 0                                                                       rw [hgeom], R25
-/
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

/- SKELETON · ka_eq   (milestone 2: both main theorems rewrite `↑(kOf T n) * T.a` with it)
  1. ha : T.a ≠ 0                                                                  R26 (with R3)
  2. Unfold `kOf`; the value `↑⟨x, …⟩` of the subtype element becomes `x`:         R27
  3. Cancel `T.a` (and close):                                                     R28
-/
-- MILESTONE (optional: change or delete)
theorem ka_eq (T : TightBindingChain) (n : Fin T.N) :
    (kOf T n : ℝ) * T.a = 2 * Real.pi / T.N * ((n : ℝ) - (T.N / 2 : ℕ)) := by
  have ha := T.a_pos.ne'
  simp only [kOf]
  field_simp

/- SKELETON · band_sum_rule   (uses milestones sum_cos and ka_eq)
  1. hcos := sum_cos T.N (T.N / 2) 1 (proof of ¬ T.N ∣ 1, from hN : 2 ≤ T.N):      R29 (`one_pos`, `omega`)
     then clean `↑1` and `* 1` out of hcos:                                         R30
  2. One `simp only [...]` whose lemmas do, in this order:
       unfold the energy; `ka_eq` under `∑`                                         R31, R32
       split `∑ (E0 - 2t cos)`; `∑ E0` → `↑T.N * E0`                                R33, R34, R35, R36
       pull `2 * T.t` out of the `∑`, then `hcos`                                   R18 (←), R32
  3. Close the algebra: `ring`
-/
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

/- SKELETON · band_second_moment   (uses milestones sum_cos and ka_eq)
  1. hcos := sum_cos T.N (T.N / 2) 2 (…)   (`¬ T.N ∣ 2` needs `3 ≤ T.N`):          R29 (`two_pos`, `omega`)
  2. Prove each term first (keep the cast `(2 : ℕ)`, so the angle matches hcos):
       hterm : ∀ n : Fin T.N, (T.energyEigenvalue (kOf T n) - T.E0) ^ 2 =
         2 * T.t ^ 2 + 2 * T.t ^ 2 *
           Real.cos (2 * Real.pi * (2 : ℕ) / T.N * ((n : ℝ) - (T.N / 2 : ℕ)))
     proof: `intro n`; unfold the energy, `ka_eq`                                  R31, R32
            `(E0 - 2t c - E0)² = 4t² c²` on the spot, then cos²                     R37, R38
            casts, then normalise inside `Real.cos`                                 R24, R39
  3. One `simp only [...]`: hterm under `∑`, split, pull `2 * T.t ^ 2` out, hcos, count:
                                                                    R32, R40, R18 (←), R34, R35, R36
  4. `ring`
-/
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
H1. With `θₙ = k a = 2π/N · (n − m)` (`m = ⌊N/2⌋`, milestone `ka_eq`), both rules reduce to
    `∑ₙ cos (j θₙ) = 0` (milestone `sum_cos`) for `j = 1` and `j = 2`; for (2) first use
    `cos² x = 1/2 + cos (2x)/2` (R38).
H2. `cos (j θₙ)` is the real part (R16, R17) of `exp (i j θₙ) = exp (-2πi j m / N) · ζⁿ` with
    `ζ = ωʲ`, `ω = exp (2πi/N)` a primitive `N`-th root of unity (R4). `ζ ≠ 1` because `¬ N ∣ j`
    (R6), and `ζᴺ = 1`, so `(∑ₙ ζⁿ) (ζ - 1) = ζᴺ - 1 = 0` (R11) forces `∑ₙ ζⁿ = 0` (R13–R15).
    Main theorems: unfold the energy, rewrite with `ka_eq`, split the sum, plug in `sum_cos`.
H3. In `sum_cos`, aim for `(exp (-(2π I j / N) * m) * ∑ n ∈ range N, ζ ^ n).re` (skeleton step 5).
    Main theorems: `sum_cos T.N (T.N / 2) 1 (Nat.not_dvd_of_pos_of_lt one_pos (by omega))`, then one
    `simp only` with `TightBindingChain.energyEigenvalue, ka_eq`, the sum lemmas R33–R36,
    `← Finset.mul_sum` and `hcos`, then `ring`; for (2) first rewrite each term as
    `2t² + 2t² cos (2·2π/N · x)` (`hterm` in the skeleton).
-/
