/- M167 | Edges of the tight-binding band | 15-20 min | IsLeast, IsGreatest, subtypes, QuantaWaveNumber, ℕ division, cos bounds, physlib
GOAL
  A periodic tight-binding chain `T` (`T.N` sites, spacing `T.a > 0`, on-site energy `T.E0`, hopping
  `T.t`) has energies `E(k) = E0 - 2t cos (k a)` for the allowed wavenumbers `k`. For `t ≥ 0`: the band
  bottom `E0 - 2t` is attained (at `k = 0`), and for an even number of sites the band top `E0 + 2t`
  is attained too (at `k = -π/a`).

GUIDE
  Entries R1–R25: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter

namespace M167

/- SKELETON · band_bottom
  1. The witness k = 0 is allowed; prove it first (index n = T.N / 2):
       h0 : (0 : ℝ) ∈ T.QuantaWaveNumber
       the index and its bound `T.N / 2 < T.N`                              R1, R2 → R3
       the wavenumber formula gives 0                                       R4 (or `simp`)
  2. Split IsLeast and give the range witness ⟨0, h0⟩ in one `refine`:      R5, R6
       its energy is E0 - 2t: formula, cos 0 = 1, then `mul_one`             R7, R8, rw [mul_one]
         (one call: `simp [TightBindingChain.energyEigenvalue]`; plain `simp`
          makes no progress, it must be given the definition)
  3. The lower bound: every energy is ≥ E0 - 2t:
       introduce an arbitrary energy                                         R9
       expose the formula                                                    R7
       add `cos (↑k * T.a) ≤ 1`, then close with `0 ≤ T.t`                  R10 → R11
-/
-- BEGIN SPEC
theorem band_bottom (T : TightBindingChain) (ht : 0 ≤ T.t) :
    IsLeast (Set.range T.energyEigenvalue) (T.E0 - 2 * T.t) :=
-- END SPEC
  by
    have h0 : (0 : ℝ) ∈ T.QuantaWaveNumber := by
      refine ⟨⟨T.N / 2, by have := NeZero.pos T.N; omega⟩, ?_⟩
      simp
    refine ⟨⟨⟨0, h0⟩, by simp [TightBindingChain.energyEigenvalue]⟩, ?_⟩
    rintro _ ⟨k, rfl⟩
    unfold TightBindingChain.energyEigenvalue
    have := Real.cos_le_one (k * T.a)
    nlinarith

/- SKELETON · band_top
  1. Unpack the evenness and collect the positivity facts:
       `T.N = m + m`                                                         R12
       `0 < T.a`, and `(0 : ℝ) < m` (from `0 < T.N` in ℕ)                    R13, R2 → R3 → R14
  2. The witness k = -π/a is allowed; prove it first (index n = 0):
       hk : -(Real.pi / T.a) ∈ T.QuantaWaveNumber
       the index ⟨0, _⟩                                                      R1, R2
       facts h2 : `T.N / 2 = m`                                              R3
             hNr : `(T.N : ℝ) = 2 * m`                                       rw [hm], R15, ring
       rewrite in that order (ℕ division first)                              rw [h2, hNr]
       remove the signs, then clear the denominators                         R16 → R17
  3. Split IsGreatest, witness ⟨_, hk⟩:                                     R18, R6
       its energy is E0 + 2t: formula, then the cosine                       R7, R19 → R21 (R20) → R22 → R23 → ring
  4. The upper bound: every energy is ≤ E0 + 2t:                            R24, R7, R25 → R11
-/
-- BEGIN SPEC
theorem band_top (T : TightBindingChain) (ht : 0 ≤ T.t) (hN : Even T.N) :
    IsGreatest (Set.range T.energyEigenvalue) (T.E0 + 2 * T.t) :=
-- END SPEC
  by
    obtain ⟨m, hm⟩ := hN
    have ha := T.a_pos
    have hm0 : (0 : ℝ) < m := by
      have := NeZero.pos T.N
      exact_mod_cast (show 0 < m by omega)
    have hk : -(Real.pi / T.a) ∈ T.QuantaWaveNumber := by
      refine ⟨⟨0, NeZero.pos T.N⟩, ?_⟩
      -- WHY: rewrite the ℕ-division `T.N / 2` before casting `T.N` to ℝ.
      have h2 : T.N / 2 = m := by omega
      have hNr : (T.N : ℝ) = 2 * m := by rw [hm]; push_cast; ring
      rw [h2, hNr]
      simp
      field_simp
    refine ⟨⟨⟨_, hk⟩, ?_⟩, ?_⟩
    · simp only [TightBindingChain.energyEigenvalue]
      rw [neg_mul, div_mul_cancel₀ _ ha.ne', Real.cos_neg, Real.cos_pi]
      ring
    · rintro _ ⟨k, rfl⟩
      unfold TightBindingChain.energyEigenvalue
      have := Real.neg_one_le_cos (k * T.a)
      nlinarith

end M167

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each part: exhibit an allowed `k` with the extreme energy, then bound every `E(k)` using
    `-1 ≤ cos ≤ 1` and `t ≥ 0`. Which site index `n : Fin T.N` gives `k = 0`? Which gives `k = -π/a`?
H2. Prove the membership of the witness first (`have h0 …`/`have hk …`, R1), then
    `refine ⟨⟨⟨_, h0⟩, ?_⟩, ?_⟩` (R5/R18 with R6), and finish the bound with `rintro _ ⟨k, rfl⟩` (R9/R24).
    Bottom: `n = T.N / 2` makes `n - T.N / 2 = 0`. Top: `obtain ⟨m, hm⟩ := hN` (so `T.N = m + m`) and take
    `n = 0`; then `T.N / 2 = m` and `(T.N : ℝ) = 2 * m`, so the wavenumber is `2π/(2am) * (0 - m) = -π/a`.
H3. `have h0 : (0 : ℝ) ∈ T.QuantaWaveNumber := ⟨⟨T.N / 2, by have := NeZero.pos T.N; omega⟩, by simp⟩`,
    then `refine ⟨⟨⟨0, h0⟩, by simp [TightBindingChain.energyEigenvalue]⟩, ?_⟩` and
    `rintro _ ⟨k, rfl⟩; unfold TightBindingChain.energyEigenvalue; have := Real.cos_le_one (k * T.a); nlinarith`.
    Top: in `hk`, `rw [h2, hNr]; simp; field_simp` (with `ha : 0 < T.a` and `(0 : ℝ) < m` in context); the value is
    `rw [neg_mul, div_mul_cancel₀ _ ha.ne', Real.cos_neg, Real.cos_pi]; ring`.
-/
