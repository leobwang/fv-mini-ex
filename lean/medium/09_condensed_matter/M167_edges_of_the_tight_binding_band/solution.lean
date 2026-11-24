/- M167 | Edges of the tight-binding band | 15-20 min | IsLeast, IsGreatest, subtypes, QuantaWaveNumber, ℕ division, cos bounds, physlib
GOAL
  A periodic tight-binding chain `T` (`T.N` sites, spacing `T.a > 0`, on-site energy `T.E0`, hopping
  `T.t`) has energies `E(k) = E0 - 2t cos (k a)` for the allowed wavenumbers `k`. For `t ≥ 0`: the band
  bottom `E0 - 2t` is attained (at `k = 0`), and for an even number of sites the band top `E0 + 2t`
  is attained too (at `k = -π/a`).

REFERENCE
  #check TightBindingChain.energyEigenvalue  -- T.energyEigenvalue k = T.E0 - 2 * T.t * Real.cos (k * T.a)
  example (T : TightBindingChain) (x : ℝ) : x ∈ T.QuantaWaveNumber ↔ ∃ n : Fin T.N, 2 * Real.pi / (T.a * T.N) * ((n : ℝ) - (T.N / 2 : ℕ)) = x := Iff.rfl
  -- `k : T.QuantaWaveNumber` is a subtype element `⟨x, hx⟩`; build one with `⟨x, ⟨n, proof⟩⟩`
  #check NeZero.pos                 -- `NeZero.pos T.N : 0 < T.N` (physlib provides `NeZero T.N`)
  #check TightBindingChain.a_pos    -- 0 < T.a
  #check Real.cos_le_one  -- cos x ≤ 1;  also Real.neg_one_le_cos, Real.cos_pi : cos π = -1, Real.cos_neg
  #check div_mul_cancel₀  -- b ≠ 0 → a / b * b = a
  example (m : ℕ) : ((m + m : ℕ) : ℝ) = 2 * m := by push_cast; ring   -- `push_cast` moves `↑` inward
  example (N m : ℕ) (h : N = m + m) : N / 2 = m := by omega   -- `/` on ℕ rounds down
  example (s : Set ℝ) (a : ℝ) : IsGreatest s a ↔ a ∈ s ∧ ∀ x ∈ s, x ≤ a := Iff.rfl  -- IsLeast: `a ≤ x`
NOTE: `field_simp` needs nonzero facts in context: `T.a ≠ 0`, and after `obtain ⟨m, hm⟩ := hN`, `(m : ℝ) ≠ 0`.
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter

namespace M167

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
H2. Bottom: `n = T.N / 2` makes `n - T.N / 2 = 0`. Top: `obtain ⟨m, hm⟩ := hN` (so `T.N = m + m`) and take
    `n = 0`; then `T.N / 2 = m` and `(T.N : ℝ) = 2 * m`, so the wavenumber is `2π/(2am) * (0 - m) = -π/a`.
H3. `have h0 : (0 : ℝ) ∈ T.QuantaWaveNumber := ⟨⟨T.N / 2, by have := NeZero.pos T.N; omega⟩, by simp⟩`,
    then `refine ⟨⟨⟨0, h0⟩, by simp [TightBindingChain.energyEigenvalue]⟩, ?_⟩` and
    `rintro _ ⟨k, rfl⟩; unfold TightBindingChain.energyEigenvalue; have := Real.cos_le_one (k * T.a); nlinarith`.
    Top: same shape with `-(Real.pi / T.a)`, `div_mul_cancel₀`, `Real.cos_neg`, `Real.cos_pi`.
-/
