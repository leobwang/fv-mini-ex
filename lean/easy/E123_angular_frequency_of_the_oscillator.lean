/- E123 | Angular frequency of the oscillator | 2 min | structure fields, field_simp, physlib
GOAL
  physlib's classical harmonic oscillator `S` bundles a mass `S.m > 0` and a spring constant `S.k > 0`,
  and defines the angular frequency `S.ω = √(k/m)`. Show `m ω² = k`.

REFERENCE
  `S : HarmonicOscillator` is a structure: fields `S.m S.k : ℝ` and proofs `S.m_pos : 0 < S.m`, `S.k_pos`.
  example (S : HarmonicOscillator) : S.ω = √(S.k / S.m) := rfl
  #check ClassicalMechanics.HarmonicOscillator.ω_sq      -- S.ω ^ 2 = S.k / S.m
  #check ClassicalMechanics.HarmonicOscillator.m_ne_zero -- S.m ≠ 0
  example (a b : ℝ) (hb : b ≠ 0) : b * (a / b) = a := by field_simp
  `field_simp` clears denominators using the `≠ 0` facts in context or given as `field_simp [h]`.
NOTE: `HarmonicOscillator` here is `ClassicalMechanics.HarmonicOscillator` (opened below).
-/
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic

open ClassicalMechanics

namespace E123

-- BEGIN SPEC
theorem m_mul_omega_sq (S : HarmonicOscillator) : S.m * S.ω ^ 2 = S.k :=
-- END SPEC
  sorry

end E123

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Don't fight the square root: physlib already knows what `S.ω ^ 2` is.
H2. Rewrite `S.ω ^ 2` with `HarmonicOscillator.ω_sq`; what is left is `m * (k / m) = k`.
H3. `rw [HarmonicOscillator.ω_sq]; field_simp [S.m_ne_zero]` (or `mul_div_cancel₀ _ S.m_ne_zero`).
-/
