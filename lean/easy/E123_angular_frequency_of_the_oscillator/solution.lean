/- E123 | Angular frequency of the oscillator | 2 min | structure fields, field_simp, physlib
GOAL
  physlib's classical harmonic oscillator `S` bundles a mass `S.m > 0` and a spring constant `S.k > 0`,
  and defines the angular frequency `S.ω = √(k/m)`. Show `m ω² = k`.

GUIDE
  Entries R1–R4: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic

open ClassicalMechanics

namespace E123

/- SKELETON · m_mul_omega_sq
  1. Replace `S.ω ^ 2` by the data of the oscillator, `S.k / S.m`:          R1
     (do not unfold `ω`: that leaves a square root, guide W1)
  2. The goal is now `S.m * (S.k / S.m) = S.k`; get the nonzero fact
       S.m ≠ 0                                                              R2
  3. Cancel `S.m` using that fact:                                          R3  (or R4)
-/
-- BEGIN SPEC
theorem m_mul_omega_sq (S : HarmonicOscillator) : S.m * S.ω ^ 2 = S.k :=
-- END SPEC
  by
    rw [HarmonicOscillator.ω_sq]
    field_simp [S.m_ne_zero]

end E123

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Don't fight the square root: physlib already knows what `S.ω ^ 2` is (R1). After that the goal is
    pure real-number algebra, and the only thing that makes it true is `S.m ≠ 0`.
H2. Rewrite with `HarmonicOscillator.ω_sq`; what is left is `S.m * (S.k / S.m) = S.k`. Cancel the mass
    with `field_simp`, giving it `S.m_ne_zero` (R2, R3), or with the lemma `mul_div_cancel₀` (R4).
H3. `rw [HarmonicOscillator.ω_sq]`, then `field_simp [S.m_ne_zero]` (or `exact mul_div_cancel₀ _ S.m_ne_zero`).
-/
