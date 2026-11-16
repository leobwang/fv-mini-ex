/- E124 | Quantum oscillator level spacing | 2 min | unfold, push_cast, ring, Nat cast, physlib
GOAL
  The 1D quantum harmonic oscillator `Q` (mass `Q.m`, angular frequency `Q.ω`) has energy levels
  `Eₙ = (n + ½) ℏ ω`. Show that adjacent levels are equally spaced: `Eₙ₊₁ - Eₙ = ℏ ω`.

REFERENCE
  example (Q : HarmonicOscillator) (n : ℕ) : Q.eigenValue n = (n + 1/2) * ℏ * Q.ω := rfl
  `ℏ : {x : ℝ // 0 < x}` is reduced Planck's constant as a positive real; `(ℏ : ℝ)` (shown `↑ℏ`) casts it.
  example (n : ℕ) : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  `unfold f` (or `simp only [f]`) replaces a definition by its body.
  `push_cast` moves casts `↑(n + 1)` inward to `↑n + 1`; `ring` then closes commutative-ring identities.
NOTE: `HarmonicOscillator` here is `QuantumMechanics.OneDimension.HarmonicOscillator` (opened below).
-/
import Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.TISE

open QuantumMechanics OneDimension Constants

namespace E124

-- BEGIN SPEC
theorem eigenValue_gap (Q : HarmonicOscillator) (n : ℕ) :
    Q.eigenValue (n + 1) - Q.eigenValue n = ℏ * Q.ω :=
-- END SPEC
  by
    unfold HarmonicOscillator.eigenValue
    push_cast
    ring

end E124

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold `eigenValue`: the goal becomes an identity between real expressions with a cast `↑(n + 1)`.
H2. Push the cast inward so both levels are written in terms of `↑n`, then it is pure algebra.
H3. `unfold HarmonicOscillator.eigenValue; push_cast; ring`.
-/
