/- E124 | Quantum oscillator level spacing | 2 min | unfold, push_cast, ring, Nat cast, physlib
GOAL
  The 1D quantum harmonic oscillator `Q` (mass `Q.m`, angular frequency `Q.ω`) has energy levels
  `Eₙ = (n + ½) ℏ ω`. Show that adjacent levels are equally spaced: `Eₙ₊₁ - Eₙ = ℏ ω`.

GUIDE
  Entries R1–R3: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.TISE

open QuantumMechanics OneDimension Constants

namespace E124

/- SKELETON · eigenValue_gap
  1. Unfold both levels; the goal becomes a real identity with a cast `↑(n + 1)`:   R1
  2. Push the cast inward, `↑(n + 1)` → `↑n + 1`, so both levels are in `↑n`:      R2
  3. Close the commutative-ring identity (`↑n`, `↑ℏ`, `Q.ω` are unknowns):        R3
-/
-- BEGIN SPEC
theorem eigenValue_gap (Q : HarmonicOscillator) (n : ℕ) :
    Q.eigenValue (n + 1) - Q.eigenValue n = ℏ * Q.ω :=
-- END SPEC
  sorry

end E124

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `Q.eigenValue` is a definition: unfold it (full name `HarmonicOscillator.eigenValue`). The goal is
    then an identity of real numbers containing the cast `↑(n + 1)`.
H2. `ring` treats `↑(n + 1)` as an unknown unrelated to `↑n`, so first push the cast inward; after that
    the two levels differ by exactly `↑ℏ * Q.ω` and it is pure algebra.
H3. `unfold HarmonicOscillator.eigenValue`, then `push_cast`, then `ring`.
-/
