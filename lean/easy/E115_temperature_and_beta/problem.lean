/- E115 | Temperature and β | 3 min | Temperature, inverse temperature, NNReal coercions, positivity, field_simp, gcongr, physlib
GOAL
  physlib's `Temperature` wraps `T.val : ℝ≥0` (a non-negative real); its inverse temperature is
  `T.β = 1/(k_B T)`. For `T > 0` show `β > 0` and `β · k_B T = 1`; then show hotter means smaller `β`.

REFERENCE
  #check Temperature.β_toReal   -- (T.β : ℝ) = 1 / (kB * T.toReal)    (`T.β : ℝ≥0`, cast to ℝ)
  #check Constants.kB_pos       -- 0 < kB   (Boltzmann's constant; `open Constants` lets you write `kB`)
  example (T : Temperature) : (T.val : ℝ) = T.toReal := rfl   -- `toReal` is `T.val` cast to ℝ
  example (T : Temperature) (hT : 0 < T.val) : (0 : ℝ) < T.toReal := hT   -- moves `0 < ·` from ℝ≥0 to ℝ
  example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < 1 / (a * b) := by positivity
  example (a b : ℝ) (ha : a ≠ 0) : 1 / a * (a * b) = b := by field_simp   -- clears known-nonzero denominators
  example (x y : ℝ) (hx : 0 < x) (h : x < y) : 1 / y < 1 / x := by gcongr  -- monotonicity, piece by piece
BANNED: Temperature.beta_pos
NOTE: `positivity`, `field_simp`, `gcongr` only see facts in context: state `0 < T.toReal` and `0 < kB` with `have`.
-/
import Physlib.Thermodynamics.Temperature.Basic

open Constants

namespace E115

-- BEGIN SPEC
theorem beta_inverse (T : Temperature) (hT : 0 < T.val) :
    0 < (T.β : ℝ) ∧ (T.β : ℝ) * (kB * T.toReal) = 1 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem beta_antitone (T₁ T₂ : Temperature) (h₁ : 0 < T₁.val) (h : T₁.val < T₂.val) :
    (T₂.β : ℝ) < T₁.β :=
-- END SPEC
  sorry

end E115

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Rewrite every `(T.β : ℝ)` with `Temperature.β_toReal`; after that it is algebra in ℝ.
H2. Put the positivity facts in context first: `have hT' : (0 : ℝ) < T.toReal := hT` and
    `have hk := kB_pos`. Then `constructor` and close the two halves with one tactic each.
H3. After the two `have`s: `rw [Temperature.β_toReal]; exact ⟨by positivity, by field_simp⟩`; for `beta_antitone`:
    `rw [Temperature.β_toReal, Temperature.β_toReal]`, the two `have`s (`T₁.toReal < T₂.toReal := h`), `gcongr`.
-/
