/- E115 | Temperature and β | 3 min | Temperature, inverse temperature, NNReal coercions, positivity, field_simp, gcongr, physlib
GOAL
  physlib's `Temperature` wraps `T.val : ℝ≥0` (a non-negative real); its inverse temperature is
  `T.β = 1/(k_B T)`. For `T > 0` show `β > 0` and `β · k_B T = 1`; then show hotter means smaller `β`.
BANNED: Temperature.beta_pos

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.Thermodynamics.Temperature.Basic

open Constants

namespace E115

/- SKELETON · beta_inverse
  1. Turn both `↑T.β` into the formula `1 / (kB * T.toReal)`:               R1
  2. Put the positivity facts in context (the tactics below see only these):
       h  : (0 : ℝ) < T.toReal     from hT                                  R2
       hk : 0 < kB                                                          R4
  3. Split the `∧`:                                                          constructor
  4. First goal  `0 < 1 / (kB * T.toReal)`:                                  R5
     Second goal `1 / (kB * T.toReal) * (kB * T.toReal) = 1`:                R6
-/
-- BEGIN SPEC
theorem beta_inverse (T : Temperature) (hT : 0 < T.val) :
    0 < (T.β : ℝ) ∧ (T.β : ℝ) * (kB * T.toReal) = 1 :=
-- END SPEC
  sorry

/- SKELETON · beta_antitone
  1. Turn `↑T₂.β` and `↑T₁.β` into formulas (one rewrite per temperature):  R1 (twice, W1)
  2. Put the facts in context:
       0 < T₁.toReal               from h₁                                  R2
       T₁.toReal < T₂.toReal       from h                                   R3
       0 < kB                                                               R4
  3. `1 / (kB * T₂.toReal) < 1 / (kB * T₁.toReal)` by monotonicity:         R7 (W2)
-/
-- BEGIN SPEC
theorem beta_antitone (T₁ T₂ : Temperature) (h₁ : 0 < T₁.val) (h : T₁.val < T₂.val) :
    (T₂.β : ℝ) < T₁.β :=
-- END SPEC
  sorry

end E115

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Rewrite every `(T.β : ℝ)` with `Temperature.β_toReal` (R1); after that it is algebra in ℝ. The tactics
    that do that algebra only see facts in context, so state them about `T.toReal` and `kB` first.
H2. `beta_inverse`: R1, then `have`s for `0 < T.toReal` (R2) and `0 < kB` (R4), `constructor`, and one
    closing tactic per half (R5, R6). `beta_antitone`: R1 twice, the `have`s R2, R3, R4, then R7.
H3. `have hT' : (0 : ℝ) < T.toReal := hT` and `have hk := kB_pos`; the halves are `positivity` and
    `field_simp`. For `beta_antitone`: `rw [Temperature.β_toReal, Temperature.β_toReal]`, the three `have`s
    (`have h' : T₁.toReal < T₂.toReal := h`), then `gcongr`.
-/
