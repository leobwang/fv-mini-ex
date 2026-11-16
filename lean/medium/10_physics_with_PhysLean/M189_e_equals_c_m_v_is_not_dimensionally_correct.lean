/- M189 | E = c·m·v is not dimensionally correct | 10-15 min | counterexample, SIPrimed, scaleUnit, not_forall, norm_num, physlib
GOAL
  For every constant `c ≠ 0`, the relation `E = c · m · v` (on the raw numbers of a mass, a velocity and an
  energy) is not dimensionally correct: find unit systems and values where it holds in one system but fails
  after converting. (For `c = 0` it is correct, so `hc` matters.)

REFERENCE
  `WithDim d ℝ`: a real number tagged with dimension `d`; `⟨a⟩ : WithDim d ℝ` has value `a`.
  `M𝓭 L𝓭 T𝓭` (mass, length, time) are plain `def`s of `Dimension`s; unfold them to see their exponents.
  `SI`; `SIPrimed`: SI with the length, time, mass units scaled by 2, 3, 5 (charge 7, temperature 11).
  #check isDimensionallyCorrect_fun_iff -- IsDimensionallyCorrect f ↔ ∀ u1 u2 m, scaleUnit u1 u2 (f (scaleUnit u2 u1 m)) = f m
  #check UnitDependent.scaleUnit_apply_fun -- scaleUnit u1 u2 f m1 = scaleUnit u1 u2 (f (scaleUnit u2 u1 m1))
  #check WithDim.scaleUnit_val          -- (scaleUnit u1 u2 m).val = (u1.dimScale u2) d • m.val
  #check LTMCTUnitChoices.dimScale_apply -- (u1.dimScale u2) d = (u1.length / u2.length) ^ d.length * ...
  #check NNReal.smul_def                -- c • x = (c : ℝ) • x   for `c : NNReal`
  #check not_forall                     -- (¬ ∀ x, p x) ↔ ∃ x, ¬ p x
  `use a, b` supplies the first two witnesses of an `∃ x y ..., P x y ...` goal.
-/
import Physlib.Units.WithDim.Speed

open Dimension CarriesDimension LTMCTUnitChoices UnitDependent HasDim WithDim

namespace M189

-- BEGIN SPEC
/-- `E = c · m · v` on the raw numbers (wrong: the dimensions differ by a length). -/
def Wrong (c : ℝ) (m : WithDim M𝓭 ℝ) (v : WithDim (L𝓭 * T𝓭⁻¹) ℝ)
    (E : WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ) : Prop :=
  E.1 = c * m.1 * v.1
-- END SPEC

-- BEGIN SPEC
theorem wrong_not_isDimensionallyCorrect (c : ℝ) (hc : c ≠ 0) :
    ¬ IsDimensionallyCorrect (Wrong c) :=
-- END SPEC
  sorry

end M189

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold "dimensionally correct" into a statement about all unit systems and all arguments, and push
    the negation inside: you must produce two unit systems and a concrete `m, v, E` that satisfy `E = c m v`.
H2. `m = v = 1`, `E = c` satisfies the relation. A unit change multiplies `E` by `s_M s_L² / s_T²` but `c m v` by
    `s_M s_L / s_T` (`s_M, s_L, s_T` = the mass, length, time factors); between `SI` and `SIPrimed`,
    `s_L / s_T ≠ 1`, so the rescaled equation says `k₁ c = k₂ c` with numbers `k₁ ≠ k₂`, i.e. `c = 0`.
H3. `simp only [isDimensionallyCorrect_fun_iff, not_forall, funext_iff, scaleUnit_apply_fun]`, then
    `use SI, SIPrimed, ⟨1⟩, ⟨1⟩, ⟨c⟩`, `unfold Wrong`, `norm_num [WithDim.scaleUnit_val, M𝓭, L𝓭, T𝓭, NNReal.smul_def]`.
    What is left is `¬ (a * c = c * b)` for numerals `a ≠ b`: assume it and derive `c = 0`.
-/
