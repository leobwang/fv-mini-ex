/- M189 | E = c·m·v is not dimensionally correct | 10-15 min | counterexample, SIPrimed, scaleUnit, not_forall, norm_num, physlib
GOAL
  For every constant `c ≠ 0`, the relation `E = c · m · v` (on the raw numbers of a mass, a velocity and an
  energy) is not dimensionally correct: find unit systems and values where it holds in one system but fails
  after converting. (For `c = 0` it is correct, so `hc` matters.)

GUIDE
  Entries R1–R18: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · wrong_not_isDimensionallyCorrect
  1. Unfold "dimensionally correct" and push `¬` inside, all in ONE `simp only [...]`:  R1, R2, R3, R4
       the goal becomes  ∃ u1 u2 m v E, ¬ (relation after converting = relation before)
  2. Give the two unit systems, then values `m, v, E` that make `E = c·m·v` TRUE:      R5, R6
  3. Expose the relation's body:                                                     R7
  4. Compute the converted numbers with one `norm_num [...]` that names R9, R11, R13;
     it applies R8, R10, R12, R14, R15 by itself:                                    R8 → R9 → R10 → R11 → R12 → R13 → R14 → R15
       left:  ¬ (a * c = c * b)  for two numerals a ≠ b
  5. Turn that into `c = 0` and close it with hc:                                     R16 → R17 → R18
-/
-- BEGIN SPEC
theorem wrong_not_isDimensionallyCorrect (c : ℝ) (hc : c ≠ 0) :
    ¬ IsDimensionallyCorrect (Wrong c) :=
-- END SPEC
  sorry

end M189

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold "dimensionally correct" into a statement about all unit systems and all arguments, and push
    the negation inside: you must produce two unit systems and concrete `m, v, E` for which `E = c m v`
    holds in one system and fails after converting to the other (cheatsheet R1–R5).
H2. Use `SI` and `SIPrimed` (units scaled by 2, 3, 5) and `m = v = 1`, `E = c`, which satisfy the relation.
    Converting multiplies `E` by `s_M s_L² / s_T²` but `c m v` by `s_M s_L / s_T` (`s_M, s_L, s_T` = the
    mass, length, time factors); here `s_L / s_T ≠ 1`, so the converted equation says `a c = b c` with
    numerals `a ≠ b`, which forces `c = 0` (R16–R18).
H3. `simp only [isDimensionallyCorrect_fun_iff, not_forall, funext_iff, scaleUnit_apply_fun]`, then
    `use SI, SIPrimed, ⟨1⟩, ⟨1⟩, ⟨c⟩`, `unfold Wrong`, `norm_num [WithDim.scaleUnit_val, M𝓭, L𝓭, T𝓭, NNReal.smul_def]`.
    What is left is `¬ (a * c = c * b)` for numerals `a ≠ b`: assume it (R16), reduce `False` to `c = 0`
    with `hc` (R17) and finish by linear arithmetic (R18).
-/
