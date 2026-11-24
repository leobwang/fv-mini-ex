/- E119 | Tight-binding bandwidth | 2-3 min | TightBindingChain, energyEigenvalue, abs, subtypes, physlib
GOAL
  In physlib's tight-binding chain (on-site energy `T.E0`, hopping `T.t`, lattice spacing `T.a`), the
  Bloch state of wavenumber `k` has energy `E(k) = E0 - 2t cos(ka)`. Show `|E(k) - E0| ≤ 2|t|`
  (the band has width `4|t|`).

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter

namespace E119

/- SKELETON · bandwidth
  1. Unfold E(k) into its formula `T.E0 - 2 * T.t * Real.cos (↑k * T.a)`:        R1
  2. Cancel the two `E0`s inside `|…|`: rewrite with an identity proved by ring
       T.E0 - 2 * T.t * Real.cos (k * T.a) - T.E0 = -(2 * T.t * Real.cos (k * T.a))   R2
  3. Peel the absolute value: drop the minus, split the product twice,
     evaluate `|2|`; the goal becomes `2 * |T.t| * |Real.cos (↑k * T.a)| ≤ 2 * |T.t|`:  R3, R4, R4, R5
  4. Bound `a * b ≤ a` with `a = 2 * |T.t|`, `b = |Real.cos (↑k * T.a)|`:          R6
       its two arguments: `0 ≤ 2 * |T.t|`                                       R7
                          `|Real.cos (↑k * T.a)| ≤ 1`                            R8
-/
-- BEGIN SPEC
theorem bandwidth (T : TightBindingChain) (k : T.QuantaWaveNumber) :
    |T.energyEigenvalue k - T.E0| ≤ 2 * |T.t| :=
-- END SPEC
  by
    unfold TightBindingChain.energyEigenvalue
    rw [show T.E0 - 2 * T.t * Real.cos (k * T.a) - T.E0 = -(2 * T.t * Real.cos (k * T.a)) by ring,
      abs_neg, abs_mul, abs_mul, abs_two]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

end E119

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold `energyEigenvalue` (R1). The two `E0`s inside `|…|` do not cancel by themselves: rewrite the
    difference to `-(2 t cos(ka))` with a ring identity (R2) before touching `|…|`.
H2. Rewrite with a `show … by ring` identity (R2), peel the absolute value with `abs_neg`, `abs_mul`
    (twice) and `abs_two` (R3–R5), then bound `2|t| · |cos(ka)| ≤ 2|t|` using `|cos| ≤ 1` (R6–R8).
H3. The cancellation: `rw [show T.E0 - 2 * T.t * Real.cos (k * T.a) - T.E0 = -(2 * T.t * Real.cos (k * T.a)) by ring]`.
    The last line, once the goal is `2 * |T.t| * |Real.cos (↑k * T.a)| ≤ 2 * |T.t|`:
    `exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)`.
-/
