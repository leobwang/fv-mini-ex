/- M176 | Causal character is scale invariant | 15 min | causalCharacter, if-then-else, by_cases, map_smul, physlib
GOAL
  Rescaling a 4-vector by a nonzero `c` does not change whether it is timelike, lightlike or spacelike.

GUIDE
  Entries R1–R15: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.Basic

open Lorentz Vector

namespace M176

/- SKELETON · causalCharacter_smul
  1. Two facts first, before touching `causalCharacter`:
       h   : ⟪c • p, c • p⟫ₘ = c ^ 2 * ⟪p, p⟫ₘ      proof: simp [map_smul] (R1 → R2 → R3), then R4
       hc2 : 0 < c ^ 2                              proof: R5 (uses hc)
  2. Open both sides into their nested `if`s:                               R6
  3. Put `c ^ 2 * ⟪p, p⟫ₘ` into the left-hand conditions:                    R7 (rw [h])
  4. Split on `⟪p, p⟫ₘ = 0`:                                                 R8
       zero case: one `simp` with that fact decides every `if`              R9
  5. Nonzero case: first `c ^ 2 * ⟪p, p⟫ₘ ≠ 0`                                R10 → R11
     then split on `0 < ⟪p, p⟫ₘ`:                                            R8
       positive: `0 < c ^ 2 * ⟪p, p⟫ₘ`, then `simp` with all the facts     R12, R9
       not positive: `¬0 < c ^ 2 * ⟪p, p⟫ₘ`, then `simp` with all the facts R15 → R14 (with R13), R9
-/
-- BEGIN SPEC
theorem causalCharacter_smul {d : ℕ} (c : ℝ) (hc : c ≠ 0) (p : Lorentz.Vector d) :
    causalCharacter (c • p) = causalCharacter p :=
-- END SPEC
  by
    have h : ⟪c • p, c • p⟫ₘ = c ^ 2 * ⟪p, p⟫ₘ := by simp [map_smul]; ring
    have hc2 : 0 < c ^ 2 := by positivity
    unfold causalCharacter
    rw [h]
    by_cases h0 : ⟪p, p⟫ₘ = 0
    · simp [h0]
    · have hne : c ^ 2 * ⟪p, p⟫ₘ ≠ 0 := mul_ne_zero hc2.ne' h0
      by_cases hp : 0 < ⟪p, p⟫ₘ
      · simp [hne, h0, hp, mul_pos hc2 hp]
      · have hn : ¬ 0 < c ^ 2 * ⟪p, p⟫ₘ := fun h' => hp (pos_of_mul_pos_right h' hc2.le)
        simp [hne, h0, hp, hn]

end M176

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Only the sign of `⟪c • p, c • p⟫ₘ` matters, and it equals `c ^ 2 * ⟪p, p⟫ₘ` with `0 < c ^ 2`.
    So: compute the product, then decide the two `if`s of `causalCharacter` case by case.
H2. Prove `h : ⟪c • p, c • p⟫ₘ = c ^ 2 * ⟪p, p⟫ₘ` and `hc2 : 0 < c ^ 2` first; `unfold causalCharacter`,
    `rw [h]`, then `by_cases` on `⟪p, p⟫ₘ = 0` and, in the `≠` branch, on `0 < ⟪p, p⟫ₘ`. In each case
    feed `simp` the truth values of the conditions about the product `c ^ 2 * ⟪p, p⟫ₘ`.
H3. `have h : ⟪c • p, c • p⟫ₘ = c ^ 2 * ⟪p, p⟫ₘ := by simp [map_smul]; ring`, `positivity` for `hc2`.
    The product facts: `mul_ne_zero hc2.ne' h0`, `mul_pos hc2 hp`, and
    `fun h' => hp (pos_of_mul_pos_right h' hc2.le)` for `¬0 < c ^ 2 * ⟪p, p⟫ₘ`.
-/
