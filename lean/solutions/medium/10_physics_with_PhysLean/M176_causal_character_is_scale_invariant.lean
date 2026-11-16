/- M176 | Causal character is scale invariant | 15 min | causalCharacter, if-then-else, by_cases, map_smul, physlib
GOAL
  Rescaling a 4-vector by a nonzero `c` does not change whether it is timelike, lightlike or spacelike.

REFERENCE
  -- `⟪p, q⟫ₘ` is the Minkowski product `p⁰q⁰ - ∑ᵢ pⁱqⁱ`; it is a linear map into linear maps (bilinear)
  #check Lorentz.Vector.causalCharacter
  -- causalCharacter p = if ⟪p, p⟫ₘ = 0 then .lightLike else if 0 < ⟪p, p⟫ₘ then .timeLike else .spaceLike
  #check map_smul   -- f (c • x) = c • f x  (works for `minkowskiProduct` and `minkowskiProduct p`)
  example (d : ℕ) (c : ℝ) (p : Lorentz.Vector d) : ⟪c • p, p⟫ₘ = c * ⟪p, p⟫ₘ := by simp [map_smul]
  #check pos_of_mul_pos_right   -- 0 < a * b → 0 ≤ a → 0 < b
  #check mul_ne_zero            -- a ≠ 0 → b ≠ 0 → a * b ≠ 0
  -- `unfold causalCharacter` shows the `if`s; `by_cases h : x = 0` then `simp [h]` decides them
-/
import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.Basic

open Lorentz Vector

namespace M176

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
H1. Only the sign of `⟪c • p, c • p⟫ₘ` matters, and it is `c ^ 2 * ⟪p, p⟫ₘ` with `c ^ 2 > 0`.
H2. Prove `h : ⟪c • p, c • p⟫ₘ = c ^ 2 * ⟪p, p⟫ₘ` and `hc2 : 0 < c ^ 2` first; `unfold causalCharacter`,
    `rw [h]`, then case on `⟪p, p⟫ₘ = 0` and on `0 < ⟪p, p⟫ₘ`.
H3. `have h : ⟪c • p, c • p⟫ₘ = c ^ 2 * ⟪p, p⟫ₘ := by simp [map_smul]; ring`; in the nonzero case feed
    `simp` the facts `mul_ne_zero hc2.ne' h0` and (for the negative case) `pos_of_mul_pos_right · hc2.le`.
-/
