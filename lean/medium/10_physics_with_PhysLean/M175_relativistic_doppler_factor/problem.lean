/- M175 | Relativistic Doppler factor | 5-10 min | boost, light-cone coordinates, γ_sq, field_simp, physlib
GOAL
  A boost with speed `β` along spatial axis `i` multiplies the light-cone coordinate `t + xᵢ` by the
  Doppler factor `γ β * (1 - β)`, and the two Doppler factors `γ(1 - β)`, `γ(1 + β)` are reciprocal.

REFERENCE
  -- `Lorentz.Vector d` is `Fin 1 ⊕ Fin d → ℝ`: `p (Sum.inl 0)` is time `t`, `p (Sum.inr i)` is `xᵢ` (c = 1)
  -- `boost i β hβ : LorentzGroup d` (needs `hβ : |β| < 1`); `boost i β hβ • p` applies it to `p`
  #check Lorentz.Vector.boost_time_eq      -- (boost i β hβ • p) (inl 0) = γ β * (p (inl 0) - β * p (inr i))
  #check Lorentz.Vector.boost_inr_self_eq  -- (boost i β hβ • p) (inr i) = γ β * (p (inr i) - β * p (inl 0))
  #check LorentzGroup.γ_sq                 -- |β| < 1 → γ β ^ 2 = 1 / (1 - β ^ 2)
  #check LorentzGroup.γ_det_not_zero       -- |β| < 1 → 1 - β ^ 2 ≠ 0
  example (a b : ℝ) (h : b ≠ 0) : a / b * b = a := by field_simp   -- clears denominators known ≠ 0
  -- `constructor` splits `∧`;  `ring` closes commutative-ring identities
-/
import Physlib.Relativity.LorentzGroup.Boosts.Apply

open Lorentz Vector LorentzGroup

namespace M175

-- BEGIN SPEC
theorem doppler {d : ℕ} (i : Fin d) (β : ℝ) (hβ : |β| < 1) (p : Lorentz.Vector d) :
    (boost i β hβ • p) (Sum.inl 0) + (boost i β hβ • p) (Sum.inr i)
      = γ β * (1 - β) * (p (Sum.inl 0) + p (Sum.inr i)) ∧
    (γ β * (1 - β)) * (γ β * (1 + β)) = 1 :=
-- END SPEC
  sorry

end M175

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Part 1 is pure algebra once the two boosted coordinates are written out. Part 2 is `γ² (1 - β²) = 1`.
H2. Part 1: rewrite with `boost_time_eq` and `boost_inr_self_eq`, then `ring`. Part 2: regroup the
    product as `γ β ^ 2 * (1 - β ^ 2)`, then substitute `γ_sq`.
H3. Regroup with `γ β * (1 - β) * (γ β * (1 + β)) = γ β ^ 2 * (1 - β ^ 2) := by ring`.
-/
