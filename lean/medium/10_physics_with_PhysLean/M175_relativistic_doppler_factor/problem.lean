/- M175 | Relativistic Doppler factor | 5-10 min | boost, light-cone coordinates, γ_sq, field_simp, physlib
GOAL
  A boost with speed `β` along spatial axis `i` multiplies the light-cone coordinate `t + xᵢ` by the
  Doppler factor `γ β * (1 - β)`, and the two Doppler factors `γ(1 - β)`, `γ(1 + β)` are reciprocal.

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.Relativity.LorentzGroup.Boosts.Apply

open Lorentz Vector LorentzGroup

namespace M175

/- SKELETON · doppler
  1. Split the two conjuncts:                                              R1
  2. First conjunct (t + xᵢ):
       write out the boosted time coordinate, then the boosted xᵢ          R2, R3
       the rest is algebra with `γ β` as an unknown                        R4
  3. Second conjunct, D₋ * D₊ = 1 with D₋ = γ β * (1 - β), D₊ = γ β * (1 + β):
       a. the fact hd : 1 - β ^ 2 ≠ 0                                      R5
       b. a calc chain: first regroup the product into
            γ β ^ 2 * (1 - β ^ 2)                                          R6, step proved by R4
       c. then `_ = 1`: substitute γ β ^ 2, clear the denominator (uses hd) R7 → R8
-/
-- BEGIN SPEC
theorem doppler {d : ℕ} (i : Fin d) (β : ℝ) (hβ : |β| < 1) (p : Lorentz.Vector d) :
    (boost i β hβ • p) (Sum.inl 0) + (boost i β hβ • p) (Sum.inr i)
      = γ β * (1 - β) * (p (Sum.inl 0) + p (Sum.inr i)) ∧
    (γ β * (1 - β)) * (γ β * (1 + β)) = 1 :=
-- END SPEC
  sorry

end M175

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Part 1 is pure algebra once the two boosted coordinates are written out. Part 2 is
    `γ² (1 - β²) = 1`; `ring` cannot see it because it knows nothing about `γ β`.
H2. `constructor`. Part 1: `rw` with `boost_time_eq` and `boost_inr_self_eq`, then `ring`. Part 2:
    `have hd := γ_det_not_zero β hβ`, then a `calc` that first regroups the product as
    `γ β ^ 2 * (1 - β ^ 2)` (by `ring`) and then substitutes `γ_sq β hβ`.
H3. `calc γ β * (1 - β) * (γ β * (1 + β)) = γ β ^ 2 * (1 - β ^ 2) := by ring`, then
    `_ = 1 := by rw [γ_sq β hβ]; field_simp`.
-/
