/- H108 | Twin paradox: the travelling twin is younger | 1-1.5 h | causal cones, reverse triangle inequality, Real.sqrt, physlib
GOAL
  In physlib's `InstantaneousTwinParadox`, twin A goes straight from `startPoint` to `endPoint`; twin B goes via
  `twinBMid` (each event causally after the previous). physlib states "A is older" only informally. Prove it:
  `0 ≤ T.ageGap`, i.e. τ(start, end) ≥ τ(start, mid) + τ(mid, end) (reverse triangle inequality).

REFERENCE
  `SpaceTime d = Lorentz.Vector d = (Fin 1 ⊕ Fin d → ℝ)`; `⟪p, q⟫ₘ = p⁰ q⁰ - p⃗ · q⃗` (scoped: `open Lorentz Vector`);
  `p.timeComponent = p (Sum.inl 0)` (rfl) is `p⁰`, `p.spatialPart : EuclideanSpace ℝ (Fin d)` is `p⃗`; `√x` is `Real.sqrt x` (`= 0` if x < 0).
  `SpaceTime.properTime q p = √⟪p - q, p - q⟫ₘ`; `T.ageGap = τ(start, end) - (τ(start, mid) + τ(mid, end))`:
  `unfold InstantaneousTwinParadox.ageGap InstantaneousTwinParadox.properTimeTwinA InstantaneousTwinParadox.properTimeTwinB SpaceTime.properTime`
  `causallyFollows p q`: `q - p` timelike with `0 < (q - p)⁰`, or lightlike with `0 ≤ (q - p)⁰` (`rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩`).
  #check Lorentz.Vector.timeLike_iff_norm_sq_pos  -- causalCharacter p = .timeLike ↔ 0 < ⟪p, p⟫ₘ  (`lightLike_iff_norm_sq_zero`: = 0)
  #check Lorentz.Vector.minkowskiProduct_eq_timeComponent_spatialPart  -- ⟪p, q⟫ₘ = p⁰ * q⁰ - inner ℝ p⃗ q⃗  (`_self_`: ‖p⁰‖^2 - ‖p⃗‖^2)
  #check real_inner_le_norm   -- inner ℝ x y ≤ ‖x‖ * ‖y‖
  #check abs_le_of_sq_le_sq'  -- a ^ 2 ≤ b ^ 2 → 0 ≤ b → -b ≤ a ∧ a ≤ b
  #check Real.sqrt_mul        -- 0 ≤ x → √(x * y) = √x * √y;   `Real.sqrt_le_left : 0 ≤ y → (√x ≤ y ↔ x ≤ y ^ 2)`
  #check Real.le_sqrt_of_sq_le  -- x ^ 2 ≤ y → x ≤ √y;   `Real.sq_sqrt : 0 ≤ x → √x ^ 2 = x`
  `simp [map_add, minkowskiProduct_symm v u]; ring` proves `⟪u + v, u + v⟫ₘ = ⟪u, u⟫ₘ + 2 * ⟪u, v⟫ₘ + ⟪v, v⟫ₘ`.
-/
import Physlib.Relativity.Special.TwinParadox.Basic

open Lorentz Vector SpecialRelativity

namespace H108

-- MILESTONE (optional: change or delete)
/-- A causally later event lies inside or on the future cone: `‖Δx⃗‖ ≤ Δt`. -/
theorem future_causal {d : ℕ} {p q : SpaceTime d} (h : causallyFollows p q) :
    ‖(q - p).spatialPart‖ ≤ (q - p).timeComponent := by
  sorry

-- MILESTONE (optional: change or delete)
/-- Reverse Cauchy–Schwarz for future causal vectors. -/
theorem reverse_cauchy_schwarz {d : ℕ} (u v : Lorentz.Vector d)
    (hu : ‖u.spatialPart‖ ≤ u.timeComponent) (hv : ‖v.spatialPart‖ ≤ v.timeComponent) :
    √⟪u, u⟫ₘ * √⟪v, v⟫ₘ ≤ ⟪u, v⟫ₘ := by
  sorry

-- MILESTONE (optional: change or delete)
/-- Reverse triangle inequality for future causal vectors. -/
theorem reverse_triangle {d : ℕ} (u v : Lorentz.Vector d)
    (hu : ‖u.spatialPart‖ ≤ u.timeComponent) (hv : ‖v.spatialPart‖ ≤ v.timeComponent) :
    √⟪u, u⟫ₘ + √⟪v, v⟫ₘ ≤ √⟪u + v, u + v⟫ₘ := by
  sorry

-- BEGIN SPEC
theorem ageGap_nonneg (T : InstantaneousTwinParadox) : 0 ≤ T.ageGap :=
-- END SPEC
  sorry

end H108

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Put `u = mid - start` and `v = end - mid`; then `u + v = end - start`, and the claim is
    `√⟪u, u⟫ₘ + √⟪v, v⟫ₘ ≤ √⟪u + v, u + v⟫ₘ` for two vectors in the closed future cone `‖w⃗‖ ≤ w⁰`.
H2. Square both sides: it reduces to `√⟪u, u⟫ₘ √⟪v, v⟫ₘ ≤ ⟪u, v⟫ₘ`. With `a = u⁰, b = v⁰, c = ‖u⃗‖, e = ‖v⃗‖`
    you have `⟪u, u⟫ₘ = a² - c²`, `⟪v, v⟫ₘ = b² - e²` and `⟪u, v⟫ₘ ≥ ab - ce ≥ 0` (Cauchy–Schwarz), and
    `(a² - c²)(b² - e²) ≤ (ab - ce)²` because the difference is `(ae - bc)²`.
H3. Reverse Cauchy–Schwarz: `rw [huu, hvv, ← Real.sqrt_mul (by nlinarith)]`, `refine le_trans ?_ huv`,
    `rw [Real.sqrt_le_left hnn]`, `nlinarith [sq_nonneg (a * e - b * c)]`. Triangle: `apply Real.le_sqrt_of_sq_le`,
    expand with `add_sq` and `Real.sq_sqrt`. Main: unfold, apply `reverse_triangle` to `u, v`, rewrite `u + v` by `abel`.
-/
