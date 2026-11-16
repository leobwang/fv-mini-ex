/- M177 | Time dilation, with its equality case | 15-20 min | properTime, Real.sqrt, sums of squares, Finset.sum_eq_zero_iff_of_nonneg, physlib
GOAL
  For events `q`, `p` with coordinate-time gap `Δt = (p - q)⁰ > 0`, the proper time
  `τ = √⟪p - q, p - q⟫ₘ` satisfies `τ ≤ Δt`, and `τ = Δt` iff `p`, `q` have the same spatial coordinates.

REFERENCE
  -- `SpaceTime d` is `Lorentz.Vector d = Fin 1 ⊕ Fin d → ℝ`; `v (Sum.inl 0)` = time, `v (Sum.inr i)` = xᵢ
  #check SpaceTime.properTime   -- properTime q p = √⟪p - q, p - q⟫ₘ  (`unfold` it)
  #check Lorentz.Vector.minkowskiProduct_toCoord  -- ⟪p, q⟫ₘ = p (inl 0) * q (inl 0) - ∑ i, p (inr i) * q (inr i)
  #check Real.sqrt_le_left      -- 0 ≤ y → (√x ≤ y ↔ x ≤ y ^ 2)
  #check Real.sqrt_eq_zero'     -- √x = 0 ↔ x ≤ 0
  #check Real.sq_sqrt           -- 0 ≤ x → √x ^ 2 = x      (and Real.sqrt_sq : 0 ≤ x → √(x ^ 2) = x)
  #check Finset.sum_eq_zero_iff_of_nonneg  -- (∀ i ∈ s, 0 ≤ f i) → (∑ i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0)
  example (a : ℝ) (h : a ^ 2 = 0) : a = 0 := pow_eq_zero_iff two_ne_zero |>.mp h
  -- `set v := p - q with hv` names the difference; `(p - q) x = p x - q x` holds by `rfl`/`simp`
BANNED: Lorentz.Vector.minkowskiProduct_self_le_timeComponent_sq, Lorentz.Vector.timelike_time_dominates_space
NOTE: `0 < Δt`, not `0 ≤`: for Δt = 0 and spacelike separation, `√(negative) = 0 = Δt`.
-/
import Physlib.Relativity.Special.ProperTime

open Lorentz Vector

namespace M177

-- BEGIN SPEC
theorem properTime_le {d : ℕ} (q p : SpaceTime d) (h : 0 < (p - q) (Sum.inl 0)) :
    SpaceTime.properTime q p ≤ (p - q) (Sum.inl 0) ∧
      (SpaceTime.properTime q p = (p - q) (Sum.inl 0) ↔ ∀ i, p (Sum.inr i) = q (Sum.inr i)) :=
-- END SPEC
  sorry

end M177

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. With `v = p - q`: `⟪v, v⟫ₘ = (v⁰)² - ∑ i, (vⁱ)²`, and the sum of squares is `≥ 0`.
H2. Prove `key : ⟪v, v⟫ₘ = v (Sum.inl 0) ^ 2 - ∑ i, v (Sum.inr i) ^ 2` and `hs : 0 ≤ ∑ ...`. Part 1:
    `Real.sqrt_le_left`. (→): rule out `⟪v, v⟫ₘ < 0` (then `τ = 0 < Δt`), square both sides to get
    `∑ = 0`, so each `vⁱ = 0`. (←): the sum is `0`, so `τ = √((v⁰)²) = v⁰`.
H3. `key` is `by rw [minkowskiProduct_toCoord]; simp [sq]`; (←) ends with
    `rw [key, hz, sub_zero, Real.sqrt_sq h.le]` where `hz : ∑ i, v (Sum.inr i) ^ 2 = 0 := Finset.sum_eq_zero ...`.
-/
