/- H103 | Collinear boosts compose (velocity addition) | 45-75 min | LorentzGroup, boost, mulVec, ext, field identities, physlib
GOAL
  Two boosts along the same spatial axis `i` compose to one boost along `i` with the relativistic
  sum of speeds `(β₁ + β₂) / (1 + β₁β₂)`; part of the claim is that this speed is again `< 1`.

REFERENCE
  -- `boost i β hβ : LorentzGroup d` boosts along axis `i` at speed `β` (c = 1, `hβ : |β| < 1`); `γ β = 1 / √(1 - β ^ 2)`
  -- `Λ • p` applies `Λ` to `p : Lorentz.Vector d = Fin 1 ⊕ Fin d → ℝ` (`p (Sum.inl 0)` = t, `p (Sum.inr i)` = xᵢ)
  #check LorentzGroup.eq_of_mulVec_eq     -- (∀ x, Λ.1 *ᵥ x = Λ'.1 *ᵥ x) → Λ = Λ'   (`*ᵥ` = matrix times vector)
  #check Lorentz.Vector.smul_eq_mulVec    -- Λ • p = Λ.1 *ᵥ p
  #check SemigroupAction.mul_smul         -- (x * y) • b = x • y • b
  #check Lorentz.Vector.boost_toCoord_eq  -- boost i β hβ • p = fun j => match j with | inl 0 => γ β * (t - β * xᵢ) | inr j => if j = i then γ β * (xᵢ - β * t) else xⱼ
  #check Real.sqrt_div'                   -- 0 ≤ y → √(x / y) = √x / √y   (also `Real.sqrt_mul`, `Real.sqrt_sq`)
  #check lt_div_iff₀                      -- 0 < c → (a < b / c ↔ a * c < b)   (and `div_lt_iff₀`)
  example (a c : ℝ) (h : c ≠ 0) : a / c * c = a := div_mul_cancel₀ a h
  -- `funext j; match j with | Sum.inl 0 => .. | Sum.inr j => ..` splits a goal about `Fin 1 ⊕ Fin d → ℝ`
  -- `linear_combination e * h` closes a ring goal that is `e` times the equation `h`
  -- `simp only [if_true]` turns a leftover `if i = i then a else b` into `a` (do this before `linear_combination`)
NOTE: with `open Lorentz Vector`, plain `mul_smul`/`smul_eq_mulVec` can be ambiguous: use the full names above.
-/
import Physlib.Relativity.LorentzGroup.Boosts.Apply

open Lorentz Vector LorentzGroup Matrix

namespace H103

-- MILESTONE (optional: change or delete)
theorem abs_add_lt {β₁ β₂ : ℝ} (h₁ : |β₁| < 1) (h₂ : |β₂| < 1) :
    |(β₁ + β₂) / (1 + β₁ * β₂)| < 1 := by
  sorry

-- MILESTONE (optional: change or delete)
theorem gamma_add {β₁ β₂ : ℝ} (h₁ : |β₁| < 1) (h₂ : |β₂| < 1) :
    γ ((β₁ + β₂) / (1 + β₁ * β₂)) = γ β₁ * γ β₂ * (1 + β₁ * β₂) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem mul_smul_apply {d : ℕ} (i : Fin d) {β₁ β₂ : ℝ} (h₁ : |β₁| < 1) (h₂ : |β₂| < 1)
    (p : Lorentz.Vector d) :
    (boost i β₁ h₁ * boost i β₂ h₂) • p = boost i β₁ h₁ • (boost i β₂ h₂ • p) := by
  sorry

-- BEGIN SPEC
theorem boost_mul_boost {d : ℕ} (i : Fin d) {β₁ β₂ : ℝ} (h₁ : |β₁| < 1) (h₂ : |β₂| < 1) :
    ∃ h : |(β₁ + β₂) / (1 + β₁ * β₂)| < 1,
      boost i β₁ h₁ * boost i β₂ h₂ = boost i ((β₁ + β₂) / (1 + β₁ * β₂)) h :=
-- END SPEC
  sorry

end H103

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two Lorentz matrices are equal if they act the same on every vector, and you have an explicit
    coordinate formula for a boost acting on a vector. The speed bound comes first: `refine ⟨abs_add_lt h₁ h₂, ?_⟩`.
H2. Everything reduces to two scalar facts: `abs_add_lt` (`abs_lt`, then `1 + β₁β₂ > 0` by `nlinarith`)
    and `gamma_add`, whose key is `1 - β₃² = (1 - β₁²)(1 - β₂²) / (1 + β₁β₂)²` (`field_simp; ring`),
    then take square roots. With those, compare the time row, the `i` row, and the other rows.
H3. `apply eq_of_mulVec_eq; intro x; rw [← Lorentz.Vector.smul_eq_mulVec, ← Lorentz.Vector.smul_eq_mulVec,
    SemigroupAction.mul_smul, boost_toCoord_eq, boost_toCoord_eq, boost_toCoord_eq, gamma_add h₁ h₂]`, then
    `funext j; match j with ...`. Time row: `simp only [if_true]` (clears the leftover `if i = i`), then with
    `h3 : (β₁ + β₂) / (1 + β₁ * β₂) * (1 + β₁ * β₂) = β₁ + β₂` use `linear_combination (γ β₁ * γ β₂ * x (Sum.inr i)) * h3`.
    Row `Sum.inr j`: `by_cases hj : j = i`; if so `subst hj; simp only [if_true]` and a similar `linear_combination`.
-/
