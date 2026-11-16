/- H104 | Boosts along different axes do not compose to a boost | 45-75 min | boost, matrix entries, Fin d sums with ite, symmetric matrices, physlib
GOAL
  In any spatial dimension `d`, a boost along axis `i` times a boost along a different axis `j`
  (both speeds nonzero) is not a pure boost along any axis `k` at any speed `β` (the seed of the
  Thomas–Wigner rotation). Idea: pure boosts are symmetric matrices, the product is not.

REFERENCE
  -- `boost i β hβ : LorentzGroup d` (needs `hβ : |β| < 1`); `Λ.1` is its matrix on `Fin 1 ⊕ Fin d`
  -- (index `Sum.inl 0` = time, `Sum.inr i` = space axis i); `boost` is defined entrywise by nested `if`s
  #check @LorentzGroup.boost_transpose_matrix_eq_self  -- (boost i β hβ).1ᵀ = (boost i β hβ).1
  #check lorentzGroupIsGroup_mul_coe   -- ((A * B : LorentzGroup d) : Matrix ..) = A.1 * B.1
  #check Matrix.mul_apply              -- (M * N) i k = ∑ j, M i j * N j k
  #check Fintype.sum_sum_type          -- ∑ x : α ⊕ β, f x = ∑ a, f (inl a) + ∑ b, f (inr b)
  #check @Finset.sum_eq_zero           -- (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
  #check LorentzGroup.γ                -- γ β = 1 / √(1 - β ^ 2)   (`Real.sqrt_ne_zero'`: √x ≠ 0 ↔ 0 < x)
  example (M N : Matrix (Fin 2) (Fin 2) ℝ) (h : M = N) (i j : Fin 2) : M i j = N i j := congrFun (congrFun h i) j
  #check @LorentzGroup.boost_inr_other_inr       -- j ≠ i → (boost i β hβ).1 (inr j) (inr k) = if j = k then 1 else 0 (row j = identity's)
  #check @LorentzGroup.boost_inr_self_inr_other  -- j ≠ i → (boost i β hβ).1 (inr i) (inr j) = 0  (also `boost_inr_other_inl_0`)
  -- entries `(inl 0, inl 0)`, `(inl 0, inr i)`, `(inr i, inl 0)` of `boost i` are `@[simp]`: plain `simp` evaluates them
NOTE: unfolding with `simp [boost, ..]` leaves nested `if`s whose shape depends on `hij` vs `Ne.symm hij`; prefer the named lemmas.
-/
import Physlib.Relativity.LorentzGroup.Boosts.Basic

open LorentzGroup Matrix

namespace H104

-- MILESTONE (optional: change or delete)
theorem gamma_ne_zero (β : ℝ) (hβ : |β| < 1) : γ β ≠ 0 := by
  have : 0 < 1 - β ^ 2 := by rw [abs_lt] at hβ; nlinarith
  simp [γ, Real.sqrt_ne_zero', this]

-- MILESTONE (optional: change or delete)
theorem entry_ij {d : ℕ} {i j : Fin d} (hij : i ≠ j) {β₁ β₂ : ℝ} (h₁ : |β₁| < 1) (h₂ : |β₂| < 1) :
    (boost i β₁ h₁ * boost j β₂ h₂).1 (Sum.inr i) (Sum.inr j) = γ β₁ * β₁ * (γ β₂ * β₂) := by
  simp only [lorentzGroupIsGroup_mul_coe, Matrix.mul_apply, Fintype.sum_sum_type]
  simp
  -- WHY: the time term is `@[simp]`; the spatial sum is left, and each of its terms is 0.
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : l = i
  · subst hl
    simp [boost_inr_other_inr h₂ hij, hij]
  · simp [boost_inr_self_inr_other h₁ hl]

-- MILESTONE (optional: change or delete)
theorem entry_ji {d : ℕ} {i j : Fin d} (hij : i ≠ j) {β₁ β₂ : ℝ} (h₁ : |β₁| < 1) (h₂ : |β₂| < 1) :
    (boost i β₁ h₁ * boost j β₂ h₂).1 (Sum.inr j) (Sum.inr i) = 0 := by
  simp only [lorentzGroupIsGroup_mul_coe, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [boost_inr_other_inr h₁ (Ne.symm hij), boost_inr_other_inl_0 h₁ (Ne.symm hij),
    boost_inr_self_inr_other h₂ hij]

-- BEGIN SPEC
theorem boost_mul_boost_ne_boost {d : ℕ} {i j : Fin d} (hij : i ≠ j) {β₁ β₂ : ℝ}
    (h₁ : |β₁| < 1) (h₂ : |β₂| < 1) (h₁0 : β₁ ≠ 0) (h₂0 : β₂ ≠ 0) :
    ∀ (k : Fin d) (β : ℝ) (hβ : |β| < 1), boost i β₁ h₁ * boost j β₂ h₂ ≠ boost k β hβ :=
-- END SPEC
  by
    intro k β hβ h
    have e := congrFun (congrFun (boost_transpose_matrix_eq_self k hβ) (Sum.inr i)) (Sum.inr j)
    rw [← h] at e
    simp only [transpose_apply] at e
    rw [entry_ij hij, entry_ji hij] at e
    have hne : γ β₁ * β₁ * (γ β₂ * β₂) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (gamma_ne_zero β₁ h₁) h₁0) (mul_ne_zero (gamma_ne_zero β₂ h₂) h₂0)
    exact hne e.symm

end H104

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Suppose the product equals `boost k β hβ`. A boost's matrix equals its transpose, so the product's
    `(inr i, inr j)` and `(inr j, inr i)` entries would have to agree. Compute both.
H2. `(B₁B₂)ᵢⱼ = ∑ₗ (B₁)ᵢₗ (B₂)ₗⱼ`: only `l = time` survives, giving `(-γ₁β₁)(-γ₂β₂)`; row `j` of `B₁` is a row
    of the identity, so `(B₁B₂)ⱼᵢ = (B₂)ⱼᵢ = 0`. For the entries: `simp only [lorentzGroupIsGroup_mul_coe,
    Matrix.mul_apply, Fintype.sum_sum_type]`, then `simp [..named entry lemmas..]`; in `entry_ij` a spatial
    sum `∑ l` is left: every term is 0 (`Finset.sum_eq_zero`, split on `l = i`). `γ β ≠ 0` since `0 < 1 - β ^ 2`.
H3. Main: `intro k β hβ h`, then `have e := congrFun (congrFun (boost_transpose_matrix_eq_self k hβ) (Sum.inr i)) (Sum.inr j)`
    and `rw [← h] at e`: after `transpose_apply`, `e` says the product's `(j, i)` entry equals its `(i, j)` entry.
-/
