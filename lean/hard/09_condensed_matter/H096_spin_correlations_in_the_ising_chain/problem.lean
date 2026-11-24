/- H096 | Spin correlations in the Ising chain | 1.5-2 h | Fin.snoc, Fin.snocEquiv, Nat.le_induction, tanh, correlation length, mathlib
GOAL
  Open zero-field chain of `n + 1` spins `s_i = spin (σ i) = ±1`, energy `E(σ) = -J ∑_{i<n} s_i s_{i+1}`.
  The thermal average `⟨s₀ s_r⟩ = (∑_σ s₀ s_r e^{-βE(σ)}) / Z` equals `tanh(βJ)^r` for every `r ≤ n`,
  whatever the length `n`: correlations decay like `e^{-r/ξ}` (correlation length
  `ξ = -1 / log tanh βJ` for `βJ > 0`), so there is no long-range order at `T > 0`.

REFERENCE
  #check Fin.snocEquiv          -- (α : Fin (n+1) → Type*) : α (last n) × (∀ i, α i.castSucc) ≃ ∀ i, α i
  #check Equiv.sum_comp         -- (e : ι ≃ κ) (g : κ → M) : ∑ i, g (e i) = ∑ i, g i
  #check Fintype.sum_prod_type  -- ∑ x : α × β, f x = ∑ a, ∑ b, f (a, b)   (Finset.sum_comm swaps sums)
  #check Fin.sum_univ_castSucc  -- ∑ i : Fin (n+1), f i = ∑ i : Fin n, f i.castSucc + f (Fin.last n)
  #check Fin.snoc_castSucc      -- Fin.snoc p x i.castSucc = p i   (Fin.snoc_last : Fin.snoc p x (last n) = x)
  #check Fin.succ_last          -- (Fin.last n).succ = Fin.last (n + 1)   (also Fin.succ_castSucc)
  #check Nat.le_induction       -- P m _ → (∀ n (h : m ≤ n), P n h → P (n+1) _) → ∀ n (h : m ≤ n), P n h
  #check Real.tanh_eq_sinh_div_cosh  -- tanh x = sinh x / cosh x   (Real.sinh_eq, Real.cosh_eq: exp form)
  #check mul_div_mul_left       -- c ≠ 0 → c * a / (c * b) = a / b
  example : (⟨2, by omega⟩ : Fin 3) = Fin.last 2 := rfl
  -- `induction n, hr using Nat.le_induction with | base => _ | succ n hrn ih => _`
NOTE: `Fin.snoc σ b` appends spin `b` after site `n`; write it as `(Fin.snoc σ b : Fin (n + 2) → Bool)`.
-/
import Mathlib

namespace H096

-- BEGIN SPEC
/-- Spin value of an up (`true`) / down (`false`) site. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- Zero-field energy of an open chain of `n + 1` spins with coupling `J`. -/
noncomputable def energy (J : ℝ) {n : ℕ} (σ : Fin (n + 1) → Bool) : ℝ :=
  -J * ∑ i : Fin n, spin (σ i.castSucc) * spin (σ i.succ)

/-- Partition function of the chain of `n + 1` spins. -/
noncomputable def Z (β J : ℝ) (n : ℕ) : ℝ :=
  ∑ σ : Fin (n + 1) → Bool, Real.exp (-β * energy J σ)

/-- Thermal average `⟨s₀ s_r⟩` in a chain of `n + 1` spins (`r ≤ n`). -/
noncomputable def corr (β J : ℝ) (n r : ℕ) (hr : r ≤ n) : ℝ :=
  (∑ σ : Fin (n + 1) → Bool,
    spin (σ 0) * spin (σ ⟨r, by omega⟩) * Real.exp (-β * energy J σ)) / Z β J n
-- END SPEC

-- MILESTONE (optional: change or delete)
/-- Summing out the last spin of a chain of `n + 2` spins. -/
theorem snoc_split (β J : ℝ) (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool → ℝ) :
    ∑ σ : Fin (n + 2) → Bool,
        f (fun i => σ i.castSucc) (σ (Fin.last (n + 1))) * Real.exp (-β * energy J σ) =
      ∑ τ : Fin (n + 1) → Bool, (∑ b : Bool,
        f τ b * Real.exp (β * J * (spin (τ (Fin.last n)) * spin b))) * Real.exp (-β * energy J τ) := by
  sorry

-- MILESTONE (optional: change or delete)
/-- An observable that ignores the last spin: appending a spin multiplies the sum by `2 cosh βJ`. -/
theorem sum_snoc (β J : ℝ) (n : ℕ) (g : (Fin (n + 1) → Bool) → ℝ) :
    ∑ σ : Fin (n + 2) → Bool, g (fun i => σ i.castSucc) * Real.exp (-β * energy J σ) =
      2 * Real.cosh (β * J) * ∑ τ : Fin (n + 1) → Bool, g τ * Real.exp (-β * energy J τ) := by
  sorry

-- MILESTONE (optional: change or delete)
/-- H095's result, here via `sum_snoc` with `g := fun _ => 1`. -/
theorem Z_eq (β J : ℝ) (n : ℕ) : Z β J n = 2 * (2 * Real.cosh (β * J)) ^ n := by
  sorry

-- MILESTONE (optional: change or delete)
/-- End-to-end numerator `∑_σ s₀ s_n e^{-βE}`. -/
theorem G_eq (β J : ℝ) (n : ℕ) :
    ∑ σ : Fin (n + 1) → Bool, spin (σ 0) * spin (σ (Fin.last n)) * Real.exp (-β * energy J σ) =
      2 * (2 * Real.sinh (β * J)) ^ n := by
  sorry

-- MILESTONE (optional: change or delete)
theorem corr_succ (β J : ℝ) (n r : ℕ) (hr : r ≤ n) :
    corr β J (n + 1) r (by omega) = corr β J n r hr := by
  sorry

-- BEGIN SPEC
theorem corr_eq (β J : ℝ) (n r : ℕ) (hr : r ≤ n) :
    corr β J n r hr = Real.tanh (β * J) ^ r :=
-- END SPEC
  sorry

end H096

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two facts: adding spins beyond site `r` multiplies numerator and `Z` by the same `2 cosh βJ`
    (so `corr` does not depend on `n`), and at `n = r` the numerator is `2 (2 sinh βJ)^r` while
    `Z = 2 (2 cosh βJ)^r` (`Z_eq`, H095's theorem: `sum_snoc` with `g := fun _ => 1` and induction on `n`).
H2. `snoc_split`: first state and prove a helper `energy_snoc (J : ℝ) {n : ℕ} (σ : Fin (n + 1) → Bool)
    (b : Bool) : energy J (Fin.snoc σ b : Fin (n + 2) → Bool) = energy J σ - J * (spin (σ (Fin.last n)) * spin b)`
    (recipe in H3). Then `rw [← (Fin.snocEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]`,
    and per term `show` the `Fin.snoc τ b` form and use `Fin.snoc_castSucc`, `Fin.snoc_last`,
    `energy_snoc`, `Real.exp_add`. The inner `∑ b : Bool` is `2 cosh K` or `2 sinh K · s` once
    `s = spin (τ (Fin.last n))` is known to be `±1` (`rcases ... with rfl | rfl <;> simp [spin, ...]`).
H3. `energy_snoc`: `simp only [energy, Fin.sum_univ_castSucc]` then
    `simp only [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]; ring`.
    Main: `induction n, hr using Nat.le_induction`; base: rewrite `⟨r, _⟩` to `Fin.last r` (`rfl`),
    then `rw [G_eq, Z_eq, Real.tanh_eq_sinh_div_cosh, div_pow]`;
    `have hc : 0 < Real.cosh (β * J) := Real.cosh_pos _`; `field_simp; ring`; step: `corr_succ`.
-/
