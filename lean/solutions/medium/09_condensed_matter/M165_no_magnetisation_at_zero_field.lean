/- M165 | No magnetisation at zero field | 15 min | Equiv, Equiv.sum_comp, involution, spin flip, mathlib
GOAL
  At zero field the open-chain energy `E = energy J`, `E(σ) = -J ∑_i s(σ i) s(σ (i+1))` with spin value
  `s = spin` (`true ↦ +1`, `false ↦ -1`), is unchanged by flipping every spin. Hence at inverse temperature
  `β` the unnormalised magnetisation of any site `k` vanishes: `∑_σ s(σ k) · exp (-β E(σ)) = 0`.

REFERENCE
  example : Bool ≃ Bool := ⟨fun b => !b, fun b => !b, fun b => by simp, fun b => by simp⟩
  -- an `Equiv` is ⟨toFun, invFun, left_inv, right_inv⟩; for functions use `funext i; simp` in the laws
  #check Equiv.sum_comp          -- (e : ι ≃ κ) (g : κ → M) : ∑ i, g (e i) = ∑ i, g i   (reindexing)
  #check Equiv.coe_fn_mk         -- ⇑⟨f, g, l, r⟩ = f   (lets `simp only` evaluate your Equiv)
  #check Finset.sum_neg_distrib  -- ∑ x ∈ s, -f x = -∑ x ∈ s, f x
  #check neg_mul_neg             -- -a * -b = a * b
  example (b : Bool) : (!!b) = b := by cases b <;> rfl
  example (S : ℝ) (h : S = -S) : S = 0 := by linarith
-/
import Mathlib

namespace M165

-- BEGIN SPEC
/-- Ising spin value of a site: `true ↦ +1`, `false ↦ -1`. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- Zero-field energy of an open chain of `n + 1` spins with coupling `J`. -/
noncomputable def energy (J : ℝ) {n : ℕ} (σ : Fin (n + 1) → Bool) : ℝ :=
  -J * ∑ i : Fin n, spin (σ i.castSucc) * spin (σ i.succ)
-- END SPEC

-- BEGIN SPEC
theorem no_magnetization (β J : ℝ) (n : ℕ) (k : Fin (n + 1)) :
    ∑ σ : Fin (n + 1) → Bool, spin (σ k) * Real.exp (-β * energy J σ) = 0 :=
-- END SPEC
  by
    let flip : (Fin (n + 1) → Bool) ≃ (Fin (n + 1) → Bool) :=
      ⟨fun σ i => !σ i, fun σ i => !σ i, fun σ => by funext i; simp, fun σ => by funext i; simp⟩
    have hs : ∀ b : Bool, spin (!b) = -spin b := by
      intro b; cases b <;> simp [spin]
    have hE : ∀ σ, energy J (flip σ) = energy J σ := by
      intro σ; simp only [energy, flip, Equiv.coe_fn_mk, hs, neg_mul_neg]
    have h2 : ∀ σ, spin (flip σ k) * Real.exp (-β * energy J (flip σ)) =
        -(spin (σ k) * Real.exp (-β * energy J σ)) := by
      intro σ; rw [hE]; simp only [flip, Equiv.coe_fn_mk, hs, neg_mul]
    have h := Equiv.sum_comp flip (fun σ => spin (σ k) * Real.exp (-β * energy J σ))
    simp only [h2, Finset.sum_neg_distrib] at h
    linarith

end M165

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Build the global spin flip `σ ↦ (fun i => !σ i)` as an `Equiv` of configurations (it is its own
    inverse). Reindexing the sum by it leaves the sum unchanged.
H2. Two facts: `spin (!b) = -spin b` (case on `b`), so `energy J (flip σ) = energy J σ` (each bond
    product picks up two signs). Hence each flipped term is minus the original, so `S = -S`.
H3. `let flip : (Fin (n + 1) → Bool) ≃ (Fin (n + 1) → Bool) := ⟨fun σ i => !σ i, fun σ i => !σ i,
    fun σ => by funext i; simp, fun σ => by funext i; simp⟩`; then
    `have h := Equiv.sum_comp flip (fun σ => spin (σ k) * Real.exp (-β * energy J σ))`; with
    `h2 : ∀ σ, <term at flip σ> = -<term at σ>`, finish by `simp only [h2, Finset.sum_neg_distrib] at h; linarith`.
-/
