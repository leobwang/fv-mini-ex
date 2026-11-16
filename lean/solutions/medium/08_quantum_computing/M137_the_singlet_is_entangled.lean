/- M137 | The singlet is entangled | 10-15 min | Ket.IsEntangled, Ket.prod, rintro, physlib
GOAL
  The singlet `(|01⟩ − |10⟩)/√2` on two qubits is entangled: it is not a product `ξ ⊗ φ` of
  one-qubit kets.

REFERENCE
  -- context for the examples: `variable (ψ : Ket (Fin 2 × Fin 2)) (ξ φ : Ket (Fin 2))`
  example : ψ.IsEntangled ↔ ¬ ψ.IsProd := Iff.rfl
  example : ψ.IsProd ↔ ∃ ξ φ, ψ = ξ ⊗ᵠ φ := Iff.rfl     -- `⊗ᵠ` is `Ket.prod`
  example (i j : Fin 2) : (ξ ⊗ᵠ φ) (i, j) = ξ i * φ j := rfl   -- `ψ i` means `ψ.vec i` (`Ket.apply`)
  example (z w : ℂ) (h : z * w = 1) (hz : z = 0) : False := by simp [hz] at h   -- `simp at h` closes `0 = 1`
  example (h : ψ = ξ ⊗ᵠ φ) : ψ (0, 1) = (ξ ⊗ᵠ φ) (0, 1) := congrArg (fun χ : Ket _ => χ (0, 1)) h
  #check mul_eq_zero   -- a * b = 0 ↔ a = 0 ∨ b = 0
  -- `rintro ⟨ξ, φ, h⟩` introduces a negated `∃` and destructs it in one go
BANNED: Ket.IsProd_iff_mul_eq_mul, IsProd_iff_rank_eq_one
-/
import QuantumInfo.States.Pure.Braket

namespace M137

-- BEGIN SPEC
/-- The singlet `(|01⟩ − |10⟩)/√2`; its normalisation is proved for you. -/
noncomputable def singlet : Ket (Fin 2 × Fin 2) where
  vec := fun p => if p = (0, 1) then 1 / Real.sqrt 2 else if p = (1, 0) then -1 / Real.sqrt 2 else 0
  normalized' := by
    simp [Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num
-- END SPEC

-- BEGIN SPEC
theorem singlet_entangled : singlet.IsEntangled :=
-- END SPEC
  by
    rintro ⟨ξ, φ, h⟩
    have h01 := congrArg (fun ψ : Ket _ => ψ (0, 1)) h
    have h10 := congrArg (fun ψ : Ket _ => ψ (1, 0)) h
    have h00 := congrArg (fun ψ : Ket _ => ψ (0, 0)) h
    simp [singlet, Ket.prod, Ket.apply] at h01 h10 h00
    rcases h00 with h | h <;> simp [h] at h01 h10

end M137

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Suppose `singlet = ξ ⊗ φ`. Compare amplitudes: `ξ₀φ₁ = 1/√2`, `ξ₁φ₀ = −1/√2`, but `ξ₀φ₀ = 0`.
H2. `rintro ⟨ξ, φ, h⟩`, then evaluate `h` at the basis states `(0, 1)`, `(1, 0)`, `(0, 0)` with
    `congrArg`, and `simp [singlet, Ket.prod, Ket.apply] at …` to turn them into equations in ℂ.
H3. After the `simp`, the `(0, 0)` equation reads `ξ 0 = 0 ∨ φ 0 = 0`;
    `rcases h00 with h | h <;> simp [h] at h01 h10`.
-/
