/- M137 | The singlet is entangled | 10-15 min | Ket.IsEntangled, Ket.prod, rintro, physlib
GOAL
  The singlet `(|01⟩ − |10⟩)/√2` on two qubits is entangled: it is not a product `ξ ⊗ φ` of
  one-qubit kets.
BANNED: Ket.IsProd_iff_mul_eq_mul, IsProd_iff_rank_eq_one

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · singlet_entangled
  1. Assume a product decomposition (R1 only shows what `IsEntangled` means):   R1, R2
       ξ φ : Ket (Fin 2),  h : singlet = ξ ⊗ᵠ φ  ⊢ False
  2. Evaluate `h` at the three basis states (0, 1), (1, 0), (0, 0):             R3 three times
       h01 : singlet (0, 1) = (ξ ⊗ᵠ φ) (0, 1),  likewise h10, h00
  3. One `simp` at h01 h10 h00 with `singlet, Ket.prod, Ket.apply`;
     it applies R4 → R5, R6 → R7, and prints with R8, R9:                       R4–R9
       h01 : (↑√2)⁻¹ = ξ.vec 0 * φ.vec 1
       h10 : -1 / ↑√2 = ξ.vec 1 * φ.vec 0
       h00 : ξ.vec 0 = 0 ∨ φ.vec 0 = 0
  4. Split h00, then in both goals (`<;>`) substitute the zero into h01 h10;
     one of them becomes `… = 0` and closes the goal:                            R10, then R11 → R12
-/
-- BEGIN SPEC
theorem singlet_entangled : singlet.IsEntangled :=
-- END SPEC
  sorry

end M137

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Suppose `singlet = ξ ⊗ φ`. Compare amplitudes: `ξ₀φ₁ = 1/√2`, `ξ₁φ₀ = −1/√2`, but `ξ₀φ₀ = 0`,
    so `ξ₀ = 0` or `φ₀ = 0`, and either one kills a nonzero amplitude.
H2. `rintro ⟨ξ, φ, h⟩` (R2); then `have h01 := congrArg (fun ψ : Ket _ => ψ (0, 1)) h` (R3), likewise
    at `(1, 0)` and `(0, 0)`; then `simp [singlet, Ket.prod, Ket.apply] at h01 h10 h00` (R4–R9).
H3. After that `simp`, `h00 : ξ.vec 0 = 0 ∨ φ.vec 0 = 0`; finish with
    `rcases h00 with h | h <;> simp [h] at h01 h10` (R10, R11, R12).
-/
