/- M134 | Pure states are projectors | 10-15 min | MState, pure, Finset sums, physlib
GOAL
  The density matrix `ρ = |ψ⟩⟨ψ|` of a normalised ket `ψ` (in QuantumInfo: `(MState.pure ψ).m`,
  a `Matrix d d ℂ`) is a projector: `ρ * ρ = ρ`. Prove it entrywise from normalisation.

REFERENCE
  -- context for the examples: `variable {d : Type} [Fintype d] [DecidableEq d]`
  example (ψ : Ket d) (i j : d) : (MState.pure ψ).m i j = ψ i * (starRingEnd ℂ) (ψ j) :=
    MState.pure_apply ψ                          -- ρᵢⱼ = ψᵢ · conj ψⱼ  (`starRingEnd ℂ` = conj)
  example (A B : Matrix d d ℂ) (i k : d) : (A * B) i k = ∑ j, A i j * B j k := Matrix.mul_apply
  example (ψ : Ket d) : ∑ i, ‖ψ.vec i‖ ^ 2 = 1 := ψ.normalized'   -- `ψ i` is `ψ.vec i`
  #check Complex.conj_mul'   -- conj z * z = ‖z‖ ^ 2
  #check Finset.mul_sum      -- a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i   (and `Finset.sum_mul`)
  example (A B : Matrix d d ℂ) (h : ∀ i j, A i j = B i j) : A = B := by ext i j; exact h i j
BANNED: MState.pure_mul_self, Matrix.vecMulVec_mul_vecMulVec, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMulVec_mulVec, Matrix.vecMul_vecMulVec, try?
NOTE: prove it entrywise; the library's rank-one (`vecMulVec`) product lemmas are off limits.
-/
import QuantumInfo.States.Mixed.MState

namespace M134

-- BEGIN SPEC
theorem pure_idempotent {d : Type} [Fintype d] [DecidableEq d] (ψ : Ket d) :
    (MState.pure ψ).m * (MState.pure ψ).m = (MState.pure ψ).m :=
-- END SPEC
  sorry

end M134

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Entry `(i, j)` of `ρ * ρ` is `∑ k, ψᵢ conj(ψₖ) ψₖ conj(ψⱼ)`. Pull `ψᵢ` and `conj ψⱼ` out of the
    sum; what is left is `∑ k, conj(ψₖ) ψₖ`, which normalisation says is 1.
H2. `ext i j; simp only [Matrix.mul_apply, MState.pure_apply]`. Separately prove
    `h : ∑ k, (starRingEnd ℂ) (ψ k) * ψ k = 1` from `ψ.normalized'` (rewrite with `Complex.conj_mul'`,
    then `exact_mod_cast`).
H3. `calc ∑ k, ψ i * conj (ψ k) * (ψ k * conj (ψ j))
        = ψ i * (∑ k, conj (ψ k) * ψ k) * conj (ψ j) := by rw [Finset.mul_sum, Finset.sum_mul]; …
      _ = _ := by rw [h, mul_one]`  (finish the first step with `congr 1; ext k; ring`).
-/
