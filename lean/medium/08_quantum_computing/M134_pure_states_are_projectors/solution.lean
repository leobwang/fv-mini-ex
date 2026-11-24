/- M134 | Pure states are projectors | 10-15 min | MState, pure, Finset sums, physlib
GOAL
  The density matrix `ρ = |ψ⟩⟨ψ|` of a normalised ket `ψ` (in QuantumInfo: `(MState.pure ψ).m`,
  a `Matrix d d ℂ`) is a projector: `ρ * ρ = ρ`. Prove it entrywise from normalisation.

BANNED: MState.pure_mul_self, Matrix.vecMulVec_mul_vecMulVec, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMulVec_mulVec, Matrix.vecMul_vecMulVec, try?

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import QuantumInfo.States.Mixed.MState

namespace M134

/- SKELETON · pure_idempotent
  On paper: (ρρ)ᵢⱼ = ∑ₖ ψᵢ ψ̄ₖ · ψₖ ψ̄ⱼ = ψᵢ (∑ₖ ψ̄ₖ ψₖ) ψ̄ⱼ = ψᵢ · 1 · ψ̄ⱼ = ρᵢⱼ   (ψ̄ = conj ψ).
  1. Matrix equation → entry (i, j):                                         R1
  2. Expand the product entry and the pure-state entries, under the `∑`:      R2, R3 (one `simp only`)
  3. Normalisation in ℂ, a `have` (TACTIC_STATES, "Adding facts"):
       h : ∑ k, (starRingEnd ℂ) (ψ k) * ψ k = 1
     proof: R4 → R5 → R6
  4. A two-step `calc` (R7) from the goal's left side:
       _ = ψ i * (∑ k, (starRingEnd ℂ) (ψ k) * ψ k) * (starRingEnd ℂ) (ψ j)
            pull the factors into the sum on the right, compare summands:   R8 → R9 → R10 → R11 → R12
       _ = ψ i * (starRingEnd ℂ) (ψ j)
            use step 3:                                                     rw [h], R13
-/
-- BEGIN SPEC
theorem pure_idempotent {d : Type} [Fintype d] [DecidableEq d] (ψ : Ket d) :
    (MState.pure ψ).m * (MState.pure ψ).m = (MState.pure ψ).m :=
-- END SPEC
  by
    ext i j
    simp only [Matrix.mul_apply, MState.pure_apply]
    have h : ∑ k, (starRingEnd ℂ) (ψ k) * ψ k = 1 := by
      have := ψ.normalized'
      simp only [Complex.conj_mul']
      exact_mod_cast this
    calc ∑ k, ψ i * (starRingEnd ℂ) (ψ k) * (ψ k * (starRingEnd ℂ) (ψ j))
        = ψ i * (∑ k, (starRingEnd ℂ) (ψ k) * ψ k) * (starRingEnd ℂ) (ψ j) := by
          rw [Finset.mul_sum, Finset.sum_mul]; congr 1; ext k; ring
      _ = ψ i * (starRingEnd ℂ) (ψ j) := by rw [h, mul_one]

end M134

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Entry `(i, j)` of `ρ * ρ` is `∑ k, ψᵢ conj(ψₖ) ψₖ conj(ψⱼ)`. Pull `ψᵢ` and `conj ψⱼ` out of the
    sum; what is left is `∑ k, conj(ψₖ) ψₖ = ∑ k, |ψₖ|²`, which normalisation says is 1.
H2. As in the SKELETON: `ext i j` and one `simp only` (R1–R3); a `have h` for the normalised sum
    in `ℂ` (R4–R6); then a `calc` whose middle term has the sum between `ψ i` and `conj (ψ j)`.
H3. The `calc` middle term is `ψ i * (∑ k, (starRingEnd ℂ) (ψ k) * ψ k) * (starRingEnd ℂ) (ψ j)`.
    Step 1 starts with `rw [Finset.mul_sum, Finset.sum_mul]`, then compares summands (R10–R12);
    step 2 is `rw [h, mul_one]`. `h` comes from `ψ.normalized'` by R5, then `exact_mod_cast` (R6).
-/
