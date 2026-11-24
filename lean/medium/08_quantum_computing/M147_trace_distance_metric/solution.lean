/- M147 | Trace distance is a unitarily invariant metric | 10-15 min | TrDistance, traceNorm, uConj, MState.ext_m, classical instances, physlib
GOAL
  The trace distance `T(ρ, σ) = ½‖ρ - σ‖₁` on density matrices is a metric (it vanishes exactly on the
  diagonal and satisfies the triangle inequality) and does not change when both states are rotated by `U`.

REFERENCE
  -- `ρ : MState d` is a density matrix, `ρ.m : Matrix d d ℂ` its matrix; `U : 𝐔[d]` a unitary, `(U : Matrix d d ℂ)`.
  #check TrDistance                 -- TrDistance ρ σ = 1 / 2 * (ρ.m - σ.m).traceNorm   (`unfold TrDistance`)
  #check Matrix.traceNorm_nonneg    -- 0 ≤ A.traceNorm      (‖A‖₁ = sum of the singular values of A)
  #check Matrix.traceNorm_zero_iff  -- A.traceNorm = 0 ↔ A = 0
  #check Matrix.traceNorm_add_le    -- (A + B).traceNorm ≤ A.traceNorm + B.traceNorm
  #check Matrix.traceNorm_unitary_conj  -- (U * A * Uᴴ).traceNorm = A.traceNorm   (see NOTE)
  #check MState.ext_m               -- ρ₁.m = ρ₂.m → ρ₁ = ρ₂
  #check sub_add_sub_cancel         -- a - b + (b - c) = a - c
  -- `ρ.uConj U` is `U ρ U†`. Expose its matrix: `simp only [MState.uConj, MState.m, HermitianMat.conj_apply_mat]`
  #check Matrix.sub_mul             -- (M - M') * N = M * N - M' * N    (and `Matrix.mul_sub`)
NOTE: `traceNorm_unitary_conj` uses a classical `DecidableEq`; apply it via `classical; have := traceNorm_unitary_conj (A := A) (U := ⟨U.val, by convert U.2 <;> rfl⟩); simpa using this`.
-/
import QuantumInfo.States.Mixed.TraceDistance
import QuantumInfo.Operators.Unitary

open Matrix

namespace M147

-- WHY: `traceNorm_unitary_conj` lives under `open Classical`, so its unitary group uses a different
-- `DecidableEq d` instance than ours; rebuild `U` there and let `simpa` match the two.
theorem traceNorm_conj {d : Type} [Fintype d] [DecidableEq d] (U : 𝐔[d]) (A : Matrix d d ℂ) :
    ((U : Matrix d d ℂ) * A * (U : Matrix d d ℂ)ᴴ).traceNorm = A.traceNorm := by
  classical
  have := traceNorm_unitary_conj (A := A) (U := ⟨U.val, by convert U.2 <;> rfl⟩)
  simpa using this

-- BEGIN SPEC
theorem td_eq_zero_iff {d : Type} [Fintype d] [DecidableEq d] (ρ σ : MState d) :
    TrDistance ρ σ = 0 ↔ ρ = σ :=
-- END SPEC
  by
    constructor
    · intro h
      apply MState.ext_m
      rw [← sub_eq_zero, ← traceNorm_zero_iff]
      unfold TrDistance at h
      linarith [traceNorm_nonneg (ρ.m - σ.m)]
    · rintro rfl
      simp [TrDistance]

-- BEGIN SPEC
theorem td_triangle {d : Type} [Fintype d] [DecidableEq d] (ρ σ τ : MState d) :
    TrDistance ρ τ ≤ TrDistance ρ σ + TrDistance σ τ :=
-- END SPEC
  by
    have := traceNorm_add_le (ρ.m - σ.m) (σ.m - τ.m)
    rw [sub_add_sub_cancel] at this
    unfold TrDistance
    linarith

-- BEGIN SPEC
theorem td_unitary {d : Type} [Fintype d] [DecidableEq d] (ρ σ : MState d) (U : 𝐔[d]) :
    TrDistance (ρ.uConj U) (σ.uConj U) = TrDistance ρ σ :=
-- END SPEC
  by
    simp only [TrDistance, MState.uConj, MState.m, HermitianMat.conj_apply_mat]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, traceNorm_conj U]

end M147

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each part is one trace-norm fact about the difference matrix `ρ.m - σ.m`, wrapped in `TrDistance`'s `1 / 2 * …`.
H2. Zero: `ρ = σ` follows from `ρ.m - σ.m = 0` (`MState.ext_m`, `sub_eq_zero`, `traceNorm_zero_iff`); the factor
    `1 / 2` goes away with `linarith`. Triangle: apply `traceNorm_add_le` to `ρ.m - σ.m` and `σ.m - τ.m`.
    Unitary: after exposing the matrices, factor `U * ρ.m * Uᴴ - U * σ.m * Uᴴ` as `U * (ρ.m - σ.m) * Uᴴ`.
H3. Triangle: `have := traceNorm_add_le (ρ.m - σ.m) (σ.m - τ.m); rw [sub_add_sub_cancel] at this; unfold TrDistance; linarith`.
    Unitary: `rw [← Matrix.sub_mul, ← Matrix.mul_sub]`, then the NOTE's idiom with `A := ρ.M.mat - σ.M.mat`.
-/
