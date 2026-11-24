/- M147 | Trace distance is a unitarily invariant metric | 10-15 min | TrDistance, traceNorm, uConj, MState.ext_m, classical instances, physlib
GOAL
  The trace distance `T(ρ, σ) = ½‖ρ - σ‖₁` on density matrices is a metric (it vanishes exactly on the
  diagonal and satisfies the triangle inequality) and does not change when both states are rotated by `U`.

GUIDE
  Entries R1–R20: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import QuantumInfo.States.Mixed.TraceDistance
import QuantumInfo.Operators.Unitary

open Matrix

namespace M147

-- WHY: `traceNorm_unitary_conj` states its unitary group with a classical `DecidableEq d` and with the
-- ring/star structure of `ℂ` taken through `RCLike`, so it does not match our `𝐔[d]` syntactically;
-- rebuild `U` there (`convert` + `rfl` close the instance equations) and let `simpa` erase the rebuild.
theorem traceNorm_conj {d : Type} [Fintype d] [DecidableEq d] (U : 𝐔[d]) (A : Matrix d d ℂ) :
    ((U : Matrix d d ℂ) * A * (U : Matrix d d ℂ)ᴴ).traceNorm = A.traceNorm := by
  classical
  have := traceNorm_unitary_conj (A := A) (U := ⟨U.val, by convert U.2 <;> rfl⟩)
  simpa using this

/- SKELETON · td_eq_zero_iff
  1. Split the iff into `mp` and `mpr`:                                     R1
  2. mp: `intro h`, then turn `ρ = σ` into a statement about the trace norm
       states → matrices → difference = 0 → trace norm = 0:                R2 → R3 → R4
       unfold the distance in `h`:                                          R5
       close with linear arithmetic, passing the sign of the trace norm:    R6 inside R7
  3. mpr: substitute `σ := ρ`, then unfold and simplify:                    R8, then R9 (`simp [TrDistance]`)
-/
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

/- SKELETON · td_triangle
  1. Triangle inequality on the two differences `ρ.m - σ.m`, `σ.m - τ.m`:  R10
  2. Collapse their sum to `ρ.m - τ.m` inside `this`:                       R11
  3. Unfold the three distances in the goal:                                R12
  4. Multiply `this` by `1 / 2`, i.e. close with:                           R7 (plain `linarith`)
-/
-- BEGIN SPEC
theorem td_triangle {d : Type} [Fintype d] [DecidableEq d] (ρ σ τ : MState d) :
    TrDistance ρ τ ≤ TrDistance ρ σ + TrDistance σ τ :=
-- END SPEC
  by
    have := traceNorm_add_le (ρ.m - σ.m) (σ.m - τ.m)
    rw [sub_add_sub_cancel] at this
    unfold TrDistance
    linarith

/- SKELETON · td_unitary
  1. MILESTONE first (a `have` here, or a helper lemma above this theorem):
       key : ∀ A : Matrix d d ℂ, ((U : Matrix d d ℂ) * A * (U : Matrix d d ℂ)ᴴ).traceNorm = A.traceNorm
     proof: `intro A`; rebuild `U` for the library lemma, then erase it:   R18 (with R20 inside) → R19
  2. Expose the matrices on both sides, in one `simp only`:                 R12, R13, R14, R15
  3. Factor `U _ Uᴴ - U _ Uᴴ` into `U (_ - _) Uᴴ`, right factor first:      R16 → R17
  4. Use the milestone; the goal then closes by itself:                     rw [key]
-/
-- BEGIN SPEC
theorem td_unitary {d : Type} [Fintype d] [DecidableEq d] (ρ σ : MState d) (U : 𝐔[d]) :
    TrDistance (ρ.uConj U) (σ.uConj U) = TrDistance ρ σ :=
-- END SPEC
  by
    simp only [TrDistance, MState.uConj, MState.m, HermitianMat.conj_apply_mat]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, traceNorm_conj U]

end M147

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each part is one trace-norm fact about the difference matrix `ρ.m - σ.m`, wrapped in `TrDistance`'s
    `1 / 2 * …`: `‖A‖₁ = 0 ↔ A = 0` (with `0 ≤ ‖A‖₁`), `‖A + B‖₁ ≤ ‖A‖₁ + ‖B‖₁`, `‖U A U†‖₁ = ‖A‖₁`.
H2. Zero: `constructor`; for `mp` go from `ρ = σ` back to `(ρ.m - σ.m).traceNorm = 0` with `MState.ext_m`,
    `← sub_eq_zero`, `← traceNorm_zero_iff`, then `linarith` removes the `1 / 2`; for `mpr`, `rintro rfl`.
    Triangle: `traceNorm_add_le` on `ρ.m - σ.m` and `σ.m - τ.m`, then `linarith`. Unitary: prove the
    milestone `key` first, expose the matrices with `simp only`, and factor `U (ρ - σ) Uᴴ`.
H3. Triangle: `have := traceNorm_add_le (ρ.m - σ.m) (σ.m - τ.m); rw [sub_add_sub_cancel] at this; unfold TrDistance; linarith`.
    Key: `have := traceNorm_unitary_conj (A := A) (U := ⟨U.val, by convert U.2 <;> rfl⟩); simpa using this`.
    Unitary: `simp only [TrDistance, MState.uConj, MState.m, HermitianMat.conj_apply_mat]`, then
    `rw [← Matrix.sub_mul, ← Matrix.mul_sub, key]`.
-/
