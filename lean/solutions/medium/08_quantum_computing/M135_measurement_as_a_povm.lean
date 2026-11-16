/- M135 | Measurement as a POVM | 15-20 min | POVM, HermitianMat, Born rule, physlib
GOAL
  The basis projectors `Pᵢ = |i⟩⟨i|` are positive semidefinite and sum to the identity, so they form a
  POVM (`POVM d d` = structure `⟨mats, nonneg, normalized⟩`). Measuring a state `ρ` with it gives
  outcome `i` with probability `ρᵢᵢ` (Born rule).

REFERENCE
  -- context for the examples: `variable {d : Type} [Fintype d] [DecidableEq d]`
  example (A : HermitianMat d ℂ) : Matrix d d ℂ := A.mat   -- subtype of Hermitian matrices; `.mat` = `↑A`
  example (f : d → ℝ) : (HermitianMat.diagonal ℂ f).mat = Matrix.diagonal (fun i => (f i : ℂ)) :=
    HermitianMat.diagonal_mat f
  example (A : HermitianMat d ℂ) : 0 ≤ A ↔ A.mat.PosSemidef := HermitianMat.zero_le_iff
  #check Matrix.posSemidef_diagonal_iff   -- (diagonal v).PosSemidef ↔ ∀ i, 0 ≤ v i
  example (A B : HermitianMat d ℂ) (h : A.mat = B.mat) : A = B := by ext1; exact h
  #check HermitianMat.mat_finset_sum      -- (∑ i ∈ s, f i).mat = ∑ i ∈ s, (f i).mat
  example (Λ : POVM d d) (ρ : MState d) (i : d) : (Λ.measure ρ i : ℝ) = inner ℝ (Λ.mats i) ρ.M := rfl
  #check HermitianMat.inner_eq_re_trace   -- inner ℝ A B = re (A.mat * B.mat).trace
  #check Matrix.diagonal_mul              -- (diagonal v * M) i j = v i * M i j
  example (ρ : MState d) (A : Matrix d d ℂ) : ρ.M.mat = ρ.m ∧ A.trace = ∑ i, A i i := ⟨rfl, rfl⟩
-/
import QuantumInfo.Measurements.POVM

open scoped Matrix ComplexOrder

namespace M135

-- BEGIN SPEC
/-- The projector `|i⟩⟨i|`: the diagonal matrix with a single `1` at position `(i, i)`. -/
noncomputable def zMats {d : Type} [Fintype d] [DecidableEq d] (i : d) : HermitianMat d ℂ :=
  HermitianMat.diagonal ℂ (fun j => if j = i then 1 else 0)
-- END SPEC

-- BEGIN SPEC
theorem zMats_nonneg {d : Type} [Fintype d] [DecidableEq d] (i : d) : 0 ≤ zMats (d := d) i :=
-- END SPEC
  by
    rw [HermitianMat.zero_le_iff, zMats, HermitianMat.diagonal_mat, Matrix.posSemidef_diagonal_iff]
    intro j
    split_ifs <;> simp

-- BEGIN SPEC
theorem zMats_sum {d : Type} [Fintype d] [DecidableEq d] : ∑ i, zMats (d := d) i = 1 :=
-- END SPEC
  by
    ext1
    rw [HermitianMat.mat_finset_sum]
    ext a b
    simp [zMats, HermitianMat.diagonal_mat, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]

-- BEGIN SPEC
theorem z_born {d : Type} [Fintype d] [DecidableEq d] (ρ : MState d) (i : d) :
    ((⟨zMats, zMats_nonneg, zMats_sum⟩ : POVM d d).measure ρ i : ℝ) = (ρ.m i i).re :=
-- END SPEC
  by
    simp [POVM.measure, ProbDistribution.mk', HermitianMat.inner_eq_re_trace, zMats,
      HermitianMat.diagonal_mat, Matrix.trace, Matrix.diagonal_mul]

end M135

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. All three facts are about diagonal matrices once you unwrap the `HermitianMat` subtype with
    `HermitianMat.diagonal_mat`. For `z_born`, the POVM probability is `re (Pᵢ * ρ).trace`.
H2. `zMats_nonneg`: turn `0 ≤ _` into `PosSemidef`, then into "every diagonal entry ≥ 0", and split
    the `if`. `zMats_sum`: `ext1`, push `.mat` inside the sum, compare entries `a b`.
    `z_born`: unfold `POVM.measure` (its value is `inner ℝ (zMats i) ρ.M`), then the trace.
H3. `rw [HermitianMat.zero_le_iff, zMats, HermitianMat.diagonal_mat, Matrix.posSemidef_diagonal_iff]`;
    `ext1; rw [HermitianMat.mat_finset_sum]; ext a b; simp [zMats, HermitianMat.diagonal_mat,
    Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]`; and for `z_born`
    `simp [POVM.measure, ProbDistribution.mk', HermitianMat.inner_eq_re_trace, zMats, …, Matrix.trace]`.
-/
