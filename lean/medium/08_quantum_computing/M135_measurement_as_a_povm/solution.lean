/- M135 | Measurement as a POVM | 15-20 min | POVM, HermitianMat, Born rule, physlib
GOAL
  The basis projectors `Pᵢ = |i⟩⟨i|` are positive semidefinite and sum to the identity, so they form a
  POVM (`POVM d d` = structure `⟨mats, nonneg, normalized⟩`). Measuring a state `ρ` with it gives
  outcome `i` with probability `ρᵢᵢ` (Born rule).

GUIDE
  Entries R1–R28: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import QuantumInfo.Measurements.POVM

open scoped Matrix ComplexOrder

namespace M135

-- BEGIN SPEC
/-- The projector `|i⟩⟨i|`: the diagonal matrix with a single `1` at position `(i, i)`. -/
noncomputable def zMats {d : Type} [Fintype d] [DecidableEq d] (i : d) : HermitianMat d ℂ :=
  HermitianMat.diagonal ℂ (fun j => if j = i then 1 else 0)
-- END SPEC

/- SKELETON · zMats_nonneg
  1. `0 ≤ _` on `HermitianMat` → `PosSemidef` of the underlying matrix:      R1
  2. Unfold `zMats`, then take its matrix:                                   R2, R3
  3. A diagonal matrix is PSD iff every diagonal entry is `≥ 0`:            R4
  4. Fix the entry `j`, split the `if`:                                      R5, R6
  5. Each branch is `0 ≤ ↑1` or `0 ≤ ↑0` in `ℂ`: `simp`                     R7
-/
-- BEGIN SPEC
theorem zMats_nonneg {d : Type} [Fintype d] [DecidableEq d] (i : d) : 0 ≤ zMats (d := d) i :=
-- END SPEC
  by
    rw [HermitianMat.zero_le_iff, zMats, HermitianMat.diagonal_mat, Matrix.posSemidef_diagonal_iff]
    intro j
    split_ifs <;> simp

/- SKELETON · zMats_sum
  1. Equal Hermitian matrices ← equal underlying matrices:                    R8
  2. Push `↑` inside the sum:                                                  R9
  3. Matrix equation → one entry `a b`:                                        R10
  4. One `simp` naming the unfolds and entry lemmas it needs:
       unfold `zMats` and its matrix                                           R2, R3
       entries of `∑`, of `diagonal`, of `1`                                   R11, R12, R13
     `simp` then finishes by itself: cast of the `if`, then the delta sum      R14 → R15 → R16 → R17, R18
-/
-- BEGIN SPEC
theorem zMats_sum {d : Type} [Fintype d] [DecidableEq d] : ∑ i, zMats (d := d) i = 1 :=
-- END SPEC
  by
    ext1
    rw [HermitianMat.mat_finset_sum]
    ext a b
    simp [zMats, HermitianMat.diagonal_mat, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]

/- SKELETON · z_born   (needs zMats_nonneg and zMats_sum proved: they are fields of the POVM)
  1. Unfold the measurement down to `inner ℝ (zMats i) ↑ρ = (ρ.m i i).re`:      R19 → R20 → R21
  2. Inner product → `RCLike.re (↑(zMats i) * ↑↑ρ).trace`:                      R22
  3. Unfold `zMats` and its matrix:                                             R2, R3
  4. Evaluate the trace: `simp` with `Matrix.trace` and `Matrix.diagonal_mul`.
     Trace → sum, diagonal row scaling, `↑↑ρ` → `ρ.m`:                         R23, R24, R25
     `↑(if …) * ρ.m x x` → delta sum → `ρ.m i i`:                              R14, R26 → R27 → R17
     `RCLike.re` → `.re`:                                                       R28
     (Steps 1–3 can also go into that one `simp` call.)
-/
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
    `HermitianMat.diagonal_mat` (R3). For `z_born`, the POVM probability is `re tr(Pᵢ ρ)`, and
    `Pᵢ` diagonal makes the trace a sum with a single surviving term `x = i`.
H2. `zMats_nonneg`: `0 ≤ _` → `PosSemidef` → "every diagonal entry ≥ 0", then split the `if` (R1–R7).
    `zMats_sum`: `ext1`, push `↑` inside the sum, compare entries `a b`, then one `simp` (R8–R18).
    `z_born`: unfold `POVM.measure` to `inner ℝ (zMats i) ↑ρ`, turn it into a trace, evaluate (R19–R28).
H3. `rw [HermitianMat.zero_le_iff, zMats, HermitianMat.diagonal_mat, Matrix.posSemidef_diagonal_iff]`;
    `ext1; rw [HermitianMat.mat_finset_sum]; ext a b; simp [zMats, HermitianMat.diagonal_mat,
    Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]`; and for `z_born`
    `simp [POVM.measure, ProbDistribution.mk', HermitianMat.inner_eq_re_trace, zMats, …, Matrix.trace]`.
-/
