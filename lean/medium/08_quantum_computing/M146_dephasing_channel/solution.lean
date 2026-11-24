/- M146 | The dephasing channel | 15 min | CPTPMap, Kraus form, MState, fin_cases, physlib
GOAL
  Build the qubit dephasing channel `ρ ↦ ∑ k, |k⟩⟨k| ρ |k⟩⟨k|` as a bundled channel from its Kraus
  operators: check `∑ k, (P k)ᴴ * P k = 1`, show the output is the diagonal of `ρ` (coherences erased,
  populations kept), and that dephasing twice is the same as dephasing once.

GUIDE
  Entries R1–R16: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import QuantumInfo.Channels.CPTP

open Matrix

namespace M146

/- SKELETON · dephase_tp
  1. Matrix equation → four entry goals:                                    R1, R2
  2. Evaluate each entry with one `simp`, naming `P` (to unfold the Kraus
     operators), `Fin.sum_univ_two` and `Pi.single_apply`. Inside, it does:
       (P k)ᴴ → P k                                                         R3, R4
       (P k)ᴴ * P k → one diagonal, its entries as `if`s                    R5, R6
       the sum over k, then the entry of the sum                            R7, R8, R9
       the right side `1 i j`                                               R10
-/
-- BEGIN SPEC
/-- Kraus operators `P 0 = |0⟩⟨0|` and `P 1 = |1⟩⟨1|` -/
def P (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal (Pi.single i 1)

theorem dephase_tp : ∑ k, (P k)ᴴ * P k = 1 :=
-- END SPEC
  by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [P, Fin.sum_univ_two, Pi.single_apply]

-- BEGIN SPEC
noncomputable def dephase : CPTPMap (Fin 2) (Fin 2) ℂ := CPTPMap.of_kraus_CPTPMap P dephase_tp
-- END SPEC

/-- bridge: the bundled channel acts on the matrix as its Kraus sum -/
theorem dephase_mat (ρ : MState (Fin 2)) : (dephase ρ).m = ∑ k, P k * ρ.m * (P k)ᴴ := by
  rw [CPTPMap.mat_coe_eq_apply_mat]
  -- WHY: `of_kraus_CPTPMap` stores `MatrixMap.of_kraus P P`, which unfolds to this sum
  rfl

/- SKELETON · dephase_apply
  0. FIRST, in the room above, prove a bridge lemma of your own (it is used in step 1):
       dephase_mat (ρ : MState (Fin 2)) : (dephase ρ).m = ∑ k, P k * ρ.m * (P k)ᴴ
     proof: R11 → R12
  1. Replace `(dephase ρ).m` by the Kraus sum:                              rw [dephase_mat]
  2. Matrix equation → four entry goals:                                    R1, R2
  3. Evaluate each entry with one `simp`, naming `P`, `Fin.sum_univ_two`
     and `Matrix.mul_apply`. Inside, it does:                               R3, R4, R7, R8, R13, R9, R14
-/
-- BEGIN SPEC
theorem dephase_apply (ρ : MState (Fin 2)) :
    (dephase ρ).m = Matrix.diagonal (fun i => ρ.m i i) :=
-- END SPEC
  by
    rw [dephase_mat]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [P, Fin.sum_univ_two, Matrix.mul_apply]

/- SKELETON · dephase_idem
  1. Equality of states → equality of matrices:                             R15
  2. Rewrite with `dephase_apply` twice: the first rewrite hits the outer
     `dephase`, the second the inner one (guide W2):                        rw [dephase_apply], twice
       goal: diagonal (fun i => diagonal (fun i => ρ.m i i) i i) = diagonal (fun i => ρ.m i i)
  3. Matrix equation → one entry goal:                                      R1
  4. Split on whether the entry is on the diagonal; `simp [h]` in both cases:  R16, then R9
-/
-- BEGIN SPEC
theorem dephase_idem (ρ : MState (Fin 2)) : dephase (dephase ρ) = dephase ρ :=
-- END SPEC
  by
    apply MState.ext_m
    rw [dephase_apply, dephase_apply]
    ext i j
    by_cases h : i = j <;> simp [h]

end M146

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Everything goes through the raw matrix `(dephase ρ).m`, never the bundled state `dephase ρ`. First prove
    a bridge lemma that writes it as the Kraus sum `∑ k, P k * ρ.m * (P k)ᴴ`; after that, `dephase_tp` and
    `dephase_apply` are 2×2 matrix arithmetic, entry by entry.
H2. `dephase_tp`, `dephase_apply` (after `rw` with the bridge): `ext i j; fin_cases i <;> fin_cases j`, then one
    `simp` that names `P` and the sum and entry lemmas. `dephase_idem`: `apply MState.ext_m`, `dephase_apply`
    twice, then compare entries and split on `i = j`.
H3. Bridge: `theorem dephase_mat (ρ : MState (Fin 2)) : (dephase ρ).m = ∑ k, P k * ρ.m * (P k)ᴴ`, proved by
    `rw [CPTPMap.mat_coe_eq_apply_mat]; rfl`. The `simp` sets: `simp [P, Fin.sum_univ_two, Pi.single_apply]`
    (`dephase_tp`) and `simp [P, Fin.sum_univ_two, Matrix.mul_apply]` (`dephase_apply`).
    `dephase_idem` ends with `ext i j; by_cases h : i = j <;> simp [h]`.
-/
