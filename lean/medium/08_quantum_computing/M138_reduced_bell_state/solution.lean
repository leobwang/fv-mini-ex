/- M138 | Reduced Bell state is maximally mixed | 15-20 min | MState, partial trace, maximally entangled state, HermitianMat unwrapping, physlib
GOAL
  Let `Φ = Σᵢ |i⟩|i⟩ / √d` be the maximally entangled state on `d × d` (`Ket.MES d`). Tracing out the
  left half of `|Φ⟩⟨Φ|` leaves the maximally mixed state `I / d` (`MState.uniform`).
BANNED: traceRight_pure_MES

GUIDE
  Entries R1–R29: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import QuantumInfo.States.Mixed.MState

open Matrix

namespace M138

/- SKELETON · traceLeft_MES
  1. Equation of states → one entry (i, j) of plain matrices:              R1, R2
  2. Expose `.M.mat` on both sides; write both sides out in full,
     the right one as `(MState.uniform : MState d).M.mat i j`:              R3
  3. One `rw [...]` list: left side, then right side:                      R4 → R5 → R6, R7 → R8 → R9 → R10
       goal: `(MState.pure (Ket.MES d)).m.traceLeft i j = if i = j then ↑↑(ProbDistribution.uniform i) else 0`
  4. Partial trace → sum of amplitude products (`simp only`):              R11 → R12 → R13
  5. Split on the index:                                                    R14
     case `h : i = j`:
       a. eliminate `j`:                                                    R15
       b. evaluate `Ket.MES` and collapse the sum with
          `simp [Ket.MES, Ket.apply]`, which applies                        R16–R23
          left: `(↑√↑(Fintype.card d))⁻¹ * (↑√↑(Fintype.card d))⁻¹ = (↑(Fintype.card d))⁻¹`
       c. the √ fact:                                                       R24 → R25 → R26 (side goal by R27)
       d. finish the casts with `simp`:                                     R28
     case `h : ¬i = j`:
       the same `simp`, plus `h` in its list:                               R16–R23, R29
-/
-- BEGIN SPEC
theorem traceLeft_MES {d : Type} [Fintype d] [DecidableEq d] [Nonempty d] :
    (MState.pure (Ket.MES d)).traceLeft = MState.uniform :=
-- END SPEC
  by
    apply MState.ext_m
    ext i j
    -- WHY: `ρ.m` is `ρ.M.mat`; restating it this way lets the `HermitianMat` rewrite lemmas match.
    show (MState.pure (Ket.MES d)).traceLeft.M.mat i j = (MState.uniform : MState d).M.mat i j
    rw [MState.traceLeft_M, HermitianMat.traceLeft_mat, MState.mat_M, MState.uniform,
      MState.coe_ofClassical, HermitianMat.diagonal_mat, Matrix.diagonal_apply]
    simp only [Matrix.traceLeft, Matrix.of_apply, MState.pure_apply]
    by_cases h : i = j
    · subst h
      simp [Ket.MES, Ket.apply]
      rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
      simp
    · simp [Ket.MES, Ket.apply, h]

end M138

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both sides are states. Reduce to entry (i, j) of plain matrices (R1–R3), then unwrap both sides with
    `rw` (R4–R10). What is left is a sum over `k` in which at most one term is nonzero.
H2. After the `rw` list and `simp only [Matrix.traceLeft, Matrix.of_apply, MState.pure_apply]` the goal is
    `∑ x, (Ket.MES d) (x, i) * (starRingEnd ℂ) ((Ket.MES d) (x, j)) = if i = j then ↑↑(ProbDistribution.uniform i) else 0`
    (`(starRingEnd ℂ) z` is the conjugate z̄).
    `by_cases h : i = j`. Diagonal: `subst h`, `simp [Ket.MES, Ket.apply]` leaves the √ fact.
    Off-diagonal: `simp [Ket.MES, Ket.apply, h]` closes it.
H3. `rw [MState.traceLeft_M, HermitianMat.traceLeft_mat, MState.mat_M, MState.uniform, MState.coe_ofClassical,
    HermitianMat.diagonal_mat, Matrix.diagonal_apply]`. The diagonal case ends at `(√n)⁻¹ * (√n)⁻¹ = n⁻¹`:
    `rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]`, then `simp`.
-/
