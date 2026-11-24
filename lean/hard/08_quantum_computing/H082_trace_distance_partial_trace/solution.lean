/- H082 | Trace distance contracts under partial trace | 45-75 min | TrDistance, variational trace norm, Kronecker unitaries, classical instances, physlib
GOAL
  Discarding subsystem B cannot make states easier to tell apart: for `ρ σ` on `d₁ × d₂`,
  `D(Tr_B ρ, Tr_B σ) ≤ D(ρ, σ)`. Here `D(ρ, σ) = TrDistance ρ σ = ½‖ρ − σ‖₁` (`‖·‖₁` = trace norm, sum of
  singular values) and `Tr_B ρ = ρ.traceRight` (partial trace over the second factor).

GUIDE
  Entries R1–R21: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import QuantumInfo.States.Mixed.TraceDistance

open scoped Kronecker

namespace H082

/- SKELETON · trace_mul_traceRight   (MILESTONE 1: prove it first; used in step 6 of td_traceRight)
  Both sides are the same triple sum ∑ x, ∑ y, ∑ k, U x y * A (y, k) (x, k), in different orders.
  1. One `simp only [...]` (it rewrites both sides): traces → sums, product entries → sums, sums over
     pairs split, Kronecker and identity entries evaluated, factors pushed into the `if`, the sum
     with one surviving term collapsed:                                  R1, R2, R3, R4, R5, R6, R7
     The left side is now  ∑ x, ∑ j, U x j * A.traceRight j x.
  2. Partial-trace entries → sums over d₂, then move `U x j` inside:   R8, R9   (one `simp only`)
  3. Both sides are ∑ x, (two inner sums, in opposite orders). Go under the outer sum, then swap
     the two inner sums:                                                  R11 → R10
     (as one term: `Finset.sum_congr rfl fun x _ => Finset.sum_comm`)
-/
-- MILESTONE (optional: change or delete)
/-- `Tr_B` is dual to `U ↦ U ⊗ 1`: `tr (U · Tr_B A) = tr ((U ⊗ 1) · A)` -/
theorem trace_mul_traceRight {d₁ d₂ : Type} [Fintype d₁] [Fintype d₂] [DecidableEq d₂]
    (U : Matrix d₁ d₁ ℂ) (A : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) :
    (U * A.traceRight).trace = ((U ⊗ₖ (1 : Matrix d₂ d₂ ℂ)) * A).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [Matrix.traceRight, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_comm

/- SKELETON · traceRight_m_sub   (MILESTONE 2: used in step 2 of td_traceRight)
  1. Right side: split the partial trace of the difference:               R12
  2. Both sides now agree by the definition of `MState.traceRight`:       R13
-/
-- MILESTONE (optional: change or delete)
theorem traceRight_m_sub {d₁ d₂ : Type} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ρ σ : MState (d₁ × d₂)) : ρ.traceRight.m - σ.traceRight.m = (ρ.m - σ.m).traceRight := by
  rw [Matrix.traceRight_sub]
  rfl

/- SKELETON · unitaryGroup_congr   (MILESTONE 3: used in steps 4 and 5 of td_traceRight)
  1. Identify the two instances; `i2` disappears:                        R14
  2. The goal is now `h` itself:                                          exact h
-/
-- MILESTONE (optional: change or delete)
/-- membership in the unitary group does not depend on which `DecidableEq` instance built it -/
theorem unitaryGroup_congr {n : Type} [Fintype n] (i1 i2 : DecidableEq n) (U : Matrix n n ℂ)
    (h : U ∈ @Matrix.unitaryGroup n i1 _ ℂ _ _) : U ∈ @Matrix.unitaryGroup n i2 _ ℂ _ _ := by
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  exact h

/- SKELETON · td_traceRight   (prove MILESTONES 1–3 first)
  With Δ = ρ.m - σ.m:  ‖Tr_B Δ‖₁ = re tr (U * Tr_B Δ) = re tr ((U ⊗ₖ 1) * Δ) ≤ ‖Δ‖₁.
  1. Both distances → `1 / 2 * (…).traceNorm`:                            R15
  2. Small difference → `(ρ.m - σ.m).traceRight`:                         rw [traceRight_m_sub]   (MILESTONE 2)
  3. The unitary U attaining ‖Tr_B Δ‖₁ (gives U, hU, hUeq):              R16
  4. hU' : U ⊗ₖ (1 : Matrix d₂ d₂ ℂ) ∈ Matrix.unitaryGroup (d₁ × d₂) ℂ:
       R18, with hU passed through MILESTONE 3 (classical instance → yours)
  5. hle : re tr ((U ⊗ₖ 1) * Δ) ≤ ‖Δ‖₁, the variational bound for Δ with the candidate U ⊗ₖ 1:
       R17, with hU' passed through MILESTONE 3 (yours → classical)
  6. Clean up `↑⟨_, _⟩` in hUeq and hle, then turn hUeq's trace into the big one:
       R19 (`at hUeq hle`), then R20 with MILESTONE 1 (`at hUeq`)
  7. Replace ‖Tr_B Δ‖₁ in the goal by the trace (rw [← hUeq]), then compare using hle:   R21
-/
-- BEGIN SPEC
theorem td_traceRight {d₁ d₂ : Type} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ρ σ : MState (d₁ × d₂)) : TrDistance ρ.traceRight σ.traceRight ≤ TrDistance ρ σ :=
-- END SPEC
  by
    unfold TrDistance
    rw [traceRight_m_sub]
    -- the unitary attaining the trace norm of the reduced difference
    obtain ⟨⟨U, hU⟩, hUeq⟩ := (Matrix.traceNorm_eq_max_re_tr_U ((ρ.m - σ.m).traceRight)).1
    have hU' : U ⊗ₖ (1 : Matrix d₂ d₂ ℂ) ∈ Matrix.unitaryGroup (d₁ × d₂) ℂ :=
      Matrix.kronecker_mem_unitary (unitaryGroup_congr _ _ _ hU) (one_mem _)
    -- WHY: `U ⊗ₖ 1` is only one candidate for the big difference, so it gives a lower bound
    have hle := (Matrix.traceNorm_eq_max_re_tr_U (ρ.m - σ.m)).2
      ⟨⟨_, unitaryGroup_congr _ _ _ hU'⟩, rfl⟩
    dsimp only at hUeq hle
    rw [trace_mul_traceRight] at hUeq
    rw [← hUeq]
    gcongr

end H082

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Use the variational formula ‖A‖₁ = max over unitaries U of re tr (U * A) twice: the trace norm of
    the small difference Tr_B Δ is attained by some unitary U; by MILESTONE 1 that value is
    re tr ((U ⊗ₖ 1) * Δ); and U ⊗ₖ 1 is one candidate in the formula for Δ, so the value is ≤ ‖Δ‖₁.
H2. Main proof: `unfold TrDistance`, `rw [traceRight_m_sub]`, take U from `.1` of
    `Matrix.traceNorm_eq_max_re_tr_U`, prove `U ⊗ₖ 1` unitary with `Matrix.kronecker_mem_unitary`,
    feed it to `.2` of the formula for Δ, `dsimp only at`, MILESTONE 1 `at hUeq`, `rw [← hUeq]`, `gcongr`.
    The unitaries cross between your `DecidableEq` and the classical one: MILESTONE 3 each time.
    MILESTONE 1: one `simp only` to sums, unfold `traceRight` with `Finset.mul_sum`, swap the inner sums.
    MILESTONE 2: `Matrix.traceRight_sub`, then `rfl`. MILESTONE 3: `Subsingleton.elim`.
H3. `obtain ⟨⟨U, hU⟩, hUeq⟩ := (Matrix.traceNorm_eq_max_re_tr_U ((ρ.m - σ.m).traceRight)).1`;
    `hU' := Matrix.kronecker_mem_unitary (unitaryGroup_congr _ _ _ hU) (one_mem _)`;
    `have hle := (Matrix.traceNorm_eq_max_re_tr_U (ρ.m - σ.m)).2 ⟨⟨_, unitaryGroup_congr _ _ _ hU'⟩, rfl⟩`.
    MILESTONE 1 step 1: `simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]`. MILESTONE 3: `obtain rfl : i1 = i2 := Subsingleton.elim _ _`.
-/
