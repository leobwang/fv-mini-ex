/- H082 | Trace distance contracts under partial trace | 45-75 min | TrDistance, variational trace norm, Kronecker unitaries, classical instances, physlib
GOAL
  Discarding subsystem B cannot make states easier to tell apart: for `ρ σ` on `d₁ × d₂`,
  `D(Tr_B ρ, Tr_B σ) ≤ D(ρ, σ)`. Here `D(ρ, σ) = TrDistance ρ σ = ½‖ρ − σ‖₁` (`‖·‖₁` = trace norm, sum of
  singular values) and `Tr_B ρ = ρ.traceRight` (partial trace over the second factor).

REFERENCE
  #print TrDistance                       -- TrDistance ρ σ = 1 / 2 * (ρ.m - σ.m).traceNorm   (`ρ.m` : raw matrix of ρ)
  #check Matrix.traceNorm_eq_max_re_tr_U  -- IsGreatest {x | ∃ U : unitaryGroup, re (tr (U * A)) = x} A.traceNorm
  example (S : Set ℝ) (a : ℝ) (h : IsGreatest S a) : a ∈ S ∧ ∀ x ∈ S, x ≤ a := ⟨h.1, h.2⟩  -- witness + upper bound
  #check Matrix.traceRight                -- M.traceRight i j = ∑ k, M (i, k) (j, k)   (Tr_B on raw matrices)
  #check MState.traceRight_M              -- (ρ.traceRight).M = ρ.M.traceRight   (on `HermitianMat`; `.m` is `.M.mat`)
  #check Matrix.traceRight_sub            -- (A - B).traceRight = A.traceRight - B.traceRight
  #check Matrix.kronecker_mem_unitary     -- U₁ ∈ unitary _ → U₂ ∈ unitary _ → U₁ ⊗ₖ U₂ ∈ unitary _
  #check Fintype.sum_prod_type            -- ∑ x, f x = ∑ x, ∑ y, f (x, y)   (sums over pairs)
  -- `A ⊗ₖ B` (open scoped Kronecker): (A ⊗ₖ B) (a, b) (c, e) = A a c * B b e;   `gcongr` for `1/2 * x ≤ 1/2 * y`
NOTE: `traceNorm_eq_max_re_tr_U` lives under `open Classical`: its unitary group uses classical `DecidableEq`, not yours. `obtain rfl : i1 = i2 := Subsingleton.elim _ _` identifies two instances.
-/
import QuantumInfo.States.Mixed.TraceDistance

open scoped Kronecker

namespace H082

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

-- MILESTONE (optional: change or delete)
theorem traceRight_m_sub {d₁ d₂ : Type} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ρ σ : MState (d₁ × d₂)) : ρ.traceRight.m - σ.traceRight.m = (ρ.m - σ.m).traceRight := by
  rw [Matrix.traceRight_sub]
  rfl

-- MILESTONE (optional: change or delete)
/-- membership in the unitary group does not depend on which `DecidableEq` instance built it -/
theorem unitaryGroup_congr {n : Type} [Fintype n] (i1 i2 : DecidableEq n) (U : Matrix n n ℂ)
    (h : U ∈ @Matrix.unitaryGroup n i1 _ ℂ _ _) : U ∈ @Matrix.unitaryGroup n i2 _ ℂ _ _ := by
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  exact h

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
H1. Use the variational formula twice: the trace norm of the small difference is attained by some unitary `U`; then `U ⊗ₖ 1` is one candidate in the formula for the big difference.
H2. After `unfold TrDistance`, rewrite the small difference as `(ρ.m - σ.m).traceRight` (milestone 2), take `⟨⟨U, hU⟩, hUeq⟩ := (traceNorm_eq_max_re_tr_U _).1`, show `U ⊗ₖ 1` unitary, feed it to `.2` of the big `IsGreatest`, and finish with milestone 1 and `gcongr`.
H3. `have hle := (Matrix.traceNorm_eq_max_re_tr_U (ρ.m - σ.m)).2 ⟨⟨U ⊗ₖ 1, unitaryGroup_congr _ _ _ hU'⟩, rfl⟩`. Milestone 1: unfold `trace, diag, mul_apply, kroneckerMap_apply, one_apply` with `Fintype.sum_prod_type` and `Finset.sum_ite_eq`, then `Finset.mul_sum` and `Finset.sum_comm`. Milestone 2: `rw [Matrix.traceRight_sub]; rfl`.
-/
