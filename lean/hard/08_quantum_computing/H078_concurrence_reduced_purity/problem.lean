/- H078 | Concurrence and reduced purity | 1-1.5 h | partial trace, purity, Prob subtype, Lagrange identity, physlib
GOAL
  For a two-qubit ket `ψ`, the reduced state `ρ_A = Tr_B |ψ⟩⟨ψ|` has purity `Tr ρ_A² = 1 − 2|ψ₀₀ψ₁₁ − ψ₀₁ψ₁₀|²`
  (`2|ψ₀₀ψ₁₁ − ψ₀₁ψ₁₀|` is the concurrence). Corollary: `ψ` is a product state iff `ρ_A` is pure.

BANNED: MState.pure_separable_iff_traceLeft_pure, MState.pure_separable_iff_IsProd, MState.pure_separable_imp_IsProd, MState.Ket.IsProd_iff_rank_eq_one, MState.pure_iff_rank_eq_one

GUIDE
  Entries R1–R32: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import QuantumInfo.States.Mixed.MState

open scoped Matrix

namespace H078

-- MILESTONE (optional: change or delete)
/- SKELETON · traceRight_pure_apply   (used in Part 4 for the four entries of ρ_A)
  1. Restate the left side in the `↑↑` form the lemmas expect:                R1
       show (MState.pure ψ).traceRight.M.mat i j = _
  2. Push the partial trace inward, state → Hermitian → plain matrix:        R2 → R3 → R4
  3. Unfold the partial trace, then the entries of the pure state:           R5, R6 (one `simp only`)
-/
theorem traceRight_pure_apply (ψ : Ket (Fin 2 × Fin 2)) (i j : Fin 2) :
    (MState.pure ψ).traceRight.m i j = ∑ k, ψ (i, k) * starRingEnd ℂ (ψ (j, k)) := by
  sorry

-- MILESTONE (optional: change or delete)
/- SKELETON · purity_eq   (used in Part 4 to turn the purity into a trace)
  1. One `simp only`: unfold purity, leave Prob, inner product → trace, `↑↑ρ` → `ρ.m`:   R7, R8, R9, R4
  2. What is left is `RCLike.re t = t.re`:                                              R10
-/
theorem purity_eq {d : Type} [Fintype d] [DecidableEq d] (ρ : MState d) :
    (ρ.purity : ℝ) = ((ρ.m * ρ.m).trace).re := by
  sorry

-- MILESTONE (optional: change or delete)
/- SKELETON · lagrange   (used in Part 4, step 6, as `hl`)
  1. One `simp only` into real and imaginary parts:                          R11, R12, R13, R14
  2. A polynomial identity in 8 real unknowns:                               ring
-/
/-- Lagrange's identity: `‖u‖²‖v‖² − |⟨v, u⟩|² = |u₀v₁ − u₁v₀|²` for `u = (a, b)`, `v = (c, d)` -/
theorem lagrange (a b c d : ℂ) :
    (Complex.normSq a + Complex.normSq b) * (Complex.normSq c + Complex.normSq d) -
      Complex.normSq (a * starRingEnd ℂ c + b * starRingEnd ℂ d) = Complex.normSq (a * d - b * c) := by
  sorry

/- SKELETON · reduced_purity   (prove the three MILESTONES above first)
  Shorthand below, not Lean names: a b c d = ψ (0, 0), ψ (0, 1), ψ (1, 0), ψ (1, 1);
  normSq = Complex.normSq; conj = starRingEnd ℂ. Write them out in full in your `have`s.
  1. Norm 1 as four terms:                                                    R15, then R16 + R17 at hn
       hn : normSq a + normSq b + (normSq c + normSq d) = 1
  2. Name the reduced state:   set ρ := (MState.pure ψ).traceRight            R18
  3. The four entries, each by `simp [ρ, traceRight_pure_apply, Fin.sum_univ_two, …]`
       (milestone 1, R17; add R19 for e00 e11, `mul_comm` for e10):
       e00 : ρ.m 0 0 = ((normSq a + normSq b : ℝ) : ℂ)      e11 : ρ.m 1 1 = ((normSq c + normSq d : ℝ) : ℂ)
       e01 : ρ.m 0 1 = a * conj c + b * conj d             e10 : ρ.m 1 0 = conj (ρ.m 0 1)
  4. htr : ((ρ.m * ρ.m).trace).re = (normSq a + normSq b) ^ 2 + (normSq c + normSq d) ^ 2
                                     + 2 * normSq (ρ.m 0 1)
       R20 → R21 (twice) → R17 (twice) → rw [e10, e00, e11] → R22 → R19,
       then R12, R13, R23 in one `simp only`, then ring
  5. hl := lagrange a b c d                                                  (milestone 3)
  6. rw [purity_eq, htr, Complex.sq_norm, e01]                               milestone 2, R24
  7. Close with coefficients (p + q + 1) on hn and −2 on hl, p + q = the four normSq:   R25
-/
-- BEGIN SPEC
theorem reduced_purity (ψ : Ket (Fin 2 × Fin 2)) :
    ((MState.pure ψ).traceRight.purity : ℝ) =
      1 - 2 * ‖ψ (0, 0) * ψ (1, 1) - ψ (0, 1) * ψ (1, 0)‖ ^ 2 :=
-- END SPEC
  sorry

/- SKELETON · isProd_iff_reduced_pure   (a corollary of `reduced_purity`)
  1. One `rw`: Prob equation → real equation, Part 4, IsProd → minors:       R26, R27, rw [reduced_purity], R28
  2. key : 1 - 2 * ‖ad - bc‖ ^ 2 = 1 ↔ ad = bc      (ad = ψ (0, 0) * ψ (1, 1), bc = ψ (0, 1) * ψ (1, 0))
       R29 → R30, then constructor;  →: R32 with hint R31;  ←: rw [h], ring
  3. rw [key], then constructor
  4. →: the minor at indices 0 1 0 1 is the one in `key`
  5. ←: intro the four indices, fin_cases each, simp [h, mul_comm]           (W5)
-/
-- BEGIN SPEC
theorem isProd_iff_reduced_pure (ψ : Ket (Fin 2 × Fin 2)) :
    ψ.IsProd ↔ (MState.pure ψ).traceRight.purity = 1 :=
-- END SPEC
  sorry

end H078

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Do the milestones first: they peel off physlib. Name `a b c d` for `ψ (0,0), ψ (0,1), ψ (1,0), ψ (1,1)`.
    Then `ρ_A = [[p, w], [w̄, q]]` with `p = |a|² + |b|²`, `q = |c|² + |d|²`, `w = a c̄ + b d̄`, and `p + q = 1`
    is `ψ.normalized` split into four terms (R15–R17). Theorem 2 is a corollary of theorem 1.
H2. `Tr ρ_A² = p² + q² + 2|w|² = (p + q)² − 2(pq − |w|²)`, and `pq − |w|² = |ad − bc|²` is `lagrange`. So:
    prove the four entries of `ρ_A` (milestone 1 + `Complex.mul_conj`), expand the trace (R20, R21, R17),
    rewrite purity with `purity_eq`, `‖·‖²` with `Complex.sq_norm`, and close by `linear_combination`.
    Corollary: `Subtype.ext_iff, Prob.coe_one, reduced_purity, Ket.IsProd_iff_mul_eq_mul`, then
    `1 - 2x² = 1 ↔ x = 0` for `x = ‖ad − bc‖` and a `fin_cases` over the four minor indices.
H3. Key lines: `traceRight_pure_apply`: `show (MState.pure ψ).traceRight.M.mat i j = _`, then
    `rw [MState.traceRight_M, HermitianMat.traceRight_mat, MState.mat_M]`;
    `simp only [Matrix.traceRight, Matrix.of_apply, MState.pure_apply]`.
    `purity_eq`: `simp only [MState.purity, MState.val_inner, HermitianMat.inner_eq_re_trace, MState.mat_M]; rfl`.
    `reduced_purity` ends with `linear_combination (p + q + 1) * hn - 2 * lagrange a b c d`, written out with
    `p + q = normSq a + normSq b + normSq c + normSq d`.
    Corollary `key`: `rw [← sub_eq_zero (a := ψ (0, 0) * ψ (1, 1)), ← norm_eq_zero]`, and
    `nlinarith [norm_nonneg (ψ (0, 0) * ψ (1, 1) - ψ (0, 1) * ψ (1, 0))]` for `→`.
-/
