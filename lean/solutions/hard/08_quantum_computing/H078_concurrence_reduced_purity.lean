/- H078 | Concurrence and reduced purity | 1-1.5 h | partial trace, purity, Prob subtype, Lagrange identity, physlib
GOAL
  For a two-qubit ket `ψ`, the reduced state `ρ_A = Tr_B |ψ⟩⟨ψ|` has purity `Tr ρ_A² = 1 − 2|ψ₀₀ψ₁₁ − ψ₀₁ψ₁₀|²`
  (`2|ψ₀₀ψ₁₁ − ψ₀₁ψ₁₀|` is the concurrence). Corollary: `ψ` is a product state iff `ρ_A` is pure.

REFERENCE
  -- `ψ : Ket (Fin 2 × Fin 2)`; `ψ (i, j)` is the amplitude of |ij⟩.  `ρ.m` = raw matrix of `ρ : MState d`.
  -- `(MState.pure ψ).traceRight : MState (Fin 2)` traces out the 2nd qubit;  `ψ.IsProd` := ∃ ξ φ, ψ = ξ ⊗ᵠ φ
  -- (`ξ ⊗ᵠ φ` is `Ket.prod ξ φ`, the tensor product of kets: amplitude `ξ i * φ j` at |ij⟩)
  example (ρ : MState (Fin 2 × Fin 2)) (i j : Fin 2) : ρ.traceRight.m i j = ρ.traceRight.M.mat i j := rfl
  #check MState.traceRight_M        -- ↑ρ.traceRight = (↑ρ).traceRight        (`↑ρ = ρ.M : HermitianMat`)
  #check HermitianMat.traceRight_mat -- ↑A.traceRight = (↑A).traceRight       (`↑A = A.mat : Matrix`)
  #check MState.mat_M               -- ↑↑ρ = ρ.m
  #check Matrix.traceRight          -- a def: `of fun i j => ∑ k, M (i, k) (j, k)`; unfold with `Matrix.of_apply`
  -- `ρ.purity : Prob` is Tr ρ²;  `Prob` = {p : ℝ // 0 ≤ p ∧ p ≤ 1}, so `(ρ.purity : ℝ)` is the number
  #check MState.val_inner           -- ↑⟪ρ, σ⟫_Prob = ⟪↑ρ, ↑σ⟫_ℝ      (`MState.purity ρ` is `⟪ρ, ρ⟫_Prob`)
  #check HermitianMat.inner_eq_re_trace  -- ⟪A, B⟫_ℝ = re (↑A * ↑B).trace
  example (p : Prob) : p = 1 ↔ (p : ℝ) = 1 := by rw [Subtype.ext_iff, Prob.coe_one]
  #check Ket.IsProd_iff_mul_eq_mul  -- ψ.IsProd ↔ ∀ i₁ i₂ j₁ j₂, ψ (i₁,j₁) * ψ (i₂,j₂) = ψ (i₁,j₂) * ψ (i₂,j₁)
BANNED: MState.pure_separable_iff_traceLeft_pure, MState.pure_separable_iff_IsProd, MState.pure_separable_imp_IsProd, MState.Ket.IsProd_iff_rank_eq_one, MState.pure_iff_rank_eq_one
NOTE: theorem 2 is a short corollary of theorem 1 plus `Ket.IsProd_iff_mul_eq_mul`; the work is theorem 1.
-/
import QuantumInfo.States.Mixed.MState

open scoped Matrix

namespace H078

-- MILESTONE (optional: change or delete)
theorem traceRight_pure_apply (ψ : Ket (Fin 2 × Fin 2)) (i j : Fin 2) :
    (MState.pure ψ).traceRight.m i j = ∑ k, ψ (i, k) * starRingEnd ℂ (ψ (j, k)) := by
  show (MState.pure ψ).traceRight.M.mat i j = _
  rw [MState.traceRight_M, HermitianMat.traceRight_mat, MState.mat_M]
  simp only [Matrix.traceRight, Matrix.of_apply, MState.pure_apply]

-- MILESTONE (optional: change or delete)
theorem purity_eq {d : Type} [Fintype d] [DecidableEq d] (ρ : MState d) :
    (ρ.purity : ℝ) = ((ρ.m * ρ.m).trace).re := by
  simp only [MState.purity, MState.val_inner, HermitianMat.inner_eq_re_trace, MState.mat_M]
  rfl

-- MILESTONE (optional: change or delete)
/-- Lagrange's identity: `‖u‖²‖v‖² − |⟨v, u⟩|² = |u₀v₁ − u₁v₀|²` for `u = (a, b)`, `v = (c, d)` -/
theorem lagrange (a b c d : ℂ) :
    (Complex.normSq a + Complex.normSq b) * (Complex.normSq c + Complex.normSq d) -
      Complex.normSq (a * starRingEnd ℂ c + b * starRingEnd ℂ d) = Complex.normSq (a * d - b * c) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

-- BEGIN SPEC
theorem reduced_purity (ψ : Ket (Fin 2 × Fin 2)) :
    ((MState.pure ψ).traceRight.purity : ℝ) =
      1 - 2 * ‖ψ (0, 0) * ψ (1, 1) - ψ (0, 1) * ψ (1, 0)‖ ^ 2 :=
-- END SPEC
  by
    have hn := ψ.normalized
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two] at hn
    set ρ := (MState.pure ψ).traceRight
    have e00 : ρ.m 0 0 = ((Complex.normSq (ψ (0, 0)) + Complex.normSq (ψ (0, 1)) : ℝ) : ℂ) := by
      simp [ρ, traceRight_pure_apply, Fin.sum_univ_two, Complex.mul_conj]
    have e11 : ρ.m 1 1 = ((Complex.normSq (ψ (1, 0)) + Complex.normSq (ψ (1, 1)) : ℝ) : ℂ) := by
      simp [ρ, traceRight_pure_apply, Fin.sum_univ_two, Complex.mul_conj]
    have e01 : ρ.m 0 1 =
        ψ (0, 0) * starRingEnd ℂ (ψ (1, 0)) + ψ (0, 1) * starRingEnd ℂ (ψ (1, 1)) := by
      simp [ρ, traceRight_pure_apply, Fin.sum_univ_two]
    have e10 : ρ.m 1 0 = starRingEnd ℂ (ρ.m 0 1) := by
      simp [ρ, traceRight_pure_apply, Fin.sum_univ_two, mul_comm]
    have htr : ((ρ.m * ρ.m).trace).re =
        (Complex.normSq (ψ (0, 0)) + Complex.normSq (ψ (0, 1))) ^ 2 +
          (Complex.normSq (ψ (1, 0)) + Complex.normSq (ψ (1, 1))) ^ 2 +
            2 * Complex.normSq (ρ.m 0 1) := by
      rw [Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
        Fin.sum_univ_two, e10, e00, e11, mul_comm (starRingEnd ℂ _), Complex.mul_conj]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hl := lagrange (ψ (0, 0)) (ψ (0, 1)) (ψ (1, 0)) (ψ (1, 1))
    rw [purity_eq, htr, Complex.sq_norm, e01]
    linear_combination (Complex.normSq (ψ (0, 0)) + Complex.normSq (ψ (0, 1)) +
      Complex.normSq (ψ (1, 0)) + Complex.normSq (ψ (1, 1)) + 1) * hn - 2 * hl

-- BEGIN SPEC
theorem isProd_iff_reduced_pure (ψ : Ket (Fin 2 × Fin 2)) :
    ψ.IsProd ↔ (MState.pure ψ).traceRight.purity = 1 :=
-- END SPEC
  by
    rw [Subtype.ext_iff, Prob.coe_one, reduced_purity, Ket.IsProd_iff_mul_eq_mul]
    have key : 1 - 2 * ‖ψ (0, 0) * ψ (1, 1) - ψ (0, 1) * ψ (1, 0)‖ ^ 2 = 1 ↔
        ψ (0, 0) * ψ (1, 1) = ψ (0, 1) * ψ (1, 0) := by
      rw [← sub_eq_zero (a := ψ (0, 0) * ψ (1, 1)), ← norm_eq_zero]
      constructor
      · intro h
        nlinarith [norm_nonneg (ψ (0, 0) * ψ (1, 1) - ψ (0, 1) * ψ (1, 0))]
      · intro h
        rw [h]
        ring
    rw [key]
    constructor
    · intro h
      exact h 0 1 0 1
    · intro h i₁ i₂ j₁ j₂
      fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;> simp [h, mul_comm]

end H078

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Name `a b c d` for `ψ (0,0), ψ (0,1), ψ (1,0), ψ (1,1)`. Then `ρ_A = [[p, w], [conj w, q]]` with
    `p = |a|² + |b|²`, `q = |c|² + |d|²`, `w = a c̄ + b d̄`, and `p + q = 1` (`have hn := ψ.normalized`, then
    `simp only [Fintype.sum_prod_type, Fin.sum_univ_two] at hn` splits the sum over `Fin 2 × Fin 2` into 4 terms).
H2. `Tr ρ_A² = p² + q² + 2|w|² = (p + q)² − 2(pq − |w|²)`, and `pq − |w|² = |ad − bc|²` is `lagrange`
    (prove it after `simp only [Complex.normSq_apply, Complex.mul_re, …]` by `ring`). Unwrap the library
    first: `traceRight_pure_apply` by `show … .M.mat i j = _` and the REFERENCE rewrites; `purity_eq` by
    `simp only [MState.purity, MState.val_inner, HermitianMat.inner_eq_re_trace, MState.mat_M]` then `rfl`.
H3. Prove `ρ.m 0 0 = ((normSq a + normSq b : ℝ) : ℂ)`, `ρ.m 1 1 = …`, `ρ.m 0 1 = w`, `ρ.m 1 0 = conj (ρ.m 0 1)`
    (each `simp [traceRight_pure_apply, Fin.sum_univ_two, Complex.mul_conj]`), expand the trace with
    `Matrix.trace_fin_two`, `Matrix.mul_apply`, `Fin.sum_univ_two`, then finish with
    `linear_combination (p + q + 1) * hn - 2 * lagrange a b c d` (`hn : p + q = 1`). Corollary:
    `‖z‖ = 0 ↔ z = 0`, and `fin_cases` all four indices of `IsProd_iff_mul_eq_mul`, `simp [h, mul_comm]`.
-/
