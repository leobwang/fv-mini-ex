/- H070 | Diagonally dominant ⇒ invertible | 1-1.5 h | Matrix, det, mulVec, kernel vector, max index, Finset.sum, Gershgorin, mathlib
GOAL
  Levy–Desplanques: if every row is strictly diagonally dominant, `∑_{j ≠ i} |A i j| < |A i i|`, then
  `det A ≠ 0`. Argument: a nonzero kernel vector `v` (`A v = 0`) violates the row of its largest coordinate.
  Second statement (real Gershgorin): if `A v = μ v` with `v ≠ 0` (a real eigenpair), then some row `i` has
  `|μ - A i i| ≤ ∑_{j ≠ i} |A i j|`, i.e. `μ` lies in the `i`-th Gershgorin interval. Same max-coordinate trick.
  (`Matrix (Fin n) (Fin n) ℝ`: n×n real matrix, entries `A i j`; `univ.erase i`: all indices except `i`;
  `μ • v`: the vector `v` scaled by the number `μ`.)

REFERENCE
  #check Matrix.exists_mulVec_eq_zero_iff  -- (∃ v, v ≠ 0 ∧ M *ᵥ v = 0) ↔ M.det = 0      (`*ᵥ`: matrix times vector)
  example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (i : Fin n) : (A *ᵥ v) i = ∑ j, A i j * v j := rfl
  #check Finset.exists_max_image     -- s.Nonempty → ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x
  #check Finset.add_sum_erase        -- a ∈ s → f a + ∑ x ∈ s.erase a, f x = ∑ x ∈ s, f x
  #check Finset.abs_sum_le_sum_abs   -- |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i|
  #check Finset.sum_mul              -- (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a
  #check mul_le_mul_of_nonneg_left   -- b ≤ c → 0 ≤ a → a * b ≤ a * c
  #check mul_lt_mul_of_pos_right     -- b < c → 0 < a → b * a < c * a
  #check le_of_mul_le_mul_right      -- b * a ≤ c * a → 0 < a → b ≤ c
  example (μ : ℝ) (v : Fin 3 → ℝ) (i : Fin 3) : (μ • v) i = μ * v i := by simp only [Pi.smul_apply, smul_eq_mul]
  example {n : ℕ} (v : Fin n → ℝ) (h : ∀ j, v j = 0) : v = 0 := funext h
  `congrFun h i` turns `h : A *ᵥ v = 0` into `(A *ᵥ v) i = 0 i`; `abs_nonpos_iff : |a| ≤ 0 ↔ a = 0`.
BANNED: det_ne_zero_of_sum_row_lt_diag, det_ne_zero_of_sum_col_lt_diag, eigenvalue_mem_ball, exact?, apply?, rw?, try?, hint
NOTE: `Fin 0` is empty, so `univ` may be empty: get nonemptiness from `v ≠ 0` before taking a max.
-/
import Mathlib

open Matrix Finset

namespace H070

-- MILESTONE (optional: change or delete)
theorem row_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (hAv : A *ᵥ v = 0) (i : Fin n) :
    A i i * v i = -∑ j ∈ univ.erase i, A i j * v j := by
  have := congrFun hAv i
  simp only [mulVec, dotProduct, Pi.zero_apply] at this
  rw [← add_sum_erase _ _ (mem_univ i)] at this
  linarith

-- MILESTONE (optional: change or delete)
theorem exists_max_coord {n : ℕ} (v : Fin n → ℝ) (hv : v ≠ 0) :
    ∃ i, 0 < |v i| ∧ ∀ j, |v j| ≤ |v i| := by
  -- WHY: for `n = 0` there is no index at all, but then `v = 0`
  have hne : (univ : Finset (Fin n)).Nonempty := by
    by_contra hc
    rw [not_nonempty_iff_eq_empty, univ_eq_empty_iff] at hc
    exact hv (funext fun i => (hc.false i).elim)
  obtain ⟨i, -, hi⟩ := exists_max_image univ (fun j => |v j|) hne
  refine ⟨i, ?_, fun j => hi j (mem_univ j)⟩
  by_contra hc
  push Not at hc
  exact hv (funext fun j => abs_nonpos_iff.mp ((hi j (mem_univ j)).trans hc))

-- MILESTONE (optional: change or delete)
theorem diag_le_offdiag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (hAv : A *ᵥ v = 0)
    (i : Fin n) (hi : ∀ j, |v j| ≤ |v i|) :
    |A i i| * |v i| ≤ (∑ j ∈ univ.erase i, |A i j|) * |v i| := by
  rw [← abs_mul, row_eq A v hAv i, abs_neg, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  -- WHY: `gcongr` would descend into `|·|` and ask for `0 ≤ v j`; give the monotonicity lemma directly
  exact mul_le_mul_of_nonneg_left (hi j) (abs_nonneg _)

-- MILESTONE (optional: change or delete)
/-- Row `i` of `A v = μ v`, with the diagonal term moved to the left. -/
theorem eig_row_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) (v : Fin n → ℝ) (hAv : A *ᵥ v = μ • v)
    (i : Fin n) : (μ - A i i) * v i = ∑ j ∈ univ.erase i, A i j * v j := by
  have := congrFun hAv i
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
  rw [← add_sum_erase _ _ (mem_univ i)] at this
  linarith

-- BEGIN SPEC
theorem det_ne_zero_of_diag_dominant {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ i, ∑ j ∈ univ.erase i, |A i j| < |A i i|) : A.det ≠ 0 :=
-- END SPEC
  by
    intro hdet
    obtain ⟨v, hv0, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    obtain ⟨i, hvi, hi⟩ := exists_max_coord v hv0
    have h1 := diag_le_offdiag A v hAv i hi
    have h2 := mul_lt_mul_of_pos_right (h i) hvi
    linarith

-- BEGIN SPEC
theorem gershgorin_real {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) (v : Fin n → ℝ)
    (hv : v ≠ 0) (hAv : A *ᵥ v = μ • v) : ∃ i, |μ - A i i| ≤ ∑ j ∈ univ.erase i, |A i j| :=
-- END SPEC
  by
    obtain ⟨i, hvi, hi⟩ := exists_max_coord v hv
    -- WHY: prove the bound multiplied by `|v i| > 0`, then cancel
    refine ⟨i, le_of_mul_le_mul_right ?_ hvi⟩
    rw [← abs_mul, eig_row_eq A μ v hAv i, sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hi j) (abs_nonneg _)

end H070

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Suppose `A.det = 0`; `exists_mulVec_eq_zero_iff` gives `v ≠ 0` with `A *ᵥ v = 0`. Pick `i` with `|v i|` maximal.
    Row `i` says `A i i * v i = -∑_{j ≠ i} A i j * v j`, so `|A i i| |v i| ≤ (∑_{j ≠ i} |A i j|) |v i|`.
    Gershgorin: same row with `μ v i` on the right, so `|μ - A i i| |v i| ≤ (∑_{j ≠ i} |A i j|) |v i|`; divide by `|v i|`.
H2. `row_eq`: `have := congrFun hAv i`, unfold with `simp only [mulVec, dotProduct, Pi.zero_apply] at this`, split off
    the diagonal term with `add_sum_erase`, then `linarith`. `exists_max_coord`: nonempty `univ` (else `v = 0`),
    `exists_max_image univ (fun j => |v j|)`, and `0 < |v i|` because otherwise every `|v j| ≤ 0`.
H3. `diag_le_offdiag`: `rw [← abs_mul, row_eq A v hAv i, abs_neg, sum_mul]`, then
    `refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)` and `rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hi j) (abs_nonneg _)`.
    Main: `intro hdet`, get `v`, `i`, and compare with `mul_lt_mul_of_pos_right (h i) hvi` via `linarith`.
    `eig_row_eq`: as `row_eq`, but also unfold `Pi.smul_apply, smul_eq_mul`. `gershgorin_real`: take `i` from
    `exists_max_coord`, `refine ⟨i, le_of_mul_le_mul_right ?_ hvi⟩`, `rw [← abs_mul, eig_row_eq A μ v hAv i, sum_mul]`,
    then the same `abs_sum_le_sum_abs` / `sum_le_sum` step as in `diag_le_offdiag`.
-/
