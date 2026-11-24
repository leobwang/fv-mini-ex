/- H070 | Diagonally dominant ⇒ invertible | 1-1.5 h | Matrix, det, mulVec, kernel vector, max index, Finset.sum, Gershgorin, mathlib
GOAL
  Levy–Desplanques: if every row is strictly diagonally dominant, `∑_{j ≠ i} |A i j| < |A i i|`, then
  `det A ≠ 0`. Argument: a nonzero kernel vector `v` (`A v = 0`) violates the row of its largest coordinate.
  Second statement (real Gershgorin): if `A v = μ v` with `v ≠ 0` (a real eigenpair), then some row `i` has
  `|μ - A i i| ≤ ∑_{j ≠ i} |A i j|`, i.e. `μ` lies in the `i`-th Gershgorin interval. Same max-coordinate trick.
  (`Matrix (Fin n) (Fin n) ℝ`: n×n real matrix, entries `A i j`; `univ.erase i`: all indices except `i`;
  `μ • v`: the vector `v` scaled by the number `μ`.)
BANNED: det_ne_zero_of_sum_row_lt_diag, det_ne_zero_of_sum_col_lt_diag, eigenvalue_mem_ball, exact?, apply?, rw?, try?, hint

GUIDE
  Entries R1–R27: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Matrix Finset

namespace H070

-- MILESTONE (optional: change or delete)
/- SKELETON · row_eq   (milestone 1; used by diag_le_offdiag)
  1. Row i of hAv as a hypothesis:                                  R1
       this : (A *ᵥ v) i = 0 i
  2. Unfold the product and the zero coordinate, at this:          R2, R3
       this : ∑ x, A i x * v x = 0
  3. Split the diagonal term off the sum, at this:                  R5 with R4
       this : A i i * v i + ∑ x ∈ univ.erase i, A i x * v x = 0
  4. Rearrange:                                                     R6
-/
theorem row_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (hAv : A *ᵥ v = 0) (i : Fin n) :
    A i i * v i = -∑ j ∈ univ.erase i, A i j * v j := by
  have := congrFun hAv i
  simp only [mulVec, dotProduct, Pi.zero_apply] at this
  rw [← add_sum_erase _ _ (mem_univ i)] at this
  linarith

-- MILESTONE (optional: change or delete)
/- SKELETON · exists_max_coord   (milestone 2; used by both spec theorems)
  1. FIRST  hne : (univ : Finset (Fin n)).Nonempty   (Fin 0 is empty; this is where hv is needed)
       by contradiction:                                            R7
       hc : ¬univ.Nonempty  →  univ = ∅  →  IsEmpty (Fin n):        R8, R9 (at hc)
       then v = 0 contradicts hv; each coordinate from the empty type:  R11 (term form), R10
       (hv : v ≠ 0 is a function to False, R24: apply it to the proof of v = 0)
  2. i maximising |v j| over univ (drop the membership part `-`):  R12
  3. Give the witness i: refine ⟨i, ?_, ?_⟩; the max part is hmax with R4
  4. 0 < |v i|, by contradiction:                                   R7, R13
       hc : |v i| ≤ 0, so every |v j| ≤ |v i| ≤ 0, so v j = 0, so v = 0:  R15, R14, R11; contradicts hv
-/
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
/- SKELETON · diag_le_offdiag   (milestone 3; used by det_ne_zero_of_diag_dominant)
  1. Left side → |row sum|, right side: factor into the sum:
       R16 (←), then rw with MILESTONE row_eq A v hAv i, R17, R18
       goal: |∑ j ∈ univ.erase i, A i j * v j| ≤ ∑ i_1 ∈ univ.erase i, |A i i_1| * |v i|
  2. Triangle inequality, then compare term by term (one refine):  R19 (with R15), R20
       goal: |A i j * v j| ≤ |A i j| * |v i|
  3. Split the absolute value, then monotonicity with hi j:         R16 (→), R21, R22
-/
theorem diag_le_offdiag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (hAv : A *ᵥ v = 0)
    (i : Fin n) (hi : ∀ j, |v j| ≤ |v i|) :
    |A i i| * |v i| ≤ (∑ j ∈ univ.erase i, |A i j|) * |v i| := by
  rw [← abs_mul, row_eq A v hAv i, abs_neg, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  -- WHY: `gcongr` would descend into `|·|` and ask for `0 ≤ v j`; give the monotonicity lemma directly
  exact mul_le_mul_of_nonneg_left (hi j) (abs_nonneg _)

-- MILESTONE (optional: change or delete)
/- SKELETON · eig_row_eq   (milestone 4; used by gershgorin_real)
  The steps of row_eq, with (μ • v) i instead of 0 i on the right:
  1. Row i of hAv:                                                  R1
  2. Unfold at this; the right side by R23 instead of R3:          R2, R23
       this : ∑ x, A i x * v x = μ * v i
  3. Split off the diagonal term, at this; rearrange:              R5 with R4, R6
-/
/-- Row `i` of `A v = μ v`, with the diagonal term moved to the left. -/
theorem eig_row_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) (v : Fin n → ℝ) (hAv : A *ᵥ v = μ • v)
    (i : Fin n) : (μ - A i i) * v i = ∑ j ∈ univ.erase i, A i j * v j := by
  have := congrFun hAv i
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
  rw [← add_sum_erase _ _ (mem_univ i)] at this
  linarith

/- SKELETON · det_ne_zero_of_diag_dominant
  Prove MILESTONES row_eq, exists_max_coord, diag_le_offdiag first; this proof only combines them.
  1. Assume hdet : A.det = 0; the goal becomes False:               R24
  2. A kernel vector v, hv0 : v ≠ 0, hAv : A *ᵥ v = 0:              R25 (.mpr hdet)
  3. Its largest coordinate i, hvi : 0 < |v i|, hi:                MILESTONE exists_max_coord
  4. h1 : |A i i| * |v i| ≤ (∑ j ∈ univ.erase i, |A i j|) * |v i|   MILESTONE diag_le_offdiag
     h2 : (∑ j ∈ univ.erase i, |A i j|) * |v i| < |A i i| * |v i|   R26 with h i and hvi
  5. h1 and h2 contradict:                                          R6
-/
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

/- SKELETON · gershgorin_real
  Prove MILESTONES exists_max_coord and eig_row_eq first.
  1. The largest coordinate i of v, hvi : 0 < |v i|, hi:           MILESTONE exists_max_coord
  2. Witness i; prove the bound multiplied by |v i|:               refine ⟨i, ?_⟩ with R27
       goal: |μ - A i i| * |v i| ≤ (∑ j ∈ univ.erase i, |A i j|) * |v i|
  3. Left side → |row sum|, factor into the sum:                   R16 (←), MILESTONE eig_row_eq, R18
  4. As steps 2–3 of diag_le_offdiag:                              R19 (with R15), R20, R16, R21, R22
-/
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
H1. Suppose `A.det = 0`; R25 gives `v ≠ 0` with `A *ᵥ v = 0`. Look at the row `i` where `|v i|` is largest:
    `A i i * v i = -∑_{j ≠ i} A i j * v j`, so `|A i i| |v i| ≤ (∑_{j ≠ i} |A i j|) |v i| < |A i i| |v i|`.
    Gershgorin: the same row with `μ * v i` on the right, then divide by `|v i| > 0`. Prove the milestones in order.
H2. `row_eq` / `eig_row_eq`: take row `i` (R1), unfold (R2, R3 or R23), split off the diagonal (R5), `linarith`.
    `exists_max_coord`: nonemptiness of `univ` first (else `Fin n` is empty and `v = 0`, R7–R11), then R12, and
    `0 < |v i|` by contradiction (R13–R15). `diag_le_offdiag`: rewrite into `|∑ …| ≤ ∑ … * |v i|`, triangle
    inequality, term by term (R16–R22). Main theorems: combine the milestones with R24–R27.
H3. `diag_le_offdiag`: `rw [← abs_mul, row_eq A v hAv i, abs_neg, sum_mul]`, then
    `refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)` and `rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hi j) (abs_nonneg _)`.
    Main: `intro hdet`, get `v`, `i`, and compare with `mul_lt_mul_of_pos_right (h i) hvi` via `linarith`.
    `gershgorin_real`: `refine ⟨i, le_of_mul_le_mul_right ?_ hvi⟩`, `rw [← abs_mul, eig_row_eq A μ v hAv i, sum_mul]`,
    then the same `abs_sum_le_sum_abs` / `sum_le_sum` step as in `diag_le_offdiag`.
-/
