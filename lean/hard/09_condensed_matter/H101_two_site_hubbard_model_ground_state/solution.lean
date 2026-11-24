/- H101 | Two-site Hubbard model ground state | 1-1.5 h | Matrix, mulVec, dotProduct, eigenvector, variational bound, linear_combination, nlinarith, mathlib
GOAL
  The two-site Hubbard model with two electrons (`S_z = 0`) is the 4×4 matrix `H t U` below. Prove
  that `E0 = (U - √(U² + 16t²))/2` is its ground-state energy: it is an eigenvalue (there is a
  nonzero eigenvector), and `E0 * (x ⬝ᵥ x) ≤ x ⬝ᵥ (H *ᵥ x)`, i.e. `E0 ‖x‖² ≤ ⟨x, H x⟩`, for every
  state `x` (the variational bound).

GUIDE
  Entries R1–R30: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Matrix

namespace H101

-- BEGIN SPEC
/-- Two-site Hubbard Hamiltonian at half filling, `S_z = 0` sector, basis
`|↑↓,0⟩, |0,↑↓⟩, |↑,↓⟩, |↓,↑⟩` (signs chosen so every hopping entry is `-t`). -/
noncomputable def H (t U : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![U, 0, -t, -t; 0, U, -t, -t; -t, -t, 0, 0; -t, -t, 0, 0]

/-- The claimed ground-state energy. -/
noncomputable def E0 (t U : ℝ) : ℝ := (U - Real.sqrt (U ^ 2 + 16 * t ^ 2)) / 2
-- END SPEC

/- SKELETON · E0_quad
  1. The one non-ring fact, BEFORE unfolding:                                R1 with R2
       h : √(U ^ 2 + 16 * t ^ 2) ^ 2 = U ^ 2 + 16 * t ^ 2
  2. Expose the root:                                                       R3 (unfold E0)
  3. Close: the goal minus a constant multiple of h is a ring identity      R4
-/
-- MILESTONE (optional: change or delete)
theorem E0_quad (t U : ℝ) : E0 t U ^ 2 - U * E0 t U - 4 * t ^ 2 = 0 := by
  have h := Real.sq_sqrt (show 0 ≤ U ^ 2 + 16 * t ^ 2 by positivity)
  unfold E0
  linear_combination h / 4

/- SKELETON · E0_lt
  1. Prove first  hlt : |U| < √(U ^ 2 + 16 * t ^ 2):
       write |U| as a root                                                  R5
       compare the radicands                                                R6
         side goal 0 ≤ U ^ 2                                                R7
         side goal U ^ 2 < U ^ 2 + 16 * t ^ 2: get 0 < t ^ 2 from ht        R8 → R9 → R10, then R11
  2. Unfold, split the ∧, split the sign of U, close each linear goal:      R3, constructor, R12, R11
-/
-- MILESTONE (optional: change or delete)
theorem E0_lt (t U : ℝ) (ht : t ≠ 0) : E0 t U < 0 ∧ E0 t U < U := by
  have hlt : |U| < Real.sqrt (U ^ 2 + 16 * t ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by have := pow_pos (abs_pos.mpr ht) 2; simp at this; linarith)
  unfold E0
  constructor <;> cases abs_cases U <;> linarith

/- SKELETON · block_nonneg      (uses the milestones E0_lt and E0_quad)
  1. hUE : 0 < U - E0 t U          from (E0_lt t U ht).2                     R11
  2. key : (U - E0 t U) * (the quadratic form) = ((U - E0 t U) * s - 2 * t * d) ^ 2
                                   coefficient: a monomial in d times E0_quad t U   R4
  3. Multiply the goal by U - E0 t U, rewrite with key, close:              R13, rw [key], R2
-/
-- MILESTONE (optional: change or delete)
theorem block_nonneg (t U s d : ℝ) (ht : t ≠ 0) :
    0 ≤ (U - E0 t U) * s ^ 2 - 4 * t * s * d - E0 t U * d ^ 2 := by
  have hUE : 0 < U - E0 t U := by linarith [(E0_lt t U ht).2]
  have key : (U - E0 t U) * ((U - E0 t U) * s ^ 2 - 4 * t * s * d - E0 t U * d ^ 2) =
      ((U - E0 t U) * s - 2 * t * d) ^ 2 := by
    linear_combination d ^ 2 * E0_quad t U
  rw [← mul_nonneg_iff_of_pos_left hUE, key]
  positivity

/- SKELETON · ground_state_energy
  Prove the three MILESTONES above first. E0_quad is used in step 2b, E0_lt in step 0 (its two
  halves feed step 3), block_nonneg in step 3. With them, `E0` is never unfolded here.
  0. Facts: hq := E0_quad t U; split E0_lt t U ht into h0 : E0 t U < 0, hU : E0 t U < U    R14
  1. Give the eigenvector and split into three goals:                          R15
       witness ![a, a, b, b] (equal on sites 0, 1 and on 2, 3; H2 says which a, b)
  2a. v ≠ 0: assume v = 0, read entry 2, simplify to t = 0, contradict ht:     R16 → R17 → R18 → R19
  2b. H t U *ᵥ v = E0 t U • v: entrywise, evaluate, close:                     R20, fin_cases,
        simp [H, mulVec, dotProduct, Fin.sum_univ_four]  (R21–R24), then R25 with hq
  3. Variational bound for the given x:
       hb := block_nonneg t U (x 0 + x 1) (x 2 + x 3) ht
       evaluate: simp [H, mulVec, dotProduct, Fin.sum_univ_four]               R21–R23
       close with R26, passing two more nonnegative products:
         (U - E0) (x 0 - x 1)²  from hU                                        R27, R28, R30, R7
         (-E0) (x 2 - x 3)²     from h0                                        R27, R29, R30, R7
-/
-- BEGIN SPEC
theorem ground_state_energy (t U : ℝ) (ht : t ≠ 0) :
    (∃ v : Fin 4 → ℝ, v ≠ 0 ∧ H t U *ᵥ v = E0 t U • v) ∧
      ∀ x : Fin 4 → ℝ, E0 t U * (x ⬝ᵥ x) ≤ x ⬝ᵥ (H t U *ᵥ x) :=
-- END SPEC
  by
    have hq := E0_quad t U
    obtain ⟨h0, hU⟩ := E0_lt t U ht
    refine ⟨⟨![-E0 t U, -E0 t U, 2 * t, 2 * t], ?_, ?_⟩, fun x => ?_⟩
    · intro h
      have h2 := congrFun h 2
      simp at h2
      exact ht h2
    · ext i
      fin_cases i <;> simp [H, mulVec, dotProduct, Fin.sum_univ_four] <;> first | ring1 | linear_combination hq
    · have hb := block_nonneg t U (x 0 + x 1) (x 2 + x 3) ht
      simp [H, mulVec, dotProduct, Fin.sum_univ_four]
      nlinarith [mul_nonneg (sub_nonneg.mpr hU.le) (sq_nonneg (x 0 - x 1)),
        mul_nonneg (neg_nonneg.mpr h0.le) (sq_nonneg (x 2 - x 3))]

end H101

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Hopping only sees `s = x 0 + x 1` and `d = x 2 + x 3`, so look for an eigenvector with `x 0 = x 1`
    and `x 2 = x 3`. All you need about `E0` is the quadratic `E0² - U E0 - 4t² = 0` (`E0_quad`) and
    `E0 < 0`, `E0 < U` (`E0_lt`; strict because `t ≠ 0` makes `|U| < √(U² + 16t²)`). Prove those first.
H2. Eigenvector: `![-E0 t U, -E0 t U, 2 * t, 2 * t]` (nonzero: entry 2 is `2t`, R17–R19). Variational part:
    `⟨x, Hx⟩ - E0 ‖x‖² = ½[(U - E0) s² - 4t s d - E0 d²] + ½(U - E0)(x0 - x1)² - ½E0 (x2 - x3)²`.
    The last two terms are ≥ 0 (R27–R30); the bracket is `block_nonneg`, which follows from
    `(U - E0) · bracket = ((U - E0) s - 2t d)²` and `U - E0 > 0` (R13).
H3. `E0_quad`: `linear_combination h / 4` after R1, R3. `block_nonneg`: `key` by
    `linear_combination d ^ 2 * E0_quad t U`, then `rw [← mul_nonneg_iff_of_pos_left hUE, key]`.
    Eigen-entries: `fin_cases i <;> simp [H, mulVec, dotProduct, Fin.sum_univ_four] <;> first | ring1 | linear_combination hq`.
    Main bound: after the `simp`, `nlinarith [hb, mul_nonneg (sub_nonneg.mpr hU.le) (sq_nonneg (x 0 - x 1)),
      mul_nonneg (neg_nonneg.mpr h0.le) (sq_nonneg (x 2 - x 3))]`.
-/
