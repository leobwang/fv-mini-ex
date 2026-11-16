/- H101 | Two-site Hubbard model ground state | 1-1.5 h | Matrix, mulVec, dotProduct, eigenvector, variational bound, linear_combination, nlinarith, mathlib
GOAL
  The two-site Hubbard model with two electrons (`S_z = 0`) is the 4×4 matrix `H t U` below. Prove
  that `E0 = (U - √(U² + 16t²))/2` is its ground-state energy: it is an eigenvalue (there is a
  nonzero eigenvector), and `E0 * (x ⬝ᵥ x) ≤ x ⬝ᵥ (H *ᵥ x)`, i.e. `E0 ‖x‖² ≤ ⟨x, H x⟩`, for every
  state `x` (the variational bound).

REFERENCE
  example : !![(1 : ℝ), 2; 3, 4] *ᵥ ![1, 0] = ![1, 3] := by ext i; fin_cases i <;> simp  -- `M *ᵥ v`: matrix times vector
  example (x : Fin 4 → ℝ) : x ⬝ᵥ x = x 0 * x 0 + x 1 * x 1 + x 2 * x 2 + x 3 * x 3 := by simp [dotProduct, Fin.sum_univ_four]
  #check Matrix.mulVec          -- (M *ᵥ v) i = ∑ j, M i j * v j   (unfold with `simp [H, mulVec, dotProduct, Fin.sum_univ_four]`)
  example (v w : Fin 4 → ℝ) (h : v = w) : v 2 = w 2 := congrFun h 2  -- read off one component
  #check Real.sq_sqrt           -- 0 ≤ x → √x ^ 2 = x
  #check Real.sqrt_lt_sqrt      -- 0 ≤ x → x < y → √x < √y
  #check Real.sqrt_sq_eq_abs    -- √(x ^ 2) = |x|      (then `cases abs_cases U <;> linarith`)
  #check mul_nonneg_iff_of_pos_left  -- 0 < c → (0 ≤ c * b ↔ 0 ≤ b)
  example (a b c : ℝ) (h1 : a = b) (h2 : b = c) : 2 * a = b + c := by linear_combination 2 * h1 + h2
  `nlinarith [p, q]` proves polynomial inequalities; pass it the non-negative products it needs.
NOTE: basis `|↑↓,0⟩, |0,↑↓⟩, |↑,↓⟩, |↓,↑⟩`; `t` = hopping, `U` = on-site repulsion; `![a, b, c, d]` is a vector; `x ⬝ᵥ (H *ᵥ x)` = ⟨x, H x⟩;
  `c • v` = scalar c times vector v (componentwise, `(c • v) i = c * v i`).
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

-- MILESTONE (optional: change or delete)
theorem E0_quad (t U : ℝ) : E0 t U ^ 2 - U * E0 t U - 4 * t ^ 2 = 0 := by
  have h := Real.sq_sqrt (show 0 ≤ U ^ 2 + 16 * t ^ 2 by positivity)
  unfold E0
  linear_combination h / 4

-- MILESTONE (optional: change or delete)
theorem E0_lt (t U : ℝ) (ht : t ≠ 0) : E0 t U < 0 ∧ E0 t U < U := by
  have hlt : |U| < Real.sqrt (U ^ 2 + 16 * t ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by have := pow_pos (abs_pos.mpr ht) 2; simp at this; linarith)
  unfold E0
  constructor <;> cases abs_cases U <;> linarith

-- MILESTONE (optional: change or delete)
theorem block_nonneg (t U s d : ℝ) (ht : t ≠ 0) :
    0 ≤ (U - E0 t U) * s ^ 2 - 4 * t * s * d - E0 t U * d ^ 2 := by
  have hUE : 0 < U - E0 t U := by linarith [(E0_lt t U ht).2]
  have key : (U - E0 t U) * ((U - E0 t U) * s ^ 2 - 4 * t * s * d - E0 t U * d ^ 2) =
      ((U - E0 t U) * s - 2 * t * d) ^ 2 := by
    linear_combination d ^ 2 * E0_quad t U
  rw [← mul_nonneg_iff_of_pos_left hUE, key]
  positivity

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
    and `x 2 = x 3`. All you need about `E0` is `E0² - U E0 - 4t² = 0` and `E0 < 0`, `E0 < U`
    (both strict because `t ≠ 0` makes `|U| < √(U² + 16t²)`).
H2. Eigenvector: `![-E0 t U, -E0 t U, 2 * t, 2 * t]` (nonzero: component 2 is `2t`). Variational part:
    `⟨x, Hx⟩ - E0 ‖x‖² = ½[(U - E0) s² - 4t s d - E0 d²] + ½(U - E0)(x0 - x1)² - ½E0 (x2 - x3)²`.
    The last two terms are ≥ 0; the bracket is `block_nonneg`.
H3. `block_nonneg`: `(U - E0) * ((U - E0) * s ^ 2 - 4 * t * s * d - E0 * d ^ 2) = ((U - E0) * s - 2 * t * d) ^ 2`
    by `linear_combination d ^ 2 * E0_quad t U`, then `mul_nonneg_iff_of_pos_left`. Main bound: unfold,
    then `nlinarith [block_nonneg t U (x 0 + x 1) (x 2 + x 3) ht,
      mul_nonneg (sub_nonneg.mpr (E0_lt t U ht).2.le) (sq_nonneg (x 0 - x 1)),
      mul_nonneg (neg_nonneg.mpr (E0_lt t U ht).1.le) (sq_nonneg (x 2 - x 3))]`.
-/
