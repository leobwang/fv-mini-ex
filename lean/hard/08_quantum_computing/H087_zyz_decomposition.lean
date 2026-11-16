/- H087 | ZYZ decomposition of a qubit gate | 2 h | unitary group, 2x2 matrices, polar form, Complex.arg, Real.arccos, linear_combination, mathlib
GOAL
  Every single-qubit unitary `U` is `e^{iα} R_z(β) R_y(γ) R_z(δ)` for some real angles `α β γ δ`
  (Nielsen–Chuang Thm 4.1), where `R_z(θ) = diag(e^{−iθ/2}, e^{iθ/2})` and `R_y(θ)` is the real
  rotation by `θ/2` (both defined below).

REFERENCE
  -- `!![a, b; c, d]` = 2x2 matrix literal (rows split by `;`);  `c • M` = scalar times matrix;  `I` = `Complex.I` (via `open Complex`)
  -- `star A` = `Aᴴ` (conjugate transpose);  `starRingEnd ℂ z` = complex conjugate of `z`;  `‖z‖` = modulus;  `z.arg ∈ (-π, π]`
  #check Matrix.mem_unitaryGroup_iff        -- A ∈ unitaryGroup n α ↔ A * star A = 1
  example (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) : ‖U.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hU)
  #check Matrix.eta_fin_two                 -- A = !![A 0 0, A 0 1; A 1 0, A 1 1]     (and `Matrix.det_fin_two`)
  #check Matrix.mul_fin_two                 -- !![a,b;c,d] * !![e,f;g,h] = !![ae+bg, af+bh; ce+dg, cf+dh]   (and `Matrix.smul_of`)
  #check Complex.norm_mul_exp_arg_mul_I     -- (x : ℂ) : ‖x‖ * cexp (x.arg * I) = x       (polar form; also for x = 0)
  #check Complex.mul_conj                   -- z * conj z = ↑(normSq z)  (a real cast to ℂ; finish with exact_mod_cast)  (then `Complex.normSq_eq_norm_sq : normSq z = ‖z‖ ^ 2`)
  #check Real.cos_arccos                    -- -1 ≤ x → x ≤ 1 → cos (arccos x) = x    (and `Real.sin_arccos x : sin (arccos x) = √(1 - x ^ 2)`)
  #check Complex.exp_pi_mul_I               -- cexp (π * I) = -1      (and `Complex.exp_add`, `Complex.exp_conj : cexp (conj x) = conj (cexp x)`)
  example (x y : ℂ) (h : x * y = 1) : x * y * 2 = 2 := by linear_combination 2 * h
  -- entries: `have e := congrFun (congrFun h 1) 0; simp [Matrix.mul_apply, Fin.sum_univ_two] at e`
-/
import Mathlib

open Matrix Complex

namespace H087

-- BEGIN SPEC
/-- `R_z(θ) = exp(−iθZ/2) = diag(e^{−iθ/2}, e^{iθ/2})` -/
noncomputable def Rz (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-(θ / 2 : ℂ) * I), 0; 0, Complex.exp ((θ / 2 : ℂ) * I)]

/-- `R_y(θ) = exp(−iθY/2)`, a real rotation matrix by angle `θ/2` -/
noncomputable def Ry (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos (θ / 2) : ℂ), -(Real.sin (θ / 2) : ℂ); (Real.sin (θ / 2) : ℂ), (Real.cos (θ / 2) : ℂ)]
-- END SPEC

-- MILESTONE (optional: change or delete)
/-- a 2×2 unitary `[[a, b], [c, d]]` with determinant `D` has `d = D·conj a`, `c = −D·conj b` -/
theorem unitary_struct (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    U 1 1 = U.det * starRingEnd ℂ (U 0 0) ∧ U 1 0 = -(U.det * starRingEnd ℂ (U 0 1)) ∧
      ‖U 0 0‖ ^ 2 + ‖U 0 1‖ ^ 2 = 1 ∧ ‖U.det‖ = 1 := by
  sorry

-- MILESTONE (optional: change or delete)
theorem zyz_product (α β γ δ : ℝ) :
    Complex.exp (α * I) • (Rz β * Ry γ * Rz δ)
      = !![Complex.exp ((α - (β + δ) / 2 : ℝ) * I) * Real.cos (γ / 2),
            -(Complex.exp ((α - (β - δ) / 2 : ℝ) * I) * Real.sin (γ / 2));
           Complex.exp ((α + (β - δ) / 2 : ℝ) * I) * Real.sin (γ / 2),
            Complex.exp ((α + (β + δ) / 2 : ℝ) * I) * Real.cos (γ / 2)] := by
  sorry

-- MILESTONE (optional: change or delete)
theorem half_angle (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    Real.cos (2 * Real.arccos r / 2) = r ∧
      Real.sin (2 * Real.arccos r / 2) = Real.sqrt (1 - r ^ 2) := by
  sorry

-- MILESTONE (optional: change or delete)
/-- polar form of `D · conj z` for a unit-modulus `D` -/
theorem polar_mul (D z : ℂ) (hD : ‖D‖ = 1) :
    D * starRingEnd ℂ z = Complex.exp (((D.arg - z.arg : ℝ) : ℂ) * I) * ‖z‖ := by
  sorry

-- BEGIN SPEC
theorem zyz (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ α β γ δ : ℝ, U = Complex.exp (α * I) • (Rz β * Ry γ * Rz δ) :=
-- END SPEC
  sorry

end H087

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `U = [[a, b], [c, d]]` and `D = det U`. Unitarity pins down the second row from the first (milestone 1); multiplying out the product (milestone 2) shows each entry is "phase × cos(γ/2)" or "phase × sin(γ/2)". So take `cos(γ/2) = ‖a‖`, `sin(γ/2) = ‖b‖`, and match the phases with `arg`.
H2. Milestone 1: from `U * star U = 1` take the entries `(0,0)`: `a a* + b b* = 1` and `(1,0)`: `c a* + d b* = 0`; then `d − (ad − bc)a*` and `c + (ad − bc)b*` are linear combinations of those two (`linear_combination`). Milestone 2: `simp only [Rz, Ry, Matrix.mul_fin_two, Matrix.smul_of, ...]`, `ext i j; fin_cases i <;> fin_cases j <;> simp`, then merge the three exponentials with `Complex.exp_add`. Milestone 4: rewrite `D` and `z` in polar form (`conv_lhs => rw [← norm_mul_exp_arg_mul_I D, ...]`).
H3. Choose `α = φ/2`, `β = φ − θa − θb − π`, `γ = 2 arccos ‖a‖`, `δ = θb − θa + π` with `φ = arg D`, `θa = arg a`, `θb = arg b`. Then the four phases are `θa`, `θb + π`, `φ − θb − π`, `φ − θa` (each by `ring`), and the `±π` turns the minus signs into `e^{iπ} = −1`. Start with `rw [Matrix.eta_fin_two U, hd, hc]`, and `‖b‖ = √(1 − ‖a‖²)` from `Real.sqrt_sq`.
-/
