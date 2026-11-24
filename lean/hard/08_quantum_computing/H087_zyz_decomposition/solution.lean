/- H087 | ZYZ decomposition of a qubit gate | 2 h | unitary group, 2x2 matrices, polar form, Complex.arg, Real.arccos, linear_combination, mathlib
GOAL
  Every single-qubit unitary `U` is `e^{iα} R_z(β) R_y(γ) R_z(δ)` for some real angles `α β γ δ`
  (Nielsen–Chuang Thm 4.1), where `R_z(θ) = diag(e^{−iθ/2}, e^{iθ/2})` and `R_y(θ)` is the real
  rotation by `θ/2` (both defined below).

GUIDE
  Entries R1–R38: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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
/- SKELETON · unitary_struct
  Write a b c d for U 0 0, U 0 1, U 1 0, U 1 1 and conj for starRingEnd ℂ.
  1. Unitarity as an equation:                                               R1
       h1 : U * star U = 1
  2. Entries (0,0) and (1,0) of h1, then evaluate both at once:              R2, R2, R3
       e00 : a * conj a + b * conj b = 1      e10 : c * conj a + d * conj b = 0
  3. Expand the determinant:                                                  R4
  4. Split: prove the first two conjuncts inline, keep the last two:         R5
       each inline one by R6 on e00, e10 (multiply out lhs − rhs to find the coefficients)
  5. ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1: rewrite e00 (each lemma twice, `at e00`), then     R7, R8, R9
  6. ‖det‖ = 1: fold the determinant back (R4 right to left), then            R10 → R11
-/
/-- a 2×2 unitary `[[a, b], [c, d]]` with determinant `D` has `d = D·conj a`, `c = −D·conj b` -/
theorem unitary_struct (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    U 1 1 = U.det * starRingEnd ℂ (U 0 0) ∧ U 1 0 = -(U.det * starRingEnd ℂ (U 0 1)) ∧
      ‖U 0 0‖ ^ 2 + ‖U 0 1‖ ^ 2 = 1 ∧ ‖U.det‖ = 1 := by
  have h1 := Matrix.mem_unitaryGroup_iff.mp hU
  have e00 := congrFun (congrFun h1 0) 0
  have e10 := congrFun (congrFun h1 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
  rw [Matrix.det_fin_two]
  refine ⟨by linear_combination (-U 1 1) * e00 + U 0 1 * e10,
    by linear_combination (-U 1 0) * e00 + U 0 0 * e10, ?_, ?_⟩
  · rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq] at e00
    exact_mod_cast e00
  · rw [← Matrix.det_fin_two]
    exact CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hU)

-- MILESTONE (optional: change or delete)
/- SKELETON · zyz_product
  1. The merging form of exp_add as a named fact:                             R15
       e : ∀ x y : ℂ, cexp x * cexp y = cexp (x + y)
  2. Unfold Rz, Ry and multiply out, in one `simp only`:                      R12, R13, R14
  3. Four entry goals: `ext i j`, `fin_cases i <;> fin_cases j`, `simp`        (TACTIC_STATES)
     each has the shape  cexp (↑α * I) * (cexp u * c * cexp v) = cexp w * c
  4. In each goal (`<;>`): put the three exponentials side by side and c last,
     merge them with rw [e, e], strip `cexp` and `* c`, then `ring`:          R16, R15, R17
-/
theorem zyz_product (α β γ δ : ℝ) :
    Complex.exp (α * I) • (Rz β * Ry γ * Rz δ)
      = !![Complex.exp ((α - (β + δ) / 2 : ℝ) * I) * Real.cos (γ / 2),
            -(Complex.exp ((α - (β - δ) / 2 : ℝ) * I) * Real.sin (γ / 2));
           Complex.exp ((α + (β - δ) / 2 : ℝ) * I) * Real.sin (γ / 2),
            Complex.exp ((α + (β + δ) / 2 : ℝ) * I) * Real.cos (γ / 2)] := by
  have e : ∀ x y : ℂ, Complex.exp x * Complex.exp y = Complex.exp (x + y) :=
    fun x y => (Complex.exp_add x y).symm
  simp only [Rz, Ry, Matrix.mul_fin_two, Matrix.smul_of, mul_zero, zero_mul, add_zero, zero_add]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
  · rw [show ∀ a b c d : ℂ, a * (b * c * d) = a * b * d * c from fun a b c d => by ring, e, e]
    congr 2; ring

-- MILESTONE (optional: change or delete)
/- SKELETON · half_angle
  1. Cancel the 2:                                                            R18
  2. Both conjuncts at once with ⟨_, _⟩:
       cos: R19, side goal −1 ≤ r by R21;   sin: R20 (no side goal)
-/
theorem half_angle (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    Real.cos (2 * Real.arccos r / 2) = r ∧
      Real.sin (2 * Real.arccos r / 2) = Real.sqrt (1 - r ^ 2) := by
  rw [mul_div_cancel_left₀ _ two_ne_zero]
  exact ⟨Real.cos_arccos (by linarith) h1, Real.sin_arccos r⟩

-- MILESTONE (optional: change or delete)
/- SKELETON · polar_mul
  1. Polar form of D and of z, on the left side only:                         R23 with R22 (twice)
  2. rw [hD], then push conj through the product, the real cast, the exp:    R24, R25, R26
  3. Rewrite the right exponent as  ↑D.arg * I + conj (↑z.arg * I)
     (a `show … by simp; ring` fact), then split the exponential:            R16, R15
  4. Casts inward, then `ring`:                                               R27
-/
/-- polar form of `D · conj z` for a unit-modulus `D` -/
theorem polar_mul (D z : ℂ) (hD : ‖D‖ = 1) :
    D * starRingEnd ℂ z = Complex.exp (((D.arg - z.arg : ℝ) : ℂ) * I) * ‖z‖ := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I D, ← Complex.norm_mul_exp_arg_mul_I z]
  rw [hD, map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
    show (((D.arg - z.arg : ℝ) : ℂ) * I) = D.arg * I + starRingEnd ℂ (z.arg * I) by simp; ring,
    Complex.exp_add]
  push_cast; ring

/- SKELETON · zyz
  Prove the milestones first: unitary_struct (step 1), half_angle (step 3), zyz_product and
  polar_mul (step 6). Notation: a = U 0 0, b = U 0 1, D = U.det, φ = D.arg, θa = a.arg, θb = b.arg.
  1. Split milestone unitary_struct:                                          R28
       hd : U 1 1 = D * conj a,  hc : U 1 0 = -(D * conj b),  hab : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1,  hD : ‖D‖ = 1
  2. U as a literal, its second row replaced, then name a, b, D:             R29, rw [hd, hc], R30
  3. ha1 : ‖a‖ ≤ 1                                                             R31 (hints: norm_nonneg)
     ⟨hcos, hsin⟩ from half_angle ‖a‖ (norm_nonneg a) ha1                     R28
  4. hb : √(1 - ‖a‖ ^ 2) = ‖b‖: rewrite 1 − ‖a‖² as ‖b‖² (a fact proved by R21),  R16, then R32
  5. Three helper facts (each `∀`, proved after `intro`):
       hpi    : cexp (↑(x + Real.pi) * I) = -cexp (↑x * I)                    R27, R34, R15, R33, ring
       hmpi   : cexp (↑(x - Real.pi) * I) = -cexp (↑x * I)
                have h := hpi (x − π), R35 at h, then rw [h] and R36 (neg_neg)
       hpolar : cexp (↑z.arg * I) * ↑‖z‖ = z                                  R37, R22
  6. Choose the angles (solve the four phase equations; H3 has them):         R38
     rw [zyz_product, hcos, hsin, hb, polar_mul D a hD, polar_mul D b hD], then set φ θa θb   R30
  7. Turn each of the four exponent arguments into θa, θb + π, φ − θb − π, φ − θa
     (`show … by ring`, copying each left side from the goal):                 R16
     then in one rw: hpi (entry 0 1), hmpi (entry 1 0), hpolar (entry 0 0 becomes a),
     the signs of entry 0 1, hpolar again (it becomes b), the sign of entry 1 0:   R36
     rw closes the goal by rfl once the two literals agree entry by entry.
-/
-- BEGIN SPEC
theorem zyz (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ α β γ δ : ℝ, U = Complex.exp (α * I) • (Rz β * Ry γ * Rz δ) :=
-- END SPEC
  by
    obtain ⟨hd, hc, hab, hD⟩ := unitary_struct U hU
    rw [Matrix.eta_fin_two U, hd, hc]
    set a := U 0 0
    set b := U 0 1
    set D := U.det
    have ha1 : ‖a‖ ≤ 1 := by nlinarith [norm_nonneg a, norm_nonneg b]
    obtain ⟨hcos, hsin⟩ := half_angle ‖a‖ (norm_nonneg a) ha1
    have hb : Real.sqrt (1 - ‖a‖ ^ 2) = ‖b‖ := by
      rw [show 1 - ‖a‖ ^ 2 = ‖b‖ ^ 2 by linarith]; exact Real.sqrt_sq (norm_nonneg b)
    have hpi : ∀ x : ℝ,
        Complex.exp (((x + Real.pi : ℝ) : ℂ) * I) = -Complex.exp ((x : ℂ) * I) := by
      intro x; push_cast; rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]; ring
    have hmpi : ∀ x : ℝ,
        Complex.exp (((x - Real.pi : ℝ) : ℂ) * I) = -Complex.exp ((x : ℂ) * I) := by
      intro x; have h := hpi (x - Real.pi); rw [sub_add_cancel] at h; rw [h, neg_neg]
    have hpolar : ∀ z : ℂ, Complex.exp ((z.arg : ℂ) * I) * ‖z‖ = z := fun z => by
      rw [mul_comm]; exact Complex.norm_mul_exp_arg_mul_I z
    -- WHY: the extra `π` in β and δ turns `−e^{iπ}` into `+1` in the off-diagonal entries
    refine ⟨D.arg / 2, D.arg - a.arg - b.arg - Real.pi, 2 * Real.arccos ‖a‖,
      b.arg - a.arg + Real.pi, ?_⟩
    rw [zyz_product, hcos, hsin, hb, polar_mul D a hD, polar_mul D b hD]
    set φ := D.arg
    set θa := a.arg
    set θb := b.arg
    rw [show φ / 2 - (φ - θa - θb - Real.pi + (θb - θa + Real.pi)) / 2 = θa by ring,
      show φ / 2 - (φ - θa - θb - Real.pi - (θb - θa + Real.pi)) / 2 = θb + Real.pi by ring,
      show φ / 2 + (φ - θa - θb - Real.pi - (θb - θa + Real.pi)) / 2 = φ - θb - Real.pi by ring,
      show φ / 2 + (φ - θa - θb - Real.pi + (θb - θa + Real.pi)) / 2 = φ - θa by ring,
      hpi, hmpi, hpolar, neg_mul, neg_neg, hpolar, neg_mul]

end H087

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `U = [[a, b], [c, d]]` and `D = det U`. Unitarity fixes the second row from the first
    (`unitary_struct`: `d = D·conj a`, `c = −D·conj b`); multiplying out the rotations (`zyz_product`)
    shows each entry is "phase × cos(γ/2)" or "phase × sin(γ/2)". So take `cos(γ/2) = ‖a‖`,
    `sin(γ/2) = ‖b‖` (`half_angle`), put `a`, `b`, `D·conj a`, `D·conj b` in polar form (`polar_mul`),
    and match the phases with `arg`.
H2. `unitary_struct`: entries (0,0) and (1,0) of `U * star U = 1` (R1–R3), then `linear_combination` (R6)
    for the two row identities, R7–R9 for the norms, R10–R11 for `‖D‖`. `zyz_product`:
    `simp only [Rz, Ry, Matrix.mul_fin_two, Matrix.smul_of, mul_zero, zero_mul, add_zero, zero_add]`,
    `ext i j; fin_cases i <;> fin_cases j <;> simp`, then reorder (R16), merge with `exp_add` (R15),
    `congr 2; ring` (R17). `polar_mul`: `conv_lhs` + polar form (R22, R23), push `conj` inside (R24–R26).
    `zyz`: skeleton steps 1–7; the extra `π` in `β` and `δ` turns `−e^{iπ}` into `+1` off the diagonal.
H3. Coefficients: `linear_combination (-U 1 1) * e00 + U 0 1 * e10` and
    `linear_combination (-U 1 0) * e00 + U 0 0 * e10`. Angles: `α = φ/2`, `β = φ − θa − θb − π`,
    `γ = 2 * Real.arccos ‖a‖`, `δ = θb − θa + π` with `φ = arg D`, `θa = arg a`, `θb = arg b`; the four phases
    are then `θa`, `θb + π`, `φ − θb − π`, `φ − θa` (each by `ring`). `polar_mul` step 3:
    `show ((↑(D.arg - z.arg : ℝ) : ℂ) * I) = D.arg * I + starRingEnd ℂ (z.arg * I) by simp; ring`.
-/
