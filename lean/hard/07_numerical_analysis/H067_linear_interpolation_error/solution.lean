/- H067 | Linear interpolation error | 1-1.5 h | Rolle's theorem, auxiliary function, HasDerivAt, mathlib
GOAL
  The chord through `(a, f a)` and `(b, f b)` misses `f` at `x ∈ [a, b]` by at most `M/2 · (x - a)(b - x)` when
  `|f''| ≤ M` on `[a, b]`. Classic proof: an auxiliary function with three zeros `a, x, b`, then Rolle three times.

GUIDE
  Entries R1–R35: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Set

namespace H067

/- SKELETON · aux_deriv   (milestone 1; used in `interp_error_eq` for `hφ`)
  1. hid : HasDerivAt (fun x => x) 1 t                                      R1
  2. Build the derivative forward, in one `have`, from the inside out:
       chord  f a + s * (t - a)       from hid                              R2, R3, R4
       bump   (t - a) * (t - b)       from hid twice                        R2, R2, R5
       K * bump                                                             R3
       f t - chord - K * bump         from hf t and the two above           R6, R6
  3. What step 2 built has the right function but a derivative full of `* 1` and
     `1 * (t - b) + (t - a) * 1`: trade it for the stated one                R7, then ring
-/
-- MILESTONE (optional: change or delete)
-- The auxiliary function `φ t = (f t - chord t) - K (t - a)(t - b)` and its derivative.
theorem aux_deriv (f f' : ℝ → ℝ) (hf : ∀ t, HasDerivAt f (f' t) t) (a b s K t : ℝ) :
    HasDerivAt (fun t => f t - (f a + s * (t - a)) - K * ((t - a) * (t - b)))
      (f' t - s - K * (2 * t - a - b)) t := by
  have hid := hasDerivAt_id' t
  have := ((hf t).sub (((hid.sub_const a).const_mul s).const_add (f a))).sub
    (((hid.sub_const a).mul (hid.sub_const b)).const_mul K)
  exact this.congr_deriv (by ring)

/- SKELETON · interp_error_eq   (milestone 2; uses aux_deriv; used in linear_interp_error, step 4)
  1. Name the pieces, in this order:                                        R8
       s  := (f b - f a) / (b - a)                                    (the slope)
       hden : (x - a) * (x - b) ≠ 0                                         R9, R10
       K  := (f x - (f a + s * (x - a))) / ((x - a) * (x - b))   `with hK`  R8
       φ  := fun t => f t - (f a + s * (t - a)) - K * ((t - a) * (t - b))
       φ' := fun t => f' t - s - K * (2 * t - a - b)
  2. Derivatives:
       hφ  : ∀ t, HasDerivAt φ (φ' t) t                  milestone aux_deriv
       hφ' : ∀ t, HasDerivAt φ' (f'' t - 2 * K) t
             f' t - s from hf' t: R2;  K * (2 * t - a - b) from R1: R3, R2, R2, R3;
             their difference: R6;  then R7 with ring
  3. Continuity, cφ : Continuous φ and cφ' : Continuous φ':                 R11, R12
  4. The three zeros. First hsb : s * (b - a) = f b - f a                   R13, R10
       φ a = 0                                                              R14 (`simp [φ]` closes it)
       φ b = 0                                                              R14, R15 with hsb
       φ x = 0                                                              R14 (unfold K too), R13 with hden, ring
  5. Rolle three times, each as `obtain ⟨ξ, hξ, h⟩ := …`:                    R16, R17, R18, R19
       φ on [a, x] → ξ₁;   φ on [x, b] → ξ₂;
       φ' on [ξ₁, ξ₂] → η, where ξ₁ < ξ₂ comes from hξ₁.2 and hξ₂.1         R20, R21
  6. Give η, its membership in (a, b) (R20, R21 again), leave the equation: R22
  7. f'' η = 2 * K (linarith from the third Rolle), cancel the 2, unfold K,
     cancel the denominator:                                                R23, R24, rw [hK], R13
-/
-- MILESTONE (optional: change or delete)
-- The exact error at an interior point (the Cauchy remainder for linear interpolation).
theorem interp_error_eq (f f' f'' : ℝ → ℝ) (a b x : ℝ) (hax : a < x) (hxb : x < b)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : ∀ t, HasDerivAt f' (f'' t) t) :
    ∃ η ∈ Ioo a b, f x - (f a + (f b - f a) / (b - a) * (x - a)) = f'' η / 2 * ((x - a) * (x - b)) := by
  set s := (f b - f a) / (b - a)
  have hden : (x - a) * (x - b) ≠ 0 := mul_ne_zero (by linarith) (by linarith)
  set K := (f x - (f a + s * (x - a))) / ((x - a) * (x - b)) with hK
  set φ := fun t => f t - (f a + s * (t - a)) - K * ((t - a) * (t - b))
  set φ' := fun t => f' t - s - K * (2 * t - a - b)
  have hφ : ∀ t, HasDerivAt φ (φ' t) t := fun t => aux_deriv f f' hf a b s K t
  have hφ' : ∀ t, HasDerivAt φ' (f'' t - 2 * K) t := fun t =>
    (((hf' t).sub_const s).sub
      ((((hasDerivAt_id' t).const_mul 2).sub_const a).sub_const b |>.const_mul K)).congr_deriv (by ring)
  have cφ : Continuous φ := continuous_iff_continuousAt.mpr fun t => (hφ t).continuousAt
  have cφ' : Continuous φ' := continuous_iff_continuousAt.mpr fun t => (hφ' t).continuousAt
  -- WHY: `div_mul_cancel₀` instead of `field_simp`, which rewrites `s` and `K` in unhelpful ways here.
  have hsb : s * (b - a) = f b - f a := div_mul_cancel₀ _ (by linarith)
  have φa : φ a = 0 := by simp [φ]
  have φb : φ b = 0 := by simp only [φ]; linear_combination -hsb
  have φx : φ x = 0 := by simp only [φ, K]; rw [div_mul_cancel₀ _ hden]; ring
  obtain ⟨ξ₁, hξ₁, h1⟩ :=
    exists_hasDerivAt_eq_zero hax cφ.continuousOn (φa.trans φx.symm) fun t _ => hφ t
  obtain ⟨ξ₂, hξ₂, h2⟩ :=
    exists_hasDerivAt_eq_zero hxb cφ.continuousOn (φx.trans φb.symm) fun t _ => hφ t
  obtain ⟨η, hη, h3⟩ := exists_hasDerivAt_eq_zero (hξ₁.2.trans hξ₂.1) cφ'.continuousOn
    (h1.trans h2.symm) fun t _ => hφ' t
  refine ⟨η, ⟨hξ₁.1.trans hη.1, hη.2.trans hξ₂.2⟩, ?_⟩
  rw [show f'' η = 2 * K by linarith, mul_div_cancel_left₀ _ two_ne_zero, hK, div_mul_cancel₀ _ hden]

/- SKELETON · linear_interp_error
  Prove the milestones first: aux_deriv, then interp_error_eq (which uses it). Only interp_error_eq
  is used here.
  1. Split hx into h1 : a ≤ x and h2 : x ≤ b:                               R25
  2. Endpoint x = a: R26 on h1, R27 with `rfl`; both sides are 0:           simp
  3. Endpoint x = b: R26 on h2, R27 with `rfl`; cancel the slope's
     denominator (side goal by R10), then both sides are 0:                 R13, R10, simp
  4. Interior a < x < b: obtain η, hη, he from interp_error_eq              R19
  5. hpos : 0 ≤ (x - a) * (b - x)                                           R28, R10
  6. Rewrite the left side, in one `rw`: he, then
     (x - a) * (x - b) = -((x - a) * (b - x)) (R23 with ring), then         R29, R30, R31, R32, R33 (hpos)
  7. Strip the common factors, then use hM at η:                            R34, R35
-/
-- BEGIN SPEC
theorem linear_interp_error (f f' f'' : ℝ → ℝ) (a b x M : ℝ) (hx : x ∈ Icc a b)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : ∀ t, HasDerivAt f' (f'' t) t)
    (hM : ∀ t ∈ Icc a b, |f'' t| ≤ M) :
    |f x - (f a + (f b - f a) / (b - a) * (x - a))| ≤ M / 2 * ((x - a) * (b - x)) :=
-- END SPEC
  by
    obtain ⟨h1, h2⟩ := hx
    rcases h1.eq_or_lt with rfl | hax
    · simp
    rcases h2.eq_or_lt with rfl | hxb
    · rw [div_mul_cancel₀ _ (by linarith)]; simp
    obtain ⟨η, hη, he⟩ := interp_error_eq f f' f'' a b x hax hxb hf hf'
    have hpos : 0 ≤ (x - a) * (b - x) := mul_nonneg (by linarith) (by linarith)
    rw [he, show (x - a) * (x - b) = -((x - a) * (b - x)) by ring, abs_mul, abs_div, abs_two, abs_neg,
      abs_of_nonneg hpos]
    gcongr
    exact hM η (Ioo_subset_Icc_self hη)

end H067

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Endpoints first: at `x = a` and `x = b` both sides are 0 (R26, R27, then `simp`). For `a < x < b`, the
    chord error `g t = f t - (f a + s (t - a))` vanishes at `a` and `b`; subtract `K (t - a)(t - b)` with the
    constant `K` chosen so that `φ = g - K (t - a)(t - b)` also vanishes at `x`.
H2. `interp_error_eq`: Rolle (R16) on `[a, x]` and `[x, b]` gives `ξ₁ < ξ₂` with `φ' ξᵢ = 0`; Rolle on `φ'` over
    `[ξ₁, ξ₂]` gives `η` with `f'' η - 2 K = 0`. So `g x = K (x - a)(x - b) = f'' η / 2 · (x - a)(x - b)`.
    Main theorem: take absolute values of that equation and bound `|f'' η| ≤ M` with `hM` (R35).
H3. `set K := (f x - (f a + s * (x - a))) / ((x - a) * (x - b)) with hK`; `φ' t = f' t - s - K * (2 * t - a - b)`
    and `HasDerivAt φ' (f'' t - 2 * K) t` (R1–R7, `.congr_deriv (by ring)`). Zeros: `φ a = 0` by `simp [φ]`,
    `φ b = 0` by `simp only [φ]; linear_combination -hsb` with `hsb := div_mul_cancel₀ _ (by linarith)`,
    `φ x = 0` by `simp only [φ, K]; rw [div_mul_cancel₀ _ hden]; ring`. Final bound:
    `rw [he, show (x - a) * (x - b) = -((x - a) * (b - x)) by ring, abs_mul, abs_div, abs_two, abs_neg,
    abs_of_nonneg hpos]`, then `gcongr`.
-/
