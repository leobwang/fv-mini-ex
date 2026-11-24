/- H107 | Orthogonal null vectors are parallel | 45-60 min | lightlike vectors, norm of a difference, nlinarith, funext/match, physlib
GOAL
  A 4-vector `p` is null (lightlike) when `⟪p, p⟫ₘ = 0`. Show that two Minkowski-orthogonal null vectors are
  proportional: `⟪p, p⟫ₘ = ⟪q, q⟫ₘ = ⟪p, q⟫ₘ = 0` and `q ≠ 0` give `p = r • q` for some real `r`.

GUIDE
  Entries R1–R27: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct

open Lorentz Vector

namespace H107

/- SKELETON · time_ne_zero_of_null   (milestone 1: q ≠ 0 null ⇒ q⁰ ≠ 0; gives `hb` in parallel_of_null_orth)
  1. Assume h0 : q.timeComponent = 0; the goal becomes False:                     R1
  2. hq in components, then substitute h0:                                        R2, rw [h0] at hq
  3. hq becomes "the spatial part of q is 0":                                     R3
  4. Contradict hq0; the goal becomes q = 0:                                      R4
  5. q = 0 by components:                                                         R5 → R6
       time arm:  h0                                                              R7
       space arm: the i-th component of hq                                        R8
-/
-- MILESTONE (optional: change or delete)
/-- A nonzero null vector has a nonzero time component. -/
theorem time_ne_zero_of_null {d : ℕ} (q : Lorentz.Vector d) (hq : ⟪q, q⟫ₘ = 0) (hq0 : q ≠ 0) :
    q.timeComponent ≠ 0 := by
  intro h0
  rw [minkowskiProduct_self_eq_timeComponent_spatialPart, h0] at hq
  simp at hq
  apply hq0
  funext μ
  match μ with
  | Sum.inl 0 => exact h0
  | Sum.inr i => exact congrArg (· i) hq

/- SKELETON · key   (milestone 2: ‖q⁰ p⃗ - p⁰ q⃗‖² = 0; gives `h` in parallel_of_null_orth)
  1. The hypotheses in components (`rw … at hp hq`, `rw … at hpq`):              R2, R9
  2. Remove the norms around the real time components in hp, hq:                 R10
  3. Expand the goal (one rw; norm_smul twice):                                  R11, R12, R12, R13, R14
  4. Normalise the squares (one simp only):                                       R10 with R15
  5. hpq' : inner ℝ p⃗ q⃗ = p⁰ * q⁰ from hpq, and substitute it:                  R16, rw [hpq']
  6. The rest is polynomial arithmetic in p⁰, q⁰, ‖p⃗‖², ‖q⃗‖² using hp, hq:      R17
-/
-- MILESTONE (optional: change or delete)
/-- The key identity: `q⁰ p⃗ - p⁰ q⃗` has zero length. -/
theorem key {d : ℕ} (p q : Lorentz.Vector d) (hp : ⟪p, p⟫ₘ = 0) (hq : ⟪q, q⟫ₘ = 0)
    (hpq : ⟪p, q⟫ₘ = 0) :
    ‖q.timeComponent • p.spatialPart - p.timeComponent • q.spatialPart‖ ^ 2 = 0 := by
  rw [minkowskiProduct_self_eq_timeComponent_spatialPart] at hp hq
  rw [minkowskiProduct_eq_timeComponent_spatialPart] at hpq
  simp only [Real.norm_eq_abs, sq_abs] at hp hq
  rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs]
  have hpq' : inner ℝ p.spatialPart q.spatialPart = p.timeComponent * q.timeComponent := by linarith
  rw [hpq']
  nlinarith

/- SKELETON · ext_time_space   (milestone 3: p = q from time and space parts; used in parallel_of_null_orth)
  1. Componentwise:                                                               R5 → R6
       time arm:  h0                                                              R7
       space arm: the i-th component of hs                                        R8
-/
-- MILESTONE (optional: change or delete)
/-- A 4-vector is determined by its time component and its spatial part. -/
theorem ext_time_space {d : ℕ} (p q : Lorentz.Vector d) (h0 : p.timeComponent = q.timeComponent)
    (hs : p.spatialPart = q.spatialPart) : p = q := by
  funext μ
  match μ with
  | Sum.inl 0 => exact h0
  | Sum.inr i => exact congrArg (· i) hs

/- SKELETON · parallel_of_null_orth
  Prove milestones 1–3 first; this proof assembles them.
  1. hb : q.timeComponent ≠ 0 from milestone 1;  h from milestone 2:              have, have
  2. Turn h into q⁰ • p⃗ = p⁰ • q⃗ (one `rw … at h`):                             R18, R19, R20
  3. Witness r = p⁰ / q⁰; reduce to time and space with milestone 3:              R21
  4. Time goal: unfold (r • q).timeComponent, then clear the fraction (uses hb):  R22, R23
  5. Space goal: unfold (r • q).spatialPart, then in one rw:                       R22
       a / b → b⁻¹ * a, split the scalar, use h right to left, merge, cancel:    R24, R25 ←, rw [← h], R25, R26, R27
-/
-- BEGIN SPEC
theorem parallel_of_null_orth {d : ℕ} (p q : Lorentz.Vector d) (hp : ⟪p, p⟫ₘ = 0)
    (hq : ⟪q, q⟫ₘ = 0) (hq0 : q ≠ 0) (hpq : ⟪p, q⟫ₘ = 0) : ∃ r : ℝ, p = r • q :=
-- END SPEC
  by
    have hb := time_ne_zero_of_null q hq hq0
    have h := key p q hp hq hpq
    rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at h
    refine ⟨p.timeComponent / q.timeComponent, ext_time_space _ _ ?_ ?_⟩
    · change p.timeComponent = p.timeComponent / q.timeComponent * q.timeComponent
      field_simp
    · change p.spatialPart = (p.timeComponent / q.timeComponent) • q.spatialPart
      -- WHY: `h : q⁰ • p⃗ = p⁰ • q⃗`; multiply it by `(q⁰)⁻¹`.
      rw [div_eq_inv_mul, ← smul_smul, ← h, smul_smul, inv_mul_cancel₀ hb, one_smul]

end H107

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `a = p⁰`, `b = q⁰`. In components (R2, R9) the hypotheses say `a² = ‖p⃗‖²`, `b² = ‖q⃗‖²` and
    `a b = p⃗ · q⃗`. The candidate is `r = a / b`, which needs `b ≠ 0` (milestone 1: if `q⁰ = 0` then
    `‖q⃗‖ = 0`, so `q = 0`). Prove the three milestones in order, then assemble.
H2. Milestone 2: `‖b • p⃗ - a • q⃗‖² = b²‖p⃗‖² - 2ab (p⃗ · q⃗) + a²‖q⃗‖² = a²b² - 2a²b² + a²b² = 0` (R11–R17),
    so `b • p⃗ = a • q⃗` (R18–R20). Then compare `p` and `(a / b) • q` separately in time and in space
    (milestone 3, R21): time is `a = a / b * b`, space is `p⃗ = (b⁻¹ * a) • q⃗` (R22–R27).
H3. Milestone 1: after `intro h0` and `rw [minkowskiProduct_self_eq_timeComponent_spatialPart, h0] at hq`,
    `simp at hq` leaves `hq : (fun i => q (Sum.inr i)) = 0`; `apply hq0`, and the space arm is `congrArg (· i) hq`.
    Milestone 2: `rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right]`,
    `simp only [Real.norm_eq_abs, mul_pow, sq_abs]`, `rw [hpq']` with `hpq'` by `linarith`, then `nlinarith`.
    Main: `rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at h`, `refine ⟨a / b, ext_time_space _ _ ?_ ?_⟩`;
    the space part is `rw [div_eq_inv_mul, ← smul_smul, ← h, smul_smul, inv_mul_cancel₀ hb, one_smul]` after a `change`.
-/
