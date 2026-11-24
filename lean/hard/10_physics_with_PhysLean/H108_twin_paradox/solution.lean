/- H108 | Twin paradox: the travelling twin is younger | 1-1.5 h | causal cones, reverse triangle inequality, Real.sqrt, physlib
GOAL
  In physlib's `InstantaneousTwinParadox`, twin A goes straight from `startPoint` to `endPoint`; twin B goes via
  `twinBMid` (each event causally after the previous). physlib states "A is older" only informally. Prove it:
  `0 ≤ T.ageGap`, i.e. τ(start, end) ≥ τ(start, mid) + τ(mid, end) (reverse triangle inequality).

GUIDE
  Entries R1–R29: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.Relativity.Special.TwinParadox.Basic

open Lorentz Vector SpecialRelativity

namespace H108

/- SKELETON · future_causal   (milestone 1: causal future ⇒ ‖Δx⃗‖ ≤ Δt; used twice in ageGap_nonneg)
  1. key : 0 ≤ ⟪q - p, q - p⟫ₘ ∧ 0 ≤ (q - p).timeComponent, by cases on `h`:      R1
       timelike case:  R2, then `.le` on both facts                               R4
       lightlike case: R3, then `.ge` on the first; the second is `h2` itself      R4
  2. Split `key` into h1, h2:                                                     R5
  3. `h1` in components (`rw … at h1`):                                           R6
  4. h3 : ‖(q - p).spatialPart‖ ^ 2 ≤ (q - p).timeComponent ^ 2 from h1:          R9 (simp does R7, R8)
  5. From the squares to the values (uses h2); take the right half:               R10
-/
-- MILESTONE (optional: change or delete)
/-- A causally later event lies inside or on the future cone: `‖Δx⃗‖ ≤ Δt`. -/
theorem future_causal {d : ℕ} {p q : SpaceTime d} (h : causallyFollows p q) :
    ‖(q - p).spatialPart‖ ≤ (q - p).timeComponent := by
  have key : 0 ≤ ⟪q - p, q - p⟫ₘ ∧ 0 ≤ (q - p).timeComponent := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨((timeLike_iff_norm_sq_pos _).mp h1).le, h2.le⟩
    · exact ⟨((lightLike_iff_norm_sq_zero _).mp h1).ge, h2⟩
  obtain ⟨h1, h2⟩ := key
  rw [minkowskiProduct_self_eq_timeComponent_spatialPart] at h1
  have h3 : ‖(q - p).spatialPart‖ ^ 2 ≤ (q - p).timeComponent ^ 2 := by
    simpa [sq_abs] using h1
  exact (abs_le_of_sq_le_sq' h3 h2).2

/- SKELETON · reverse_cauchy_schwarz   (milestone 2: √⟪u,u⟫ₘ √⟪v,v⟫ₘ ≤ ⟪u,v⟫ₘ; used in milestone 3)
  1. Name the four reals a = u⁰, b = v⁰, c = ‖u⃗‖, e = ‖v⃗‖:                        R11 (four times)
  2. hc : 0 ≤ c, he : 0 ≤ e:                                                      R12
  3. huu : ⟪u, u⟫ₘ = a ^ 2 - c ^ 2 (and hvv for v):                               R6, then simp [a, c, sq_abs] (R11, R7)
  4. huv : a * b - c * e ≤ ⟪u, v⟫ₘ:                                               R13, then R15 with R14
  5. hnn : 0 ≤ a * b - c * e:                                                     R16
  6. Goal: rw huu, hvv; merge the roots (side goal 0 ≤ a ^ 2 - c ^ 2 by R16):     rw [huu, hvv], R17
  7. Pass through a * b - c * e using huv:                                        R18
  8. Square (uses hnn); the rest is (ab - ce)² - (a² - c²)(b² - e²) = (ae - bc)²: R19, then R16 with R20
-/
-- MILESTONE (optional: change or delete)
/-- Reverse Cauchy–Schwarz for future causal vectors. -/
theorem reverse_cauchy_schwarz {d : ℕ} (u v : Lorentz.Vector d)
    (hu : ‖u.spatialPart‖ ≤ u.timeComponent) (hv : ‖v.spatialPart‖ ≤ v.timeComponent) :
    √⟪u, u⟫ₘ * √⟪v, v⟫ₘ ≤ ⟪u, v⟫ₘ := by
  set a := u.timeComponent
  set b := v.timeComponent
  set c := ‖u.spatialPart‖
  set e := ‖v.spatialPart‖
  have hc : 0 ≤ c := norm_nonneg _
  have he : 0 ≤ e := norm_nonneg _
  have huu : ⟪u, u⟫ₘ = a ^ 2 - c ^ 2 := by
    rw [minkowskiProduct_self_eq_timeComponent_spatialPart]; simp [a, c, sq_abs]
  have hvv : ⟪v, v⟫ₘ = b ^ 2 - e ^ 2 := by
    rw [minkowskiProduct_self_eq_timeComponent_spatialPart]; simp [b, e, sq_abs]
  have huv : a * b - c * e ≤ ⟪u, v⟫ₘ := by
    rw [minkowskiProduct_eq_timeComponent_spatialPart]
    linarith [real_inner_le_norm u.spatialPart v.spatialPart]
  have hnn : 0 ≤ a * b - c * e := by nlinarith
  rw [huu, hvv, ← Real.sqrt_mul (by nlinarith)]
  refine le_trans ?_ huv
  rw [Real.sqrt_le_left hnn]
  -- WHY: (ab - ce)² - (a² - c²)(b² - e²) = (ae - bc)².
  nlinarith [sq_nonneg (a * e - b * c)]

/- SKELETON · reverse_triangle   (milestone 3: √⟪u,u⟫ₘ + √⟪v,v⟫ₘ ≤ √⟪u+v,u+v⟫ₘ; used in ageGap_nonneg)
  1. h := milestone 2 applied to u v hu hv                                        have
  2. hU : 0 ≤ ⟪u, u⟫ₘ (and hV for v):                                             R6, R7 (simp only), R16 with R12
  3. Square the goal:                                                             R21
  4. e : ⟪u + v, u + v⟫ₘ = ⟪u, u⟫ₘ + 2 * ⟪u, v⟫ₘ + ⟪v, v⟫ₘ:                    simp with R22, R23, then ring
  5. rw [e], expand the square, remove the roots (uses hU, hV):                   R24, R25
  6. Finish from h:                                                               R15
-/
-- MILESTONE (optional: change or delete)
/-- Reverse triangle inequality for future causal vectors. -/
theorem reverse_triangle {d : ℕ} (u v : Lorentz.Vector d)
    (hu : ‖u.spatialPart‖ ≤ u.timeComponent) (hv : ‖v.spatialPart‖ ≤ v.timeComponent) :
    √⟪u, u⟫ₘ + √⟪v, v⟫ₘ ≤ √⟪u + v, u + v⟫ₘ := by
  have h := reverse_cauchy_schwarz u v hu hv
  have hU : 0 ≤ ⟪u, u⟫ₘ := by
    rw [minkowskiProduct_self_eq_timeComponent_spatialPart]
    simp only [Real.norm_eq_abs, sq_abs]
    nlinarith [norm_nonneg u.spatialPart]
  have hV : 0 ≤ ⟪v, v⟫ₘ := by
    rw [minkowskiProduct_self_eq_timeComponent_spatialPart]
    simp only [Real.norm_eq_abs, sq_abs]
    nlinarith [norm_nonneg v.spatialPart]
  apply Real.le_sqrt_of_sq_le
  have e : ⟪u + v, u + v⟫ₘ = ⟪u, u⟫ₘ + 2 * ⟪u, v⟫ₘ + ⟪v, v⟫ₘ := by
    simp [map_add, minkowskiProduct_symm v u]; ring
  rw [e, add_sq, Real.sq_sqrt hU, Real.sq_sqrt hV]
  linarith

/- SKELETON · ageGap_nonneg
  Prove milestones 1–3 first; this proof only assembles them.
  1. Unfold to three square roots:                                                R26
  2. h := milestone 3 with u = T.twinBMid - T.startPoint, v = T.endPoint - T.twinBMid;
     its two cone hypotheses are milestone 1 applied to two structure fields:     R27
  3. In h, rewrite u + v to T.endPoint - T.startPoint:                            R29 (R28)
  4. Finish from h:                                                               R15
-/
-- BEGIN SPEC
theorem ageGap_nonneg (T : InstantaneousTwinParadox) : 0 ≤ T.ageGap :=
-- END SPEC
  by
    unfold InstantaneousTwinParadox.ageGap InstantaneousTwinParadox.properTimeTwinA
      InstantaneousTwinParadox.properTimeTwinB SpaceTime.properTime
    have h := reverse_triangle (T.twinBMid - T.startPoint) (T.endPoint - T.twinBMid)
      (future_causal T.twinBMid_causallyFollows_startPoint)
      (future_causal T.endPoint_causallyFollows_twinBMid)
    rw [show T.twinBMid - T.startPoint + (T.endPoint - T.twinBMid) = T.endPoint - T.startPoint by
      abel] at h
    linarith

end H108

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Put `u = mid - start` and `v = end - mid`; then `u + v = end - start`, and the claim is
    `√⟪u, u⟫ₘ + √⟪v, v⟫ₘ ≤ √⟪u + v, u + v⟫ₘ` for two vectors in the closed future cone `‖w⃗‖ ≤ w⁰`
    (milestone 1 turns `causallyFollows` into that cone condition). Prove the milestones in order.
H2. Square both sides (R21): it reduces to `√⟪u, u⟫ₘ √⟪v, v⟫ₘ ≤ ⟪u, v⟫ₘ` (milestone 2). With
    `a = u⁰, b = v⁰, c = ‖u⃗‖, e = ‖v⃗‖`: `⟪u, u⟫ₘ = a² - c²`, `⟪v, v⟫ₘ = b² - e²` (R6, R7),
    `⟪u, v⟫ₘ ≥ ab - ce ≥ 0` (R13, R14), and `(a² - c²)(b² - e²) ≤ (ab - ce)²` since the difference is `(ae - bc)²`.
H3. Milestone 1: `rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩`, `((timeLike_iff_norm_sq_pos _).mp h1).le`, end with
    `(abs_le_of_sq_le_sq' h3 h2).2`. Milestone 2: `rw [huu, hvv, ← Real.sqrt_mul (by nlinarith)]`,
    `refine le_trans ?_ huv`, `rw [Real.sqrt_le_left hnn]`, `nlinarith [sq_nonneg (a * e - b * c)]`.
    Milestone 3: `apply Real.le_sqrt_of_sq_le`, `simp [map_add, minkowskiProduct_symm v u]; ring` for the
    expansion, `rw [e, add_sq, Real.sq_sqrt hU, Real.sq_sqrt hV]`. Main: unfold, `have h := reverse_triangle …`,
    `rw [show … = T.endPoint - T.startPoint by abel] at h`, `linarith`.
-/
