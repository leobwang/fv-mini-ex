/- M090 | Cauchy–Schwarz for expectations | 15-20 min | discriminant argument, integral algebra, integral_nonneg, mathlib
GOAL
  `(E[XY])² ≤ E[X²] E[Y²]`. For every real `t`, `E[(X - tY)²] ≥ 0` is a quadratic in `t` that never
  goes negative, so its discriminant is `≤ 0`.
BANNED: integral_mul_le_Lp_mul_Lq_of_nonneg, integral_mul_norm_le_Lp_mul_Lq, inner_mul_inner_self_le, real_inner_mul_inner_self_le, abs_real_inner_le_norm, real_inner_le_norm, norm_inner_le_norm

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M090

/- SKELETON · cauchy_schwarz
  1. MILESTONE first (used in step 2; its shape is exactly the hypothesis of R11):    have
       key : ∀ t : ℝ, 0 ≤ μ[fun ω => Y ω ^ 2] * (t * t) + (-2 * μ[fun ω => X ω * Y ω]) * t
                + μ[fun ω => X ω ^ 2]
     Proof of key:
       a. fix `t`                                                                      R1
       b. h0 : 0 ≤ μ[fun ω => (X ω - t * Y ω) ^ 2]                                      R2 with R3 (W1)
       c. e : (fun ω => (X ω - t * Y ω) ^ 2) = fun ω => A ω + B ω + C ω, where
            A = (t * t) * Y², B = (-2 * t) * (X * Y), C = X²                            R4, ring (W2)
       d. one `have` per integrability fact, with its explicit `fun ω => …` type:
            i1 for A, i2 for B (from hY2, hXY), i3 for A + B (from i1, i2)              R6, R6, R7
       e. rewrite h0, all `at h0`: integrand, split (A + B) + C, split A + B,
            pull out both constants                                                    R5 → R8 → R8 → R9 → R9
       f. h0 and the goal are the same up to reordering products                       R10
  2. Discriminant of key: context gains `this : discrim a b c ≤ 0`                     R11
  3. Unfold `discrim` in `this`                                                        R12
  4. Close: the goal is `this` divided by 4                                            R13
-/
-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem cauchy_schwarz {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X Y : Ω → ℝ) (hX2 : Integrable (fun ω => X ω ^ 2) μ) (hY2 : Integrable (fun ω => Y ω ^ 2) μ)
    (hXY : Integrable (fun ω => X ω * Y ω) μ) :
    (μ[fun ω => X ω * Y ω]) ^ 2 ≤ μ[fun ω => X ω ^ 2] * μ[fun ω => Y ω ^ 2] :=
-- END SPEC
  by
    have key : ∀ t : ℝ, 0 ≤ μ[fun ω => Y ω ^ 2] * (t * t) + (-2 * μ[fun ω => X ω * Y ω]) * t
        + μ[fun ω => X ω ^ 2] := by
      intro t
      have h0 : 0 ≤ μ[fun ω => (X ω - t * Y ω) ^ 2] := integral_nonneg fun ω => sq_nonneg _
      have e : (fun ω => (X ω - t * Y ω) ^ 2)
          = fun ω => (t * t) * Y ω ^ 2 + (-2 * t) * (X ω * Y ω) + X ω ^ 2 := by
        funext ω; ring
      have i1 : Integrable (fun ω => (t * t) * Y ω ^ 2) μ := hY2.const_mul _
      have i2 : Integrable (fun ω => (-2 * t) * (X ω * Y ω)) μ := hXY.const_mul _
      have i3 : Integrable (fun ω => (t * t) * Y ω ^ 2 + (-2 * t) * (X ω * Y ω)) μ := i1.add i2
      rw [e, integral_add i3 hX2, integral_add i1 i2, integral_const_mul, integral_const_mul] at h0
      linarith
    have := discrim_le_zero key
    rw [discrim] at this
    nlinarith

end M090

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Think of `q(t) = E[(X - tY)²] = E[Y²] t² - 2 E[XY] t + E[X²]`: it is `≥ 0` for every real `t`
    (an integral of a square, R2 + R3). Mathlib's `discrim_le_zero` (R11) turns "a quadratic that is
    never negative" into "its discriminant `b² - 4ac` is `≤ 0`", which is the claim times 4.
H2. Prove the milestone `key` of the SKELETON first. Start from
    `h0 : 0 ≤ μ[fun ω => (X ω - t * Y ω) ^ 2] := integral_nonneg fun ω => sq_nonneg _`, rewrite its
    integrand into `(t * t) * Y ω ^ 2 + (-2 * t) * (X ω * Y ω) + X ω ^ 2` (`funext ω; ring`), split the
    integral with `integral_add` and pull the constants out with `integral_const_mul`, then `linarith`.
    After `key`: `discrim_le_zero key`, unfold `discrim`, `nlinarith`.
H3. With `i1 : Integrable (fun ω => (t * t) * Y ω ^ 2) μ := hY2.const_mul _`, `i2` likewise from `hXY`,
    and `i3 : Integrable (fun ω => (t * t) * Y ω ^ 2 + (-2 * t) * (X ω * Y ω)) μ := i1.add i2`:
    `rw [e, integral_add i3 hX2, integral_add i1 i2, integral_const_mul, integral_const_mul] at h0; linarith`.
    Finish with `have := discrim_le_zero key; rw [discrim] at this; nlinarith`.
-/
