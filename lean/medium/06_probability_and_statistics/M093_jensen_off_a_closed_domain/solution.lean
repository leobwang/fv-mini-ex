/- M093 | Jensen off a closed domain: E[1/X] ≥ 1/E[X] | 15 min | convexity, tangent line, integral_mono, integral_pos_iff_support_of_nonneg, mathlib
GOAL
  For a strictly positive `X` with `X` and `1/X` integrable: `1 / E[X] ≤ E[1 / X]` (Jensen for the convex
  map `x ↦ 1/x` on `(0, ∞)`). Integrate the tangent line of `1/x` at `m = E[X]`, which lies below `1/x`.

GUIDE
  Entries R1–R22: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M093

/- SKELETON · jensen_inv
  1. FIRST, before naming anything: hm : 0 < μ[X]
       rewrite: 0 < ∫ X ↔ 0 < μ (support X); arguments `0 ≤ X` and hX      R1 with R2
       have : Function.support X = Set.univ             R3, then `simp` with R5 (simp does R4)
       close 0 < μ (support X) with simp and that fact                       R6 (applied by simp)
  2. Name the mean: set m := μ[X]   (hm becomes 0 < m)                       R7
  3. Tangent line at m lies below 1/x:
       hpt : ∀ ω, 2 / m - X ω / m ^ 2 ≤ (X ω)⁻¹
       intro ω, have hx := hpos ω (field_simp needs it)
       left side → one fraction; side goals by hm.ne' and positivity          R8 with R5, R9
       clear that denominator                                                 R10 with R9
       clear the rest                                                         R11
       finish: it is (X ω - m)² ≥ 0                                           R13 with R12
  4. hl : Integrable (fun ω => 2 / m - X ω / m ^ 2) μ                         R15 of R14, R16
  5. Two-step chain  m⁻¹ = μ[fun ω => 2 / m - X ω / m ^ 2]  ≤  μ[fun ω => (X ω)⁻¹]:   R17
       `=` step: h2 : μ[fun ω => X ω / m ^ 2] = m / m ^ 2 as a `have`          R18
                 split the integral, rw [h2], the constant                    R19 with R14, R16; R20
                 μ.real univ • c → c                                          R21
                 clear denominators, then `ring`                              R11
       `≤` step: integrate hpt, naming the function f                         R22 with hl, hinv, hpt
-/
-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem jensen_inv {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hpos : ∀ ω, 0 < X ω) (hX : Integrable X μ)
    (hinv : Integrable (fun ω => (X ω)⁻¹) μ) :
    (μ[X])⁻¹ ≤ μ[fun ω => (X ω)⁻¹] :=
-- END SPEC
  by
    have hm : 0 < μ[X] := by
      rw [integral_pos_iff_support_of_nonneg (fun ω => (hpos ω).le) hX]
      have : Function.support X = Set.univ := by
        ext ω; simp [(hpos ω).ne']
      simp [this]
    set m := μ[X]
    -- the tangent line of `x ↦ 1/x` at `m` lies below the graph on `(0, ∞)`
    have hpt : ∀ ω, 2 / m - X ω / m ^ 2 ≤ (X ω)⁻¹ := by
      intro ω
      have hx := hpos ω
      rw [div_sub_div _ _ hm.ne' (by positivity), div_le_iff₀ (by positivity)]
      field_simp
      nlinarith [sq_nonneg (X ω - m)]
    have hl : Integrable (fun ω => 2 / m - X ω / m ^ 2) μ :=
      (integrable_const _).sub (hX.div_const _)
    calc m⁻¹ = μ[fun ω => 2 / m - X ω / m ^ 2] := by
          have h2 : μ[fun ω => X ω / m ^ 2] = m / m ^ 2 := integral_div _ _
          rw [integral_sub (integrable_const _) (hX.div_const _), h2, integral_const]
          simp only [probReal_univ, one_smul]
          field_simp
          ring
      _ ≤ μ[fun ω => (X ω)⁻¹] := integral_mono (f := fun ω => 2 / m - X ω / m ^ 2) hl hinv hpt

end M093

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Jensen's proof for `1/x` by hand: the tangent line `ℓ(x) = 2/m - x/m²` of `1/x` at `m = E X` lies below
    `1/x` on `(0, ∞)` and has `E ℓ(X) = 1/m`. You need `m > 0` first: `X > 0` everywhere, so its support is
    all of `Ω`, which has measure 1.
H2. `hm` by `integral_pos_iff_support_of_nonneg` (R1) and `Function.support X = Set.univ` (R3–R6); then
    `set m := μ[X]` (R7). The pointwise bound `hpt` multiplied out is `(X ω - m)² ≥ 0` (R8–R13). Finish with a
    `calc`: the `=` step by linearity (R18–R21, R11), the `≤` step by `integral_mono` (R22).
H3. `rw [div_sub_div _ _ hm.ne' (by positivity), div_le_iff₀ (by positivity)]; field_simp;
    nlinarith [sq_nonneg (X ω - m)]` proves `hpt`. In the `=` step,
    `have h2 : μ[fun ω => X ω / m ^ 2] = m / m ^ 2 := integral_div _ _`, then
    `rw [integral_sub (integrable_const _) (hX.div_const _), h2, integral_const]`. Last step:
    `integral_mono (f := fun ω => 2 / m - X ω / m ^ 2) hl hinv hpt`.
-/
