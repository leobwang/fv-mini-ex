/- M108 | cos on [0,1]: contraction and the Dottie number | 15-20 min | mean value theorem, Convex, trig bounds, IVT, ExistsUnique, mathlib
GOAL
  `cos` maps [0,1] into itself and is Lipschitz there with constant `sin 1 < 1` (mean value theorem:
  `|cos'| = |sin| ≤ sin 1` on [0,1]). Payoff: `cos p = p` has exactly one solution in [0,1] (≈ 0.739).

GUIDE
  Entries R1–R25: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M108

/- SKELETON · cos_maps_to
  1. Name the point and split its membership: x, h0 : 0 ≤ x, h1 : x ≤ 1          R1
  2. The goal `Real.cos x ∈ Set.Icc 0 1` is a pair:                              R2
  3. `0 ≤ Real.cos x`: reduce to `x ∈ Set.Icc (-(π / 2)) (π / 2)`, again a pair   R3, R2
       each half from h0 / h1 and a fact about π                                 R5
  4. `Real.cos x ≤ 1`:                                                           R4
-/
-- BEGIN SPEC
theorem cos_maps_to : Set.MapsTo Real.cos (Set.Icc 0 1) (Set.Icc 0 1) :=
-- END SPEC
  sorry

/- SKELETON · cos_contracts
  1. Bound the derivative of cos on [0,1] FIRST (the lemma in step 2 needs it), with `have … := by`:
       hd : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖-Real.sin t‖ ≤ Real.sin 1
     its proof: unpack t                                                          R1
                ‖-sin t‖ → ‖sin t‖ → |sin t| → sin t                              R10 → R11 → R12
                sin t ≤ sin 1 (sin increases on [-π/2, π/2])                      R14, R5
                R12's side goal 0 ≤ sin t (second goal, or inline in R12)         R13, R5
  2. The mean value bound as a fact `this`:                                       R9
     its arguments in order: the derivative of cos within the interval (R6 → R7),
       `hd`, convexity (R8), hy, hx
     (membership of y first, so it reads ‖cos x - cos y‖ ≤ sin 1 * ‖x - y‖)
  3. Norms → absolute values, close with `this`:                                 R15
-/
-- BEGIN SPEC
theorem cos_contracts (x y : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1) :
    |Real.cos x - Real.cos y| ≤ Real.sin 1 * |x - y| :=
-- END SPEC
  sorry

/- SKELETON · sin_one_lt_one
  1. sin x < x for 0 < x, at x = 1:                                               R16, R17
-/
-- BEGIN SPEC
theorem sin_one_lt_one : Real.sin 1 < 1 :=
-- END SPEC
  sorry

/- SKELETON · dottie_unique   (uses cos_contracts and sin_one_lt_one)
  1. Existence FIRST, by the IVT for `fun x => Real.cos x - x` (it goes down on [0,1]):
       obtain p, hp : p ∈ Set.Icc 0 1, hfix : Real.cos p - p = 0                  R18
     its arguments: `0 ≤ 1` (norm_num), continuity (R19),
       endpoints `Real.cos 1 - 1 ≤ 0` (R4, R5) and `0 ≤ Real.cos 0 - 0` (R20)
  2. Witness p, proof ⟨hp, cos p = p from hfix (R5)⟩, then a second point q:     R21
       context hq : q ∈ Set.Icc 0 1, hqfix : Real.cos q = q;  goal q = p
  3. Contraction at q and p (cos_contracts), then substitute both fixed points:  R22
       hc : |q - p| ≤ Real.sin 1 * |q - p|
  4. h0 : |q - p| ≤ 0, from hc, |q - p| ≥ 0 and sin_one_lt_one:                  R23, R24
  5. |q - p| ≤ 0 → q - p = 0 → q = p:                                            R25, R5
-/
-- BEGIN SPEC
theorem dottie_unique : ∃! p, p ∈ Set.Icc (0:ℝ) 1 ∧ Real.cos p = p :=
-- END SPEC
  sorry

end M108

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. [0,1] sits inside [0, π/2] because π > 3 (R5), so `cos ≥ 0` (R3) and `0 ≤ sin t ≤ sin 1` for
    `t ∈ [0,1]` (R13, R14: sin increases on [-π/2, π/2]); `sin 1 < 1` because `sin x < x` for `x > 0` (R16).
    Dottie: existence by the IVT (R18), uniqueness because `cos` contracts by the factor `sin 1 < 1`.
H2. `cos_contracts`: prove `hd : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖-Real.sin t‖ ≤ Real.sin 1`, apply the MVT bound (R9)
    with `f' := fun t => -Real.sin t`, `C := Real.sin 1`, `s := Set.Icc 0 1`, then `simpa [Real.norm_eq_abs]`.
    `dottie_unique`: existence by IVT on `fun x => Real.cos x - x`;
    uniqueness: two fixed points `p, q` give `|q - p| ≤ sin 1 * |q - p|`, which forces `|q - p| ≤ 0`.
H3. MVT: `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun t _ => (Real.hasDerivAt_cos t).hasDerivWithinAt)
    hd (convex_Icc 0 1) hy hx`. Existence: `obtain ⟨p, hp, hfix⟩ : ∃ p ∈ Set.Icc (0:ℝ) 1, Real.cos p - p = 0 :=
    intermediate_value_Icc' (by norm_num) (by fun_prop) ⟨_, _⟩` (endpoint goals: `cos 1 - 1 ≤ 0` and `0 ≤ cos 0 - 0`).
    Uniqueness: `refine ⟨p, ⟨hp, by linarith⟩, fun q ⟨hq, hqfix⟩ => ?_⟩`, `have hc := cos_contracts q p hq hp`,
    rewrite both fixed points in `hc`, then `nlinarith [abs_nonneg (q - p), sin_one_lt_one]` gives
    `|q - p| ≤ 0`; finish with `abs_nonpos_iff`.
-/
