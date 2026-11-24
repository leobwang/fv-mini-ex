/- H091 | log Z is convex in β | 1-1.5 h | ConvexOn, Hölder inequality, rpow, physlib
GOAL
  For a finite system `𝓒` (units kB = 1), `b ↦ log Z(b)` is convex on all of ℝ. The intended route avoids
  derivatives: Hölder's inequality gives `Z(a x + c y) ≤ Z(x)^a * Z(y)^c` for weights `a, c > 0`, `a + c = 1`; take logs.

GUIDE
  Entries R1–R24: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite
import Mathlib.Analysis.MeanInequalities

open CanonicalEnsemble Real

namespace H091

/- SKELETON · the milestones (prove these FIRST, in order: `holder_step` uses the other two,
   and `logZ_convex` uses `holder_step` for its first `calc` step)
  exp_rpow   `(e^{-a x e})^{1/a} = e^{-x e}`:
    1. power into the exponent                                    R1
    2. compare exponents                                          R2
    3. clear the `1 / a` (uses `ha`)                              R3
  holderConjugate_weights   `1/a`, `1/c` are Hölder conjugates:
    1. unfold the definition, split the `∧`                       R4, refine ⟨?_, ?_⟩
       (two goals: `1 < 1 / a` first, then `(1/a)⁻¹ + (1/c)⁻¹ = 1`)
    2. `1 < 1 / a`: multiply out, then linear arithmetic          R6 → R7
    3. `(1/a)⁻¹ + (1/c)⁻¹ = 1`: `simp` with `hac`                  R5
       (or close this one inline: `refine ⟨?_, by …⟩` in step 1)
  holder_step   `Z(a x + c y) ≤ Z(x)^a * Z(y)^c`:
    1. key := Hölder on `Finset.univ` with p = 1/a, q = 1/c,
         f i = exp (-(a x) E i), g i = exp (-(c y) E i)            R8 (holderConjugate_weights, R9 twice)
    2. simplify `key` in one `simp only [...] at key`:
         `exp_rpow` for a and for c, then R10, R11
    3. unfold Z in the goal                                       R12
    4. goal and `key` differ only in each summand's exponent:     R13 with `key`, R14 inside it
    5. one summand: strip `rexp`, then `ring`                      R2, ring
-/
section Milestones

variable {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι)

-- MILESTONE (optional: change or delete)
theorem exp_rpow (x e a : ℝ) (ha : 0 < a) : Real.exp (-(a * x) * e) ^ (1 / a) = Real.exp (-x * e) := by
  rw [← Real.exp_mul]
  congr 1
  field_simp

-- MILESTONE (optional: change or delete)
theorem holderConjugate_weights (a c : ℝ) (ha : 0 < a) (hc : 0 < c) (hac : a + c = 1) :
    (1 / a).HolderConjugate (1 / c) := by
  rw [Real.holderConjugate_iff]
  refine ⟨?_, by simp [hac]⟩
  rw [lt_div_iff₀ ha]
  linarith

-- MILESTONE (optional: change or delete)
theorem holder_step (x y a c : ℝ) (ha : 0 < a) (hc : 0 < c) (hac : a + c = 1) :
    𝓒.mathematicalPartitionFunctionBetaReal (a * x + c * y) ≤
      𝓒.mathematicalPartitionFunctionBetaReal x ^ a * 𝓒.mathematicalPartitionFunctionBetaReal y ^ c := by
  have key := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ)
    (f := fun i => Real.exp (-(a * x) * 𝓒.energy i)) (g := fun i => Real.exp (-(c * y) * 𝓒.energy i))
    (holderConjugate_weights a c ha hc hac) (fun i _ => (exp_pos _).le) (fun i _ => (exp_pos _).le)
  simp only [exp_rpow _ _ _ ha, exp_rpow _ _ _ hc, one_div_one_div, ← Real.exp_add] at key
  simp only [mathematicalPartitionFunctionBetaReal]
  refine Eq.trans_le (Finset.sum_congr rfl fun i _ => ?_) key
  congr 1; ring

end Milestones

/- SKELETON · logZ_convex   (needs the milestone `holder_step`)
  1. convexity → the two-point inequality, `•` → `*`:            R15, R16
     goal: log Z(a x + c y) ≤ a * log Z(x) + c * log Z(y), with ha : 0 ≤ a, hc : 0 ≤ c, hac
  2. edge weights first (holder_step needs 0 < a, 0 < c):
       split `ha`; in the `a = 0` branch force `c = 1`, then `simp`   R17, R18, simp (W1)
       the same for `hc`                                            R17, R18, simp
  3. positivity of Z:                                             R19
  4. a `calc` with two steps:                                     R20
       ≤ log (Z(x) ^ a * Z(y) ^ c)        R21 with hZ and holder_step
                                          (holder_step takes 𝓒 first, then x y a c and ha' hc' hac)
       = a * log Z(x) + c * log Z(y)      R22 (twice) → R23, then R24 twice   (W3)
-/
-- BEGIN SPEC
theorem logZ_convex {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) :
    ConvexOn ℝ Set.univ (fun b => Real.log (𝓒.mathematicalPartitionFunctionBetaReal b)) :=
-- END SPEC
  by
    refine ⟨convex_univ, fun x _ y _ a c ha hc hac => ?_⟩
    simp only [smul_eq_mul]
    rcases ha.eq_or_lt with rfl | ha'
    · obtain rfl : c = 1 := by linarith
      simp
    rcases hc.eq_or_lt with rfl | hc'
    · obtain rfl : a = 1 := by linarith
      simp
    have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos
    calc Real.log (𝓒.mathematicalPartitionFunctionBetaReal (a * x + c * y))
        ≤ Real.log (𝓒.mathematicalPartitionFunctionBetaReal x ^ a *
            𝓒.mathematicalPartitionFunctionBetaReal y ^ c) :=
          Real.log_le_log (hZ _) (holder_step 𝓒 x y a c ha' hc' hac)
      _ = a * Real.log (𝓒.mathematicalPartitionFunctionBetaReal x) +
            c * Real.log (𝓒.mathematicalPartitionFunctionBetaReal y) := by
          rw [Real.log_mul (rpow_pos_of_pos (hZ x) a).ne' (rpow_pos_of_pos (hZ y) c).ne',
            Real.log_rpow (hZ x), Real.log_rpow (hZ y)]

end H091

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold `ConvexOn` (R15, R16) and dispose of the weights `a = 0` or `c = 0` first (R17, R18, `simp`):
    Hölder needs `0 < a` and `0 < c`. For positive weights the whole proof is the milestone
    `holder_step`, `Z(a x + c y) ≤ Z(x)^a * Z(y)^c`, followed by taking logs.
H2. Hölder (R8) with exponents `p = 1/a`, `q = 1/c` (conjugate because `a + c = 1`) on
    `f i = exp (-(a x) E i)`, `g i = exp (-(c y) E i)`: then `f i * g i = exp (-(a x + c y) E i)` (R11),
    `f i ^ (1/a) = exp (-x E i)` (`exp_rpow`), and the outer powers `1 / (1 / a) = a` (R10). Then `log` is
    monotone (R21) and `log (Z(x)^a * Z(y)^c) = a log Z(x) + c log Z(y)` (R23, R24).
H3. `have key := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ) (f := fun i => Real.exp (-(a * x) * 𝓒.energy i))
    (g := fun i => Real.exp (-(c * y) * 𝓒.energy i)) (holderConjugate_weights a c ha hc hac) (by …) (by …)`;
    for `exp_rpow`: `rw [← Real.exp_mul]; congr 1; field_simp`. Last step: `Real.log_le_log (hZ _) (holder_step …)`,
    then `rw [Real.log_mul …, Real.log_rpow (hZ x), Real.log_rpow (hZ y)]` on the right.
-/
