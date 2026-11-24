/- M107 | Fixed-point iteration error | 15-20 min | Function.iterate, induction, a posteriori bound, Tendsto, squeeze, mathlib
GOAL
  Let `f` be `K`-Lipschitz (`|f x - f y| ≤ K |x - y|`, `0 ≤ K < 1`) with fixed point `p`, iterates `xₙ = fⁿ(x₀)`.
  Prove the a priori bound `|xₙ - p| ≤ Kⁿ |x₀ - p|`, the a posteriori (stopping-test) bound
  `|xₙ₊₁ - p| ≤ K/(1-K) |xₙ₊₁ - xₙ|`, which uses only computable quantities, and `xₙ → p`.
BANNED: ContractingWith, apriori_dist_iterate_fixedPoint_le, aposteriori_dist_iterate_fixedPoint_le, tendsto_iterate_fixedPoint

GUIDE
  Entries R1–R21: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M107

/- SKELETON · iterate_error      (write xₙ for f^[n] x₀)
  1. Induct on `n`:                                                        R1
  2. `zero`: f^[0] x₀ = x₀ and K ^ 0 * a = a; `simp` does both and closes:  R2, R3
  3. `succ n ih`: peel the LAST application of `f`, f^[n + 1] x₀ → f xₙ:    R4
  4. One calc chain                                                        R5
       |f xₙ - p| = |f xₙ - f p|        insert `f p` with rw [hp]           (W1)
                ≤ K * |xₙ - p|          the Lipschitz hypothesis            R6
                ≤ K * (K ^ n * |x₀ - p|)   from `ih` (and `hK : 0 ≤ K`)     R7
                = K ^ (n + 1) * |x₀ - p|   ring
-/
-- BEGIN SPEC
open Filter Topology

theorem iterate_error (f : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K) (hf : ∀ x y, |f x - f y| ≤ K * |x - y|)
    (p : ℝ) (hp : f p = p) (x₀ : ℝ) (n : ℕ) :
    |f^[n] x₀ - p| ≤ K ^ n * |x₀ - p| :=
-- END SPEC
  by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc |f (f^[n] x₀) - p| = |f (f^[n] x₀) - f p| := by rw [hp]
        _ ≤ K * |f^[n] x₀ - p| := hf _ _
        _ ≤ K * (K ^ n * |x₀ - p|) := by gcongr
        _ = K ^ (n + 1) * |x₀ - p| := by ring

/- SKELETON · aposteriori_error      (d = |f x - x| the step, e = |f x - p| the error)
  1. Name the current iterate  x := f^[n] x₀:                              R8
  2. Peel the last step, f^[n + 1] x₀ → f (f^[n] x₀):                       R4
       (the goal prints f (f^[n] x₀), not f x; it is the same term, see Traps)
  3. Fact  h1 : |f x - p| ≤ K * |x - p|   (the one-step estimate):          have, R5 with rw [hp] and R6
  4. Fact  h2 : |x - p| ≤ |f x - x| + |f x - p|   (triangle through f x):   have, R5 with R9, R10
  5. Clear the denominator: K / (1 - K) * d → K * d / (1 - K) → e * (1 - K) ≤ K * d:
                                                                           R11, R12 (side goal 0 < 1 - K: R13)
  6. Close it from h1, h2 and hK0; the proof needs the product K * h2:      R14
-/
-- BEGIN SPEC
theorem aposteriori_error (f : ℝ → ℝ) (K : ℝ) (hK0 : 0 ≤ K) (hK : K < 1)
    (hf : ∀ x y, |f x - f y| ≤ K * |x - y|) (p : ℝ) (hp : f p = p) (x₀ : ℝ) (n : ℕ) :
    |f^[n + 1] x₀ - p| ≤ K / (1 - K) * |f^[n + 1] x₀ - f^[n] x₀| :=
-- END SPEC
  by
    set x := f^[n] x₀
    rw [Function.iterate_succ_apply']
    have h1 : |f x - p| ≤ K * |x - p| := by
      calc |f x - p| = |f x - f p| := by rw [hp]
        _ ≤ K * |x - p| := hf x p
    have h2 : |x - p| ≤ |f x - x| + |f x - p| := by
      calc |x - p| ≤ |x - f x| + |f x - p| := abs_sub_le _ _ _
        _ = |f x - x| + |f x - p| := by rw [abs_sub_comm x]
    -- WHY: `(1 - K) e ≤ K d` needs `K ≥ 0` to multiply `h2` by `K`; nlinarith finds that product
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith

/- SKELETON · iterate_tendsto
  1. Fact  h0 : Tendsto (fun n => K ^ n * |x₀ - p|) atTop (𝓝 0):
       Kⁿ → 0, times the constant |x₀ - p|, then clean 0 * |x₀ - p|:       R15 → R16 → R17
  2. Goal  f^[n] x₀ → p   becomes   ‖f^[n] x₀ - p‖ → 0:                    R18
  3. Squeeze between 0 (R20) and h0's sequence; one bound left per n:      R19, R20
  4. ‖·‖ → |·|; the bound is now `iterate_error` (Part 1) at this n:        R21, then exact
-/
-- BEGIN SPEC
theorem iterate_tendsto (f : ℝ → ℝ) (K : ℝ) (hK0 : 0 ≤ K) (hK : K < 1)
    (hf : ∀ x y, |f x - f y| ≤ K * |x - y|) (p : ℝ) (hp : f p = p) (x₀ : ℝ) :
    Tendsto (fun n => f^[n] x₀) atTop (𝓝 p) :=
-- END SPEC
  by
    have h0 : Tendsto (fun n : ℕ => K ^ n * |x₀ - p|) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hK0 hK).mul_const |x₀ - p|
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0
    rw [Real.norm_eq_abs]
    exact iterate_error f K hK0 hf p hp x₀ n

end M107

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every bound starts from the one-step estimate `|f x - p| = |f x - f p| ≤ K |x - p|`: rewrite with `hp`
    to insert `f p`, then use `hf`. A priori: induction on `n`, peeling the last step of `f^[n + 1]`. For
    the limit, squeeze `|xₙ - p|` between `0` and `Kⁿ |x₀ - p|`, which tends to 0.
H2. A priori `succ` case: `rw [Function.iterate_succ_apply']`, then a `calc` through `|f xₙ - f p|`
    (`rw [hp]`), `K * |xₙ - p|` (`hf _ _`), `K * (K ^ n * |x₀ - p|)` (`gcongr`), `K ^ (n + 1) * |x₀ - p|`
    (`ring`). A posteriori: `set x := f^[n] x₀`, peel the last step, prove `h1 : e ≤ K |x - p|` and
    `h2 : |x - p| ≤ |f x - x| + e` (with `e = |f x - p|`); then `(1 - K) e ≤ K |f x - x|`, divide by `1 - K > 0`.
H3. A posteriori finish: `rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; nlinarith`.
    Limit: `have h0 : Tendsto (fun n : ℕ => K ^ n * |x₀ - p|) atTop (𝓝 0) :=
      by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hK0 hK).mul_const |x₀ - p|`, then
    `rw [tendsto_iff_norm_sub_tendsto_zero]; refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0`,
    and `rw [Real.norm_eq_abs]` leaves Part 1 at `n`.
-/
