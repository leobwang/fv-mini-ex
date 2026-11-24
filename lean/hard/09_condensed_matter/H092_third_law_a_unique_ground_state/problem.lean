/- H092 | Third law: a unique ground state | 1-1.5 h | Tendsto, squeeze, negMulLog, continuity, physlib
GOAL
  Units kB = 1, inverse temperature `b = 1/T`. If the ground state `i₀` of a finite system `𝓒` is
  non-degenerate (every other level is strictly higher), the Gibbs entropy
  `S(b) = ∑ i, -p_b(i) log p_b(i)` tends to 0 as `b → ∞` (`T → 0⁺`).

GUIDE
  Entries R1–R37: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open CanonicalEnsemble Real Filter Topology

namespace H092

section Milestones

variable {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι)

/- SKELETON · prob_le   (milestone 1: p_b(j) ≤ exp (-b (E j - E i₀)); used in prob_tendsto_zero)
  1. The instance `Nonempty ι` from `i₀`, then hZ : 0 < Z b:                 R1, R2
  2. hle : rexp (-b * 𝓒.energy i₀) ≤ 𝓒.mathematicalPartitionFunctionBetaReal b
       the `i₀` term of the sum `Z b` (by definition `∑ i, rexp (-b * E i)`):
       R6 with `(f := fun i => rexp (-b * 𝓒.energy i))`, terms ≥ 0 by R3 → R4, membership R5
  3. Unfold `p b j` and clear the denominator `Z b` (one `rw [...]`):        R7, R8 with hZ
  4. A two-step chain  _ = rexp (-b * (E j - E i₀)) * rexp (-b * E i₀)  _ ≤ _:   R9
  5. Step `=`: merge the two exponentials, then compare the exponents:      R10 (right to left), R11
  6. Step `≤`: multiply hle on the left by `rexp (…) ≥ 0`:                   R12 with R3 → R4
-/
-- MILESTONE (optional: change or delete)
theorem prob_le (b : ℝ) (i₀ j : ι) :
    𝓒.probabilityBetaReal b j ≤ Real.exp (-b * (𝓒.energy j - 𝓒.energy i₀)) := by
  sorry

/- SKELETON · prob_tendsto_zero   (milestone 2: p_b(j) → 0 for an excited j; uses milestone 1;
                                   used in prob_ground_tendsto_one and third_law)
  1. The instance `Nonempty ι`:                                              R1
  2. hd : 0 < 𝓒.energy j - 𝓒.energy i₀:                                      R13
  3. hlin : Tendsto (fun b : ℝ => -b * (𝓒.energy j - 𝓒.energy i₀)) atTop atBot:   R14 → R15
  4. Squeeze p_b(j) between 0 and rexp (-b * (E j - E i₀)), one term:        R20, with
       lower limit: the constant 0                                           R18
       upper limit: exp of something going to -∞                             R16 → R17 on hlin
       0 ≤ p_b(j) for each b (`fun b => …`):                                 R21, R19 with R3, R2, then R4
       p_b(j) ≤ bound for each b:                                            R21, milestone 1
-/
-- MILESTONE (optional: change or delete)
theorem prob_tendsto_zero (i₀ j : ι) (h : 𝓒.energy i₀ < 𝓒.energy j) :
    Tendsto (fun b => 𝓒.probabilityBetaReal b j) atTop (𝓝 0) := by
  sorry

/- SKELETON · prob_ground_tendsto_one   (milestone 3: p_b(i₀) → 1; uses milestone 2; used in third_law)
  1. `classical` (for `Finset.univ.erase i₀`), and the instance `Nonempty ι`:   R22, R1
  2. hsum : ∀ b, p_b(i₀) = 1 - ∑ j ∈ Finset.univ.erase i₀, p_b(j):
       intro b, then h1 : ∑ i, p_b(i) = 1:
         one `simp only`: unfold p under ∑ and pull out `/ Z b`              R7 (simp only form), R23 (right to left)
         the numerator is `Z b` by definition, so it is `a / a = 1`           R25 with R2 → R24
       split the `i₀` term off h1, then solve for p_b(i₀):                    R26 (with R5), R13
  3. Rewrite `p_b(i₀)` inside `fun b => …` in the goal with hsum:            R27
  4. hlim : the limit of `1 - ∑ …` is `1 - ∑ j ∈ …, 0`:
       R18 (name `x := 1`, `f := atTop`), R28 with R29, whose term for `j` is
       milestone 2 at `hgap j (…)`, the `…` from `hj : j ∈ univ.erase i₀`    R30
  5. Clean `1 - ∑ 0` to `1` and close with hlim:                             R31
-/
-- MILESTONE (optional: change or delete)
theorem prob_ground_tendsto_one (i₀ : ι) (hgap : ∀ j, j ≠ i₀ → 𝓒.energy i₀ < 𝓒.energy j) :
    Tendsto (fun b => 𝓒.probabilityBetaReal b i₀) atTop (𝓝 1) := by
  sorry

end Milestones

/- SKELETON · third_law
  Prove the milestones first, in order 1 → 2 → 3; this proof uses milestones 2 and 3.
  1. `classical`, so that `if i = i₀ then 1 else 0` typechecks:               R22
  2. hlim : ∀ i, Tendsto (fun b => 𝓒.probabilityBetaReal b i) atTop (𝓝 (if i = i₀ then 1 else 0)):
       intro i, split on `i = i₀`:                                            R32
       case `hi : i = i₀`: substitute, then milestone 3 (`if i = i …` is 1):  R33, R31 with R34
       case `hi : ¬i = i₀`: milestone 2 at `hgap i hi` (`if` is 0):           R31 with R34 (`simpa [hi] using …`)
  3. Push hlim through `negMulLog` and the finite sum, as one `have`:
       R29 over `Finset.univ`, each term                                      R35 → R17 on `hlim i`
  4. The limit is `∑ i, negMulLog (if i = i₀ then 1 else 0)`; simp it to 0:   R31 with R36, R37
-/
-- BEGIN SPEC
theorem third_law {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (i₀ : ι)
    (hgap : ∀ j, j ≠ i₀ → 𝓒.energy i₀ < 𝓒.energy j) :
    Tendsto (fun b => ∑ i, Real.negMulLog (𝓒.probabilityBetaReal b i)) atTop (𝓝 0) :=
-- END SPEC
  sorry

end H092

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every excited level's weight is at most `exp (-b (E j - E i₀))` because `Z b ≥ exp (-b E i₀)`, so
    `p_b(j) → 0` for `j ≠ i₀`, and `p_b(i₀) = 1 - ∑_{j ≠ i₀} p_b(j) → 1`. `negMulLog` is continuous and is
    0 at both 0 and 1. The three milestones are exactly these steps; prove them in order first.
H2. Milestone 1: R1, R2; `hle` from `Finset.single_le_sum` (R6); `rw [probabilityBetaReal, div_le_iff₀ hZ]`
    (R7, R8); a `calc` (R9) with `← Real.exp_add` and `ring_nf` (R10, R11), then `mul_le_mul_of_nonneg_left`
    (R12). Milestone 2: the squeeze `tendsto_of_tendsto_of_tendsto_of_le_of_le` (R20) between
    `tendsto_const_nhds` and `Real.tendsto_exp_atBot.comp hlin` (R16–R18). Milestone 3: `∑ i, p_b(i) = 1`
    (R23–R25), `Finset.add_sum_erase` (R26), `simp_rw` (R27), `Tendsto.sub` and `tendsto_finsetSum` (R28, R29).
    Main: `classical`, `hlim i` by `by_cases` (R32–R34), then R35, R17, R29 and `simpa` (R31, R36, R37).
H3. Milestone 1: `Finset.single_le_sum (f := fun i => Real.exp (-b * 𝓒.energy i)) (fun i _ => (exp_pos _).le)
    (Finset.mem_univ i₀)`. Milestone 2: `hlin := tendsto_neg_atTop_atBot.atBot_mul_const hd`.
    Main finish: `have := tendsto_finsetSum Finset.univ fun i _ =>
    (Real.continuous_negMulLog.tendsto _).comp (hlim i)`, then `simpa [apply_ite Real.negMulLog] using this`.
-/
