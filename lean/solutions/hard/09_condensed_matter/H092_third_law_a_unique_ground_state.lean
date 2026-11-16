/- H092 | Third law: a unique ground state | 1-1.5 h | Tendsto, squeeze, negMulLog, continuity, physlib
GOAL
  Units kB = 1, inverse temperature `b = 1/T`. If the ground state `i₀` of a finite system `𝓒` is
  non-degenerate (every other level is strictly higher), the Gibbs entropy
  `S(b) = ∑ i, -p_b(i) log p_b(i)` tends to 0 as `b → ∞` (`T → 0⁺`).

REFERENCE
  #check CanonicalEnsemble.probabilityBetaReal  -- p_b(i) = exp (-b * 𝓒.energy i) / Z(b);  unfold with `rw [probabilityBetaReal]`
  #check CanonicalEnsemble.mathematicalPartitionFunctionBetaReal_pos  -- [Nonempty ι] : 0 < Z(b),  Z(b) = ∑ i, exp (-b * E i)
  #check Real.negMulLog_def          -- negMulLog = fun x => -x * log x   (`Real.negMulLog_zero`, `Real.negMulLog_one`: both 0)
  #check Real.continuous_negMulLog   -- so `(Real.continuous_negMulLog.tendsto _).comp h : Tendsto (negMulLog ∘ f) l (𝓝 (negMulLog a))`
  #check tendsto_finsetSum           -- termwise limits ⇒ limit of `∑ c ∈ s, f c b`
  #check tendsto_of_tendsto_of_tendsto_of_le_of_le  -- squeeze: g → a, h → a, g ≤ f ≤ h ⇒ f → a
  #check Real.tendsto_exp_atBot      -- exp x → 0 as x → -∞
  #check Filter.Tendsto.atBot_mul_const  -- 0 < r → f → -∞ ⇒ (f · * r) → -∞;  with `tendsto_neg_atTop_atBot`
  #check Finset.single_le_sum        -- (∀ i ∈ s, 0 ≤ f i) → a ∈ s → f a ≤ ∑ x ∈ s, f x
  #check Finset.add_sum_erase        -- f a + ∑ x ∈ s.erase a, f x = ∑ x ∈ s, f x   (needs `classical`)
  `Tendsto f atTop (𝓝 L)` reads "f b → L as b → ∞";  `haveI : Nonempty ι := ⟨i₀⟩` supplies the instance.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open CanonicalEnsemble Real Filter Topology

namespace H092

section Milestones

variable {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι)

-- MILESTONE (optional: change or delete)
theorem prob_le (b : ℝ) (i₀ j : ι) :
    𝓒.probabilityBetaReal b j ≤ Real.exp (-b * (𝓒.energy j - 𝓒.energy i₀)) := by
  haveI : Nonempty ι := ⟨i₀⟩
  have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos b
  have hle : Real.exp (-b * 𝓒.energy i₀) ≤ 𝓒.mathematicalPartitionFunctionBetaReal b :=
    Finset.single_le_sum (f := fun i => Real.exp (-b * 𝓒.energy i))
      (fun i _ => (exp_pos _).le) (Finset.mem_univ i₀)
  rw [probabilityBetaReal, div_le_iff₀ hZ]
  calc Real.exp (-b * 𝓒.energy j)
      = Real.exp (-b * (𝓒.energy j - 𝓒.energy i₀)) * Real.exp (-b * 𝓒.energy i₀) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_left hle (exp_pos _).le

-- MILESTONE (optional: change or delete)
theorem prob_tendsto_zero (i₀ j : ι) (h : 𝓒.energy i₀ < 𝓒.energy j) :
    Tendsto (fun b => 𝓒.probabilityBetaReal b j) atTop (𝓝 0) := by
  haveI : Nonempty ι := ⟨i₀⟩
  have hd : 0 < 𝓒.energy j - 𝓒.energy i₀ := by linarith
  have hlin : Tendsto (fun b : ℝ => -b * (𝓒.energy j - 𝓒.energy i₀)) atTop atBot :=
    tendsto_neg_atTop_atBot.atBot_mul_const hd
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (Real.tendsto_exp_atBot.comp hlin)
    (fun b => (div_pos (exp_pos _) (𝓒.mathematicalPartitionFunctionBetaReal_pos b)).le)
    (fun b => prob_le 𝓒 b i₀ j)

-- MILESTONE (optional: change or delete)
theorem prob_ground_tendsto_one (i₀ : ι) (hgap : ∀ j, j ≠ i₀ → 𝓒.energy i₀ < 𝓒.energy j) :
    Tendsto (fun b => 𝓒.probabilityBetaReal b i₀) atTop (𝓝 1) := by
  classical
  haveI : Nonempty ι := ⟨i₀⟩
  have hsum : ∀ b, 𝓒.probabilityBetaReal b i₀ =
      1 - ∑ j ∈ Finset.univ.erase i₀, 𝓒.probabilityBetaReal b j := by
    intro b
    have h1 : ∑ i, 𝓒.probabilityBetaReal b i = 1 := by
      simp only [probabilityBetaReal, ← Finset.sum_div]
      exact div_self (𝓒.mathematicalPartitionFunctionBetaReal_pos b).ne'
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at h1
    linarith
  simp_rw [hsum]
  have hlim := tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ)) |>.sub
    (tendsto_finsetSum (Finset.univ.erase i₀) fun j hj =>
      prob_tendsto_zero 𝓒 i₀ j (hgap j (Finset.ne_of_mem_erase hj)))
  simpa using hlim

end Milestones

-- BEGIN SPEC
theorem third_law {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (i₀ : ι)
    (hgap : ∀ j, j ≠ i₀ → 𝓒.energy i₀ < 𝓒.energy j) :
    Tendsto (fun b => ∑ i, Real.negMulLog (𝓒.probabilityBetaReal b i)) atTop (𝓝 0) :=
-- END SPEC
  by
    classical
    have hlim : ∀ i, Tendsto (fun b => 𝓒.probabilityBetaReal b i) atTop
        (𝓝 (if i = i₀ then 1 else 0)) := by
      intro i
      by_cases hi : i = i₀
      · subst hi
        simpa using prob_ground_tendsto_one 𝓒 i hgap
      · simpa [hi] using prob_tendsto_zero 𝓒 i₀ i (hgap i hi)
    have := tendsto_finsetSum Finset.univ fun i _ =>
      (Real.continuous_negMulLog.tendsto _).comp (hlim i)
    simpa [apply_ite Real.negMulLog] using this

end H092

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every excited state's probability dies off like `exp (-b (E_j - E_{i₀}))`, so `p_b(j) → 0` for
    `j ≠ i₀` and `p_b(i₀) = 1 - ∑_{j ≠ i₀} p_b(j) → 1`. Then `negMulLog` is continuous with value 0 at
    both 0 and 1.
H2. `prob_le`: `Z(b) ≥ exp (-b E_{i₀})` (one term of a sum of positives), so
    `p_b(j) ≤ exp (-b E_j) / exp (-b E_{i₀})`; use `div_le_iff₀` and `Real.exp_add`.
    `prob_tendsto_zero`: squeeze between `0` and that bound. Main: show
    `∀ i, Tendsto (fun b => p_b(i)) atTop (𝓝 (if i = i₀ then 1 else 0))` (start with `classical` so the
    `if` is decidable), then push it through `negMulLog` and the finite sum.
H3. Main finish: `have := tendsto_finsetSum Finset.univ fun i _ => (Real.continuous_negMulLog.tendsto _).comp (hlim i)`
    then `simpa [apply_ite Real.negMulLog] using this`. For `prob_ground_tendsto_one`, prove
    `∑ i, p_b(i) = 1` (`simp only [probabilityBetaReal, ← Finset.sum_div]`, then `div_self` with `Z(b) ≠ 0`), split off `i₀`
    with `Finset.add_sum_erase`, and use `tendsto_const_nhds.sub (tendsto_finsetSum _ …)`.
-/
