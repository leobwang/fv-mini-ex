/- M101 | Two independent dice (product measure) | 15 min | Measure.pi, iIndepFun_pi, counting, ENNReal, decide, mathlib
GOAL
  Build an independent pair instead of assuming one: two rolls of a fair die are the coordinates of
  `ω : Fin 2 → Fin 6` under the product measure. Prove the two rolls are independent, and that the
  total number of pips is 7 with probability 1/6.

REFERENCE
  `Measure.pi μ`: product measure on `(i : ι) → α i` (coordinate `i` has law `μ i`); `μ.real s : ℝ`;
  `X ⟂ᵢ[μ] Y`: `X`, `Y` independent under `μ`; `(i : ℕ)` for `i : Fin 6` is its value 0..5 (`Fin.val`).
  #check @iIndepFun_pi          -- (∀ i, AEMeasurable (X i) (μ i)) → iIndepFun (fun i ω => X i (ω i)) (Measure.pi μ)
  #check @iIndepFun.indepFun    -- iIndepFun f μ → i ≠ j → f i ⟂ᵢ[μ] f j
  #check @Measure.pi_singleton  -- Measure.pi μ {f} = ∏ i, μ i {f i}
  #check @sum_measure_singleton -- ∑ x ∈ s, μ {x} = μ ↑s    (s : Finset α)
  example (x : Fin 6) : (PMF.uniformOfFintype (Fin 6)).toMeasure {x} = 6⁻¹ := by simp  -- one face
  #check @measureReal_def       -- μ.real s = (μ s).toReal
  #check @ENNReal.toReal_nsmul  -- (n • a).toReal = n • a.toReal
  example : (Finset.univ.filter fun ω : Fin 2 → Fin 6 => ω 0 = ω 1).card = 6 := by decide  -- count by brute force
  `f (μ := m) (X := g) h` fills implicit arguments by name.
-/
import Mathlib

namespace M101

open MeasureTheory ProbabilityTheory

-- BEGIN SPEC
/-- a fair die: face `i : Fin 6` shows `i + 1` pips -/
noncomputable abbrev die : Measure (Fin 6) := (PMF.uniformOfFintype (Fin 6)).toMeasure

/-- two independent rolls: the product measure on `Fin 2 → Fin 6` -/
noncomputable abbrev twoDice : Measure (Fin 2 → Fin 6) := Measure.pi fun _ => die
-- END SPEC

-- BEGIN SPEC
theorem rolls_indep : (fun ω : Fin 2 → Fin 6 => ω 0) ⟂ᵢ[twoDice] (fun ω => ω 1) :=
-- END SPEC
  -- coordinate `i` of the product is `X i (ω i)` with every `X i = id`
  (iIndepFun_pi (μ := fun _ : Fin 2 => die) (X := fun _ (x : Fin 6) => x)
    (fun _ => measurable_id.aemeasurable)).indepFun (by decide)

-- BEGIN SPEC
theorem prob_sum_seven :
    twoDice.real {ω | ((ω 0 : ℕ) + 1) + ((ω 1 : ℕ) + 1) = 7} = 1 / 6 :=
-- END SPEC
  by
    have hs : {ω : Fin 2 → Fin 6 | ((ω 0 : ℕ) + 1) + ((ω 1 : ℕ) + 1) = 7} =
        ↑(Finset.univ.filter fun ω : Fin 2 → Fin 6 => ((ω 0 : ℕ) + 1) + ((ω 1 : ℕ) + 1) = 7) := by
      ext ω; simp
    have hdie : ∀ x : Fin 6, die {x} = 6⁻¹ := by
      intro x; simp [die]
    have hcard : (Finset.univ.filter fun ω : Fin 2 → Fin 6 =>
        ((ω 0 : ℕ) + 1) + ((ω 1 : ℕ) + 1) = 7).card = 6 := by
      decide
    rw [measureReal_def, hs, ← sum_measure_singleton]
    simp only [twoDice, Measure.pi_singleton, hdie, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Finset.sum_const, hcard]
    rw [ENNReal.toReal_nsmul]
    simp [ENNReal.toReal_inv]
    norm_num

end M101

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Independence: the coordinates of a product of probability measures are mutually independent
    (`iIndepFun_pi` with every `X i = id`); pick out coordinates 0 and 1. Probability: the event is a
    finite set of outcomes, each of mass `6⁻¹ * 6⁻¹`, and there are 6 of them.
H2. Rewrite the event as `↑(Finset.univ.filter …)` (`ext ω; simp`), then
    `rw [measureReal_def, hs, ← sum_measure_singleton]`; show `die {x} = 6⁻¹` and count the filter by `decide`.
H3. Independence: `iIndepFun_pi (μ := fun _ : Fin 2 => die) (X := fun _ (x : Fin 6) => x) …`, then
    `.indepFun` with a proof of `(0 : Fin 2) ≠ 1`. Probability: after the rewrites, `simp only [twoDice,
    Measure.pi_singleton, hdie, Finset.prod_const, Finset.sum_const, hcard, …]`, then `ENNReal.toReal_nsmul`.
-/
