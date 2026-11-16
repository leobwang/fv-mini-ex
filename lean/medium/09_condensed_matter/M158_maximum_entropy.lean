/- M158 | Maximum entropy | 15-20 min | negMulLog, concavity, Jensen, Gibbs entropy, mathlib
GOAL
  The Gibbs entropy `S(p) = ∑ i, negMulLog (p i)` (with `negMulLog x = -x log x`, units kB = 1) of any
  probability distribution `p` on `Ω = Fintype.card ι` microstates is at most `log Ω`, and the uniform
  distribution `p i = 1/Ω` attains it: Boltzmann's `S = log Ω` is the maximum entropy.

REFERENCE
  #check Real.negMulLog            -- negMulLog x = -x * log x
  #check Real.concaveOn_negMulLog  -- ConcaveOn ℝ (Set.Ici 0) negMulLog
  #check ConcaveOn.le_map_sum      -- Jensen: w i ≥ 0, ∑ w i = 1, p i ∈ s ⊢ ∑ w i • f (p i) ≤ f (∑ w i • p i)
  #check Finset.mul_sum            -- a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i
  #check Fintype.card_pos          -- [Nonempty α] : 0 < Fintype.card α
  #check Real.log_inv              -- log x⁻¹ = -log x
  example (n : ℝ) (h : 0 < n) : n * (1 / n) = 1 := mul_one_div_cancel h.ne'
  example (a b : ℝ) : a • b = a * b := smul_eq_mul a b
  #check Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ) (w := fun _ : Fin 3 => (1 : ℝ) / 3)
    -- naming implicit arguments `(t := …)`; here Ω = 3, in the proof use `n = (Fintype.card ι : ℝ)`
  `Real.log (Fintype.card ι)` casts the natural number `Fintype.card ι` to ℝ.
BANNED: Hₛ_le_log_d, Hₛ_uniform, Sᵥₙ_le_log_d, try?
NOTE: the banned names are physlib's Shannon/von Neumann max-entropy lemmas (reachable by adding an import);
  `try?` is banned because it can run for many minutes here. The point is the Jensen argument.
-/
import Mathlib

open Real

namespace M158

-- BEGIN SPEC
theorem max_entropy {ι : Type} [Fintype ι] [Nonempty ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) :
    ∑ i, Real.negMulLog (p i) ≤ Real.log (Fintype.card ι) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem uniform_attains {ι : Type} [Fintype ι] [Nonempty ι] :
    ∑ _i : ι, Real.negMulLog (1 / Fintype.card ι) = Real.log (Fintype.card ι) :=
-- END SPEC
  sorry

end M158

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `negMulLog` is concave on `[0, ∞)`. Jensen with equal weights `1/Ω` compares the average of
    `negMulLog (p i)` with `negMulLog` of the average of the `p i`, which is `1/Ω`.
H2. Set `n := (Fintype.card ι : ℝ)` with `0 < n`. Apply `Real.concaveOn_negMulLog.le_map_sum` with
    weights `fun _ => 1 / n`; after `smul_eq_mul`, `← Finset.mul_sum` and `hs`, the right side is
    `negMulLog (1/n * 1) = log n / n`. Multiply the inequality by `n`.
H3. Side goals of Jensen: weights by `positivity`, `∑ _i, 1 / n = 1` by `simp [Finset.card_univ, ← hn]`
    (with `set n := … with hn`),
    membership by `hp i`. `uniform_attains`: `simp [Real.negMulLog, Real.log_inv, Finset.card_univ]`
    once `0 < (Fintype.card ι : ℝ)` is in context.
-/
