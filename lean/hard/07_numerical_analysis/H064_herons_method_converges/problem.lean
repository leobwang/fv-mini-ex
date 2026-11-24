/- H064 | Heron's method converges | 1-1.25 h | monotone convergence, ciInf, limit identification, Filter.Tendsto, Real.sqrt, mathlib
GOAL
  Heron's iteration `xₙ₊₁ = (xₙ + a / xₙ) / 2` (`a > 0`, `x₀ > 0`) converges to `√a`: from step 1 on it
  decreases and stays `≥ √a`, so it has a limit `L > 0`, and the recursion in the limit forces `L = √a`.
  Milestones 1-3 are M109's specs (`babylon_error`, `sqrt_le_babylon`, `babylon_le`): paste your proofs.

REFERENCE
  -- `⨅ n, g n` = infimum of a sequence;  `Tendsto u atTop (𝓝 L)` means `u n → L` (`open Filter Topology`)
  #check tendsto_atTop_ciInf      -- Antitone f → BddBelow (Set.range f) → Tendsto f atTop (𝓝 (⨅ i, f i))
  #check le_ciInf                 -- (∀ x, c ≤ f x) → c ≤ ⨅ i, f i
  #check antitone_nat_of_succ_le  -- (∀ n, f (n + 1) ≤ f n) → Antitone f
  #check tendsto_nhds_unique      -- Tendsto f l (𝓝 a) → Tendsto f l (𝓝 b) → a = b
  #check tendsto_add_atTop_iff_nat -- (k : ℕ) : Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f atTop l
  #check ContinuousAt.tendsto     -- ContinuousAt f x → Tendsto f (𝓝 x) (𝓝 (f x));  compose with `.comp h`
  example (a L : ℝ) (hL : L ≠ 0) : ContinuousAt (babylon a) L := by
    unfold babylon; fun_prop (disch := exact hL)  -- unfold first; `disch` proves the side goal `L ≠ 0`
  #check Real.sqrt_sq             -- 0 ≤ a → √(a ^ 2) = a      (and `Real.sq_sqrt : 0 ≤ a → √a ^ 2 = a`)
  #check Real.sqrt_pos            -- 0 < √x ↔ 0 < x
-/
import Mathlib

open Filter Topology

namespace H064

-- BEGIN SPEC
-- the Babylonian (Newton) step for √a
noncomputable def babylon (a x : ℝ) : ℝ := (x + a / x) / 2

/-- Heron's iteration from `x₀`: `heron a x₀ n = xₙ` -/
noncomputable def heron (a x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => babylon a (heron a x₀ n)
-- END SPEC

-- MILESTONE (optional: change or delete)  (proved in M109: paste your proof)
-- error identity: the step's overshoot above `√a` is a square over `2x`
theorem babylon_error (a x : ℝ) (ha : 0 ≤ a) (hx : 0 < x) :
    babylon a x - √a = (x - √a) ^ 2 / (2 * x) := by
  sorry

-- MILESTONE (optional: change or delete)  (proved in M109: paste your proof)
theorem sqrt_le_babylon (a x : ℝ) (ha : 0 ≤ a) (hx : 0 < x) : √a ≤ babylon a x := by
  sorry

-- MILESTONE (optional: change or delete)  (proved in M109: paste your proof)
theorem babylon_le (a x : ℝ) (ha : 0 ≤ a) (hx : 0 < x) (hsx : √a ≤ x) : babylon a x ≤ x := by
  sorry

-- MILESTONE (optional: change or delete)
theorem heron_ge (a x₀ : ℝ) (ha : 0 < a) (hx : 0 < x₀) (n : ℕ) : √a ≤ heron a x₀ (n + 1) := by
  sorry

-- MILESTONE (optional: change or delete)
-- the only positive fixed point of the step is `√a`
theorem fixed_point_eq_sqrt (a L : ℝ) (hL : 0 < L) (h : babylon a L = L) : L = √a := by
  sorry

-- BEGIN SPEC
theorem heron_tendsto (a x₀ : ℝ) (ha : 0 < a) (hx : 0 < x₀) :
    Tendsto (heron a x₀) atTop (𝓝 √a) :=
-- END SPEC
  sorry

end H064

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Work with the shifted sequence `g n := heron a x₀ (n + 1)`: it is `≥ √a` and decreasing (milestones),
    so it converges to `L := ⨅ n, g n`. At the end, shift back with `tendsto_add_atTop_iff_nat 1`.
H2. Identify the limit: `g (n + 1) = babylon a (g n)`. The left side tends to `L` (a tail of `g`); the
    right side tends to `babylon a L` because `babylon a` is continuous at `L ≠ 0`. Uniqueness of limits
    gives `babylon a L = L`. For `fixed_point_eq_sqrt`: clear denominators to get `L ^ 2 = a`.
H3. `have tg := tendsto_atTop_ciInf anti bdd`; `have hL : √a ≤ L := le_ciInf (heron_ge a x₀ ha hx)`;
    `have hc : ContinuousAt (babylon a) L := by unfold babylon; fun_prop (disch := exact hL0.ne')`;
    `have tb := hc.tendsto.comp tg`;
    `have hfix := tendsto_nhds_unique tb (tg.comp (tendsto_add_atTop_nat 1))`.
    Last step: `rw [← tendsto_add_atTop_iff_nat 1, ← fixed_point_eq_sqrt a L hL0 hfix]; exact tg`.
-/
