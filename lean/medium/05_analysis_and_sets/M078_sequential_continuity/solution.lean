/- M078 | ε-δ continuity ⇔ sequential continuity | 15-20 min | epsilon-delta, sequences, push Not, choose, mathlib
GOAL
  `f` is ε-δ continuous at `x` iff for every sequence `a n → x` we have `f (a n) → f x`
  (both notions are the explicit definitions below, not Mathlib's).

REFERENCE
  example (P : ℝ → Prop) (h : ¬ ∀ ε > 0, P ε) : ∃ ε > 0, ¬ P ε := by push Not at h; exact h  -- push `¬` inward
  example (h : ∀ n : ℕ, ∃ m : ℕ, n < m) : True := by choose f hf using h; trivial  -- f : ℕ → ℕ, hf : ∀ n, n < f n
  #check exists_nat_gt   -- (x : ℝ) : ∃ n : ℕ, x < ↑n      (Archimedes)
  #check div_lt_iff₀     -- 0 < c → (b / c < a ↔ b < a * c)   (also `div_le_iff₀` for ≤)
  example (n : ℕ) : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  example (N n : ℕ) (h : N ≤ n) : (N : ℝ) ≤ n := by exact_mod_cast h
  #check not_lt          -- ¬ a < b ↔ b ≤ a
BANNED: Continuous, ContinuousOn, ContinuousAt, ContinuousWithinAt, continuous, continuousOn, continuousAt, Tendsto, tendsto, nhds, 𝓝, Filter, atTop, Eventually, eventually, ∀ᶠ, Metric, CauchySeq, tendsto_nhds_nhds, tendsto_nhds, tendsto_atTop, tendsto_order, eventually_atTop, mem_atTop_sets, ball_mem_nhds, continuous_iff_continuousAt, continuous_def, cauchySeq_iff, cauchySeq_iff', cauchy_iff_exists_le_nhds, fun_prop, continuity, tendsto_nhds_iff_seq_tendsto, SeqContinuous, continuous_iff_seqContinuous
NOTE: The bans keep you in ε-δ land: no bridging to Mathlib's `Continuous` / `Tendsto`.
-/
import Mathlib

namespace M078

-- BEGIN SPEC
def ContAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y, |y - x| < δ → |f y - f x| < ε
-- END SPEC

-- BEGIN SPEC
def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
-- END SPEC

-- BEGIN SPEC
theorem contAt_iff_seq (f : ℝ → ℝ) (x : ℝ) :
    ContAt f x ↔ ∀ a : ℕ → ℝ, ConvergesTo a x → ConvergesTo (fun n => f (a n)) (f x) :=
-- END SPEC
  by
    constructor
    · intro hf a ha ε hε
      obtain ⟨δ, hδ, h⟩ := hf ε hε
      obtain ⟨N, hN⟩ := ha δ hδ
      exact ⟨N, fun n hn => h _ (hN n hn)⟩
    · intro h
      by_contra hf
      unfold ContAt at hf
      push Not at hf
      obtain ⟨ε, hε, hbad⟩ := hf
      -- WHY: δ = 1/(n+1) shrinks to 0, so the bad points a n are forced to converge to x.
      choose a ha1 ha2 using fun n : ℕ => hbad (1 / ((n : ℝ) + 1)) (by positivity)
      have hconv : ConvergesTo a x := by
        intro η hη
        obtain ⟨N, hN⟩ := exists_nat_gt (1 / η)
        refine ⟨N, fun n hn => lt_of_lt_of_le (ha1 n) ?_⟩
        have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
        rw [div_le_iff₀ (by positivity)]
        rw [div_lt_iff₀ hη] at hN
        nlinarith
      obtain ⟨N, hN⟩ := h a hconv ε hε
      exact absurd (hN N le_rfl) (not_lt.mpr (ha2 N))

end M078

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. (→) is a chase: ε gives δ (continuity), δ gives N (convergence). (←) goes by contradiction.
H2. (←): `by_contra hf; unfold ContAt at hf; push Not at hf` gives a bad `ε` such that every `δ > 0` has a `y` with `|y - x| < δ` but `ε ≤ |f y - f x|`. Use `δ = 1 / (n + 1)` to build a sequence.
H3. `choose a ha1 ha2 using fun n : ℕ => hbad (1 / ((n : ℝ) + 1)) (by positivity)`; prove `ConvergesTo a x` with `exists_nat_gt (1 / η)`, then feed it to the hypothesis at `ε` and compare `ha2 N` with `hN N le_rfl`.
-/
