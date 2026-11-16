/- M075 | Monotone convergence | 15 min | sSup, epsilon-N, exists_lt_of_lt_csSup, mathlib
GOAL
  A monotone sequence that is bounded above converges (explicit ε-N definition) to the supremum of
  its values, `sSup (Set.range a)`.

REFERENCE
  #check exists_lt_of_lt_csSup  -- s.Nonempty → b < sSup s → ∃ a ∈ s, b < a
  #check le_csSup               -- BddAbove s → a ∈ s → a ≤ sSup s
  #check Set.range_nonempty     -- (f : ι → α) : (Set.range f).Nonempty   (ι = ℕ is nonempty)
  #check sub_lt_self            -- (a : α) : 0 < b → a - b < a
  #check abs_sub_lt_iff         -- |a - b| < c ↔ a - b < c ∧ b - a < c
  example (a : ℕ → ℝ) (hm : Monotone a) (m n : ℕ) (h : m ≤ n) : a m ≤ a n := hm h
  -- `obtain ⟨_, ⟨N, rfl⟩, hN⟩ := h` turns `h : ∃ x ∈ Set.range a, b < x` into `hN : b < a N`
NOTE: `BddAbove S` means `∃ M, ∀ x ∈ S, x ≤ M`; `Monotone a` means `m ≤ n → a m ≤ a n`.
BANNED: Continuous, ContinuousOn, ContinuousAt, ContinuousWithinAt, continuous, continuousOn, continuousAt, Tendsto, tendsto
BANNED: nhds, 𝓝, Filter, atTop, Eventually, eventually, ∀ᶠ, Metric, CauchySeq, tendsto_nhds_nhds, tendsto_nhds, tendsto_atTop
BANNED: tendsto_order, eventually_atTop, mem_atTop_sets, ball_mem_nhds, continuous_iff_continuousAt, continuous_def
BANNED: cauchySeq_iff, cauchySeq_iff', cauchy_iff_exists_le_nhds, fun_prop, continuity, tendsto_atTop_ciSup, tendsto_atTop_isLUB
-/
import Mathlib

namespace M075

-- BEGIN SPEC
def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
-- END SPEC

-- BEGIN SPEC
theorem monotone_converges (a : ℕ → ℝ) (hm : Monotone a) (hb : BddAbove (Set.range a)) :
    ConvergesTo a (sSup (Set.range a)) :=
-- END SPEC
  sorry

end M075

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `sSup - ε` is not an upper bound, so some term `a N` exceeds it; monotonicity keeps every later term above it.
H2. Use `exists_lt_of_lt_csSup` with `b = sSup (Set.range a) - ε` to get `N`. For `n ≥ N`, collect
    `sSup - ε < a N ≤ a n ≤ sSup`.
H3. `obtain ⟨_, ⟨N, rfl⟩, hN⟩ := exists_lt_of_lt_csSup (Set.range_nonempty a) (sub_lt_self _ hε)`;
    then `le_csSup hb ⟨n, rfl⟩`, `hm hn`, and `rw [abs_sub_lt_iff]; constructor <;> linarith`.
-/
