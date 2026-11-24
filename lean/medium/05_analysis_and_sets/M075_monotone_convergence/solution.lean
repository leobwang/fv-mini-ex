/- M075 | Monotone convergence | 15 min | sSup, epsilon-N, exists_lt_of_lt_csSup, mathlib
GOAL
  A monotone sequence that is bounded above converges (explicit ε-N definition) to the supremum of
  its values, `sSup (Set.range a)`.

BANNED: Continuous, ContinuousOn, ContinuousAt, ContinuousWithinAt, continuous, continuousOn, continuousAt, Tendsto, tendsto
BANNED: nhds, 𝓝, Filter, atTop, Eventually, eventually, ∀ᶠ, Metric, CauchySeq, tendsto_nhds_nhds, tendsto_nhds, tendsto_atTop
BANNED: tendsto_order, eventually_atTop, mem_atTop_sets, ball_mem_nhds, continuous_iff_continuousAt, continuous_def
BANNED: cauchySeq_iff, cauchySeq_iff', cauchy_iff_exists_le_nhds, fun_prop, continuity, tendsto_atTop_ciSup, tendsto_atTop_isLUB

GUIDE
  Entries R1–R11: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M075

-- BEGIN SPEC
def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
-- END SPEC

/- SKELETON · monotone_converges
  Write `L` for `sSup (Set.range a)`.
  1. Open the definition: context gains `ε`, `hε : ε > 0`:                   R1
  2. Find a term above `L - ε`, in one `obtain`:                              R5
       its source: `exists_lt_of_lt_csSup` applied to                         R4
         the range is nonempty                                                R3
         `L - ε < L` from `hε`                                                R2
       result: `N : ℕ`, `hN : L - ε < a N`
  3. Choose that `N`; context gains `n`, `hn : n ≥ N`:                        R6
  4. Two facts about `a n` (one `have` each):
       h1 : a n ≤ L          from `hb` and `a n ∈ Set.range a`                R8, R7
       h2 : a N ≤ a n        from `hm` and `hn`                               R9
  5. `|a n - L| < ε` → two inequalities, split them:                          R10, constructor
  6. Each half is linear in `ε`, `L`, `a N`, `a n` given hN, h1, h2:          R11
-/
-- BEGIN SPEC
theorem monotone_converges (a : ℕ → ℝ) (hm : Monotone a) (hb : BddAbove (Set.range a)) :
    ConvergesTo a (sSup (Set.range a)) :=
-- END SPEC
  by
    intro ε hε
    obtain ⟨_, ⟨N, rfl⟩, hN⟩ := exists_lt_of_lt_csSup (Set.range_nonempty a) (sub_lt_self _ hε)
    refine ⟨N, fun n hn => ?_⟩
    have h1 : a n ≤ sSup (Set.range a) := le_csSup hb ⟨n, rfl⟩
    have h2 : a N ≤ a n := hm hn
    rw [abs_sub_lt_iff]
    constructor <;> linarith

end M075

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `L - ε` (with `L = sSup (Set.range a)`) is below the supremum, so it is not an upper bound: some term
    `a N` exceeds it. Monotonicity keeps every later term above it, and `L` bounds every term from above.
H2. After `intro ε hε`, get `N` and `hN : L - ε < a N` from `exists_lt_of_lt_csSup` (needs
    `Set.range_nonempty a` and `sub_lt_self _ hε`). Choose `N`; for `n ≥ N` collect
    `L - ε < a N ≤ a n ≤ L` as hypotheses, then unfold `|·| < ε` into two inequalities.
H3. `obtain ⟨_, ⟨N, rfl⟩, hN⟩ := exists_lt_of_lt_csSup (Set.range_nonempty a) (sub_lt_self _ hε)`;
    `refine ⟨N, fun n hn => ?_⟩`; `have h1 : a n ≤ sSup (Set.range a) := le_csSup hb ⟨n, rfl⟩`;
    `have h2 : a N ≤ a n := hm hn`; `rw [abs_sub_lt_iff]; constructor <;> linarith`.
-/
