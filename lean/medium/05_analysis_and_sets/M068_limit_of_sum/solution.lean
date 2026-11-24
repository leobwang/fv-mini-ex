/- M068 | Limit of a sum | 10-15 min | epsilon-N, epsilon/2, max, triangle inequality, mathlib
GOAL
  If `a n → La` and `b n → Lb`, then `a n + b n → La + Lb`, using the explicit ε-N definition.

BANNED: Filter.Tendsto.add, tendsto_add

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M068

-- BEGIN SPEC
def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
-- END SPEC

/- SKELETON · converges_add
  1. Open the definition: context gains `ε`, `hε : ε > 0`:                    R1
  2. Ask each hypothesis for precision `ε / 2` (side goal by R2):             R3 with R2
       N1, h1 : ∀ n ≥ N1, |a n - La| < ε / 2       (from `ha`)
       N2, h2 : ∀ n ≥ N2, |b n - Lb| < ε / 2       (from `hb`)
  3. Give the witness `max N1 N2`; context gains `n`, `hn : n ≥ max N1 N2`:   R4
  4. Instantiate both bounds at `n`, with `n ≥ N1` / `n ≥ N2` from `hn`:      R5 with R6, R5 with R7
       e1 : |a n - La| < ε / 2        e2 : |b n - Lb| < ε / 2
  5. One `calc` from `|a n + b n - (La + Lb)|` (beta-reduced goal):           R8
       = |(a n - La) + (b n - Lb)|                                            R9
       ≤ |a n - La| + |b n - Lb|                                              R10
       < ε / 2 + ε / 2                                                        R11
       = ε                                                                    R12
-/
-- BEGIN SPEC
theorem converges_add (a b : ℕ → ℝ) (La Lb : ℝ) (ha : ConvergesTo a La) (hb : ConvergesTo b Lb) :
    ConvergesTo (fun n => a n + b n) (La + Lb) :=
-- END SPEC
  by
    intro ε hε
    obtain ⟨N1, h1⟩ := ha (ε / 2) (by positivity)
    obtain ⟨N2, h2⟩ := hb (ε / 2) (by positivity)
    refine ⟨max N1 N2, fun n hn => ?_⟩
    have e1 := h1 n (le_of_max_le_left hn)
    have e2 := h2 n (le_of_max_le_right hn)
    calc |a n + b n - (La + Lb)| = |(a n - La) + (b n - Lb)| := by ring_nf
      _ ≤ |a n - La| + |b n - Lb| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add e1 e2
      _ = ε := by ring

end M068

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Ask each hypothesis for precision `ε / 2`, not `ε`; one `N` must serve both sequences.
H2. `intro ε hε`; `obtain` `N1`, `N2` from `ha (ε / 2) _`, `hb (ε / 2) _`; witness `max N1 N2`; get both
    bounds at `n` via `le_of_max_le_left/right hn`; regroup as `(a n - La) + (b n - Lb)`, apply the
    triangle inequality `abs_add_le`, add the two bounds with `add_lt_add`.
H3. `calc |a n + b n - (La + Lb)| = |(a n - La) + (b n - Lb)| := by ring_nf
      _ ≤ |a n - La| + |b n - Lb| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add e1 e2
      _ = ε := by ring`
-/
