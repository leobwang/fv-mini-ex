/- M074 | Computing a supremum | 10-15 min | sSup, IsLUB, Archimedean, mathlib
GOAL
  Show `sup {1 - 1/(n+1) | n ∈ ℕ} = 1`: `1` is an upper bound, and any `b < 1` is beaten by some term
  (Archimedean property).
BANNED: isLUB_of_tendsto_atTop, isGLB_of_tendsto_atTop, tendsto_one_div_add_atTop_nhds_zero_nat, Tendsto, tendsto, nhds, 𝓝, Filter, atTop

GUIDE
  Entries R1–R15: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M074

/- SKELETON · sSup_one_sub_inv
  1. `sSup` → `IsLUB`; pass nonemptiness (the `n = 0` term) inline:                       R1, R2
  2. Split `IsLUB` into its two halves:                                                  R3
  3. Upper bound (`case left`):
       take a term of the range                                                          R4
       have : 0 < 1 / ((n : ℝ) + 1)                                                      R5
       beta-reduce the goal, then finish                                                 R6, R7
  4. Least among upper bounds (`case right`):
       take an upper bound `b` and its proof `hb`                                        R8
       suppose `b < 1`                                                                   R9, R10
       h1 : 0 < 1 - b                                                                    R7
       a natural `n` with `1 / (1 - b) < ↑n`                                             R11
       hbn : 1 - 1 / ((n : ℝ) + 1) ≤ b, from `hb`                                        R12
       key fact `1 / ((n : ℝ) + 1) < 1 - b`:
         clear the goal's denominator, then `hn`'s (with `h1`)                           R13 + R5, R14
         finish                                                                          R15
       `hbn` and the key fact contradict each other                                      R7
-/
-- BEGIN SPEC
theorem sSup_one_sub_inv : sSup (Set.range fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) = 1 :=
-- END SPEC
  sorry

end M074

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `sSup` is junk (`0`) on empty or unbounded sets, so go through the honest statement
    `IsLUB (Set.range …) 1` plus nonemptiness (the `n = 0` term). `IsLUB` = upper bound ∧ least.
H2. `apply IsLUB.csSup_eq _ ⟨_, Set.mem_range_self 0⟩; constructor`. Upper bound: `rintro _ ⟨n, rfl⟩`,
    get `0 < 1 / ((n : ℝ) + 1)` by `positivity`, `dsimp only`, `linarith`. Least: `intro b hb`,
    `by_contra hlt; push Not at hlt` gives `b < 1`; then find a term above `b` (Archimedes).
H3. With `h1 : 0 < 1 - b`: `obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - b))`, then prove
    `1 / ((n : ℝ) + 1) < 1 - b` by `rw [div_lt_iff₀ (by positivity)]; rw [div_lt_iff₀ h1] at hn; nlinarith`,
    and close with `linarith` against `hb ⟨n, rfl⟩ : 1 - 1 / ((n : ℝ) + 1) ≤ b`.
-/
