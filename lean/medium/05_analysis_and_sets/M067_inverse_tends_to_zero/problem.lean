/- M067 | 1/(n+1) tends to 0 | 15 min | epsilon-N, Archimedean, abs, mathlib
GOAL
  With the explicit ε-N definition of convergence, prove that constant sequences converge and
  that `1 / (n + 1) → 0`.

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M067

-- BEGIN SPEC
def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
-- END SPEC

/- SKELETON · const_converges
  1. Open the definition: context gains `ε`, `hε : ε > 0`:                    R1
  2. Any `N` works: give `0`, ignore the bound `n ≥ 0` (write `_`):           R2
  3. The goal is `|(fun x => c) n - c| < ε`. `simp` would turn it into `0 < ε` (R3);
     `simpa using hε` does that and closes it with `hε` in one step:          R4
-/
-- BEGIN SPEC
theorem const_converges (c : ℝ) : ConvergesTo (fun _ => c) c :=
-- END SPEC
  sorry

/- SKELETON · inv_succ_converges
  1. Open the definition: context gains `ε`, `hε : ε > 0`:                    R1
  2. Choose `N` FIRST, from the Archimedean property applied to `1 / ε`:      R5, R6
       hN : 1 / ε < ↑N
  3. Give `N` as the witness; context gains `n`, `hn : n ≥ N`:                R2
  4. Cast the bound to ℝ:                                                     R7
       hn' : (N : ℝ) ≤ n
  5. Simplify the goal `|(fun n => 1 / (↑n + 1)) n - 0| < ε`:
       drop `- 0`                                                             R8
       drop `|·|`; side goal `0 < (fun n => …) n` by `(by positivity)`       R9, R10
       clear the denominator: goal `1 < ε * (↑n + 1)`                         R11, R10
  6. Clear the denominator in `hN` too: `hN : 1 < ↑N * ε`:                    R12
  7. Finish: needs the product of `hn'` and `hε`:                             R13
-/
-- BEGIN SPEC
theorem inv_succ_converges : ConvergesTo (fun n => 1 / ((n : ℝ) + 1)) 0 :=
-- END SPEC
  sorry

end M067

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold: given `ε > 0`, find `N` with `1 / (n + 1) < ε` for all `n ≥ N`; choose `N > 1 / ε`.
    The constant sequence needs no thought: `|c - c| = 0 < ε` for any `N`.
H2. Get `N` from `exists_nat_gt (1 / ε)` before giving the witness; cast `hn` to ℝ; remove `- 0`
    and `|·|` (the term is positive); clear both denominators with `div_lt_iff₀`; finish with `nlinarith`.
H3. `rw [sub_zero, abs_of_pos (by positivity), div_lt_iff₀ (by positivity)]`, then
    `rw [div_lt_iff₀ hε] at hN`, then `nlinarith` (it uses `hn' : (N : ℝ) ≤ n` times `hε`).
-/
