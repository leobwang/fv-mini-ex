/- E031 | Tactic combinators | 3 min | <;>, all_goals, refine, first, assumption
GOAL
  Handle several similar goals at once with tactic combinators.

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · three_goals
  1. One goal → three goals, one per conjunct:                                  R1
  2. All three close the same way: `simp [h]` normalises `a + 0`, `0 + a`,
     `a * 1` to `a`, then rewrites `a` to `b`. Run it on every goal at once:     R2 (or R4) with R3
-/
-- BEGIN SPEC
theorem three_goals (a b : Nat) (h : a = b) : a + 0 = b ∧ 0 + a = b ∧ a * 1 = b :=
-- END SPEC
  sorry

/- SKELETON · nested_and
  1. Split the outer `∧`: goals `p ∧ q` and `r ∧ p`:                            R5
  2. Split each of those, chained after step 1: goals `p`, `q`, `r`, `p`:       R2 with R5
  3. Each goal is a hypothesis; one closer for all four, chained again:         R6 with R7
-/
-- BEGIN SPEC
theorem nested_and (p q r : Prop) (hp : p) (hq : q) (hr : r) : (p ∧ q) ∧ (r ∧ p) :=
-- END SPEC
  sorry

/- SKELETON · small_square
  `omega` cannot prove `n * n < 9` (a product of two variables), but `h` leaves three values.
  1. Prove the list of values first, by linear arithmetic:                      R8 with R9
       this : n = 0 ∨ n = 1 ∨ n = 2
  2. Split `this`, substituting each value for `n`; goals `0 * 0 < 9`, …:       R10
  3. Every goal is now concrete: compute them all at once:                      R2 (or R4) with R11
-/
-- BEGIN SPEC
theorem small_square (n : Nat) (h : n < 3) : n * n < 9 :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each theorem produces several goals of the same kind that one tactic closes. The work is creating
    those goals (`refine`, `constructor`, `rcases`) and running the closer on all of them (`<;>`,
    `all_goals`). In `small_square`, `omega` cannot handle `n * n`: make `n` a concrete number first.
H2. `three_goals`: three `?_` holes, then `simp [h]` on every goal. `nested_and`: two levels of
    `constructor`, then `assumption` on all four goals. `small_square`: `have` the list of possible
    values of `n` (by `omega`), case-split it with the `rfl` pattern, then `decide` each case.
H3. `three_goals`: `refine ⟨?_, ?_, ?_⟩`, then `simp [h]` reaching all three goals (`<;>`).
    `nested_and`: `constructor <;> constructor`, then `assumption` chained the same way.
    `small_square`: `have : n = 0 ∨ n = 1 ∨ n = 2 := by omega`, then
    `rcases this with rfl | rfl | rfl` with `decide` on every case.
-/
