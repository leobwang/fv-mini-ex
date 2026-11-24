/- H043 | ℝ is uncountable | 1-1.5 h | nested intervals, recursive def, split_ifs, sSup, mathlib
GOAL
  No sequence `f : ℕ → ℝ` lists every real. Build nested closed intervals `[l n, r n]`: step `n`
  keeps a third of the current interval that misses `f n`. `x = sSup {l n}` (least upper bound of
  the left endpoints) lies in every interval, so `x ≠ f n` for all `n` (Cantor's argument).

BANNED: import, Surjective, cantor_surjective

GUIDE
  Entries R1–R24: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
-- BEGIN SPEC
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
-- END SPEC

namespace H043

/- SKELETON · the MILESTONES (do these FIRST, in order)
  `step` and `I` build the intervals; `step_spec` is used by `I_lt`, `left_le_right` and the last
  line of `real_uncountable`; `I_lt` by `left_le_right` and `real_uncountable`; `left_le_right` gives
  both bounds on `x` in `real_uncountable`.
  step:
    1. The `:=` is written: the body is one term, an `if` on `z < (p.1 + 2 * p.2) / 3`
       returning one of two pairs                                                   R1
    2. Test it: `example : step (0, 3) 0 = (2, 3) := by norm_num [step]`
-/
-- MILESTONE (optional: change or delete)
-- From `p = (a, b)` keep `[(a + 2b)/3, b]` if `z` is left of `(a + 2b)/3`, else `[a, (2a + b)/3]`.
noncomputable def step (p : ℝ × ℝ) (z : ℝ) : ℝ × ℝ :=
  sorry

-- MILESTONE (optional: change or delete)
noncomputable def I (f : ℕ → ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, 1)
  | n + 1 => step (I f n) (f n)

/- SKELETON · step_spec
  1. Unfold `step` and split its `if` (goals `case pos`, `hz : z < …`, and `case neg`,
     `hz : ¬z < …`):                                                                R2, R3
  2. In the `neg` branch only, first turn `hz : ¬z < …` into `… ≤ z`:               R7
  3. In each branch, split the four parts with `refine ⟨?_, ?_, ?_, ?_⟩` (or `⟨by …, …⟩`):
       an inequality between pair components: reduce the pairs, then linear arith   R4, R5
       an endpoint that did not move (`… ≤ p.2` or `p.1 ≤ …`)                       R6
       `z` outside: `Or.inl hz` (pos) / `Or.inr` and then R4, R5 (neg)
-/
-- MILESTONE (optional: change or delete)
-- The new interval is nonempty, nested in `p`, and `z` lies strictly outside it.
theorem step_spec (p : ℝ × ℝ) (z : ℝ) (h : p.1 < p.2) :
    (step p z).1 < (step p z).2 ∧ p.1 ≤ (step p z).1 ∧ (step p z).2 ≤ p.2 ∧
    (z < (step p z).1 ∨ (step p z).2 < z) := by
  sorry

/- SKELETON · I_lt   (uses step_spec)
  1. `induction n with`
  2. zero: the base pair `(0, 1)`                                                   R8
  3. succ: `I f (n + 1)` is `step (I f n) (f n)` by definition, so the first part of
     `step_spec _ (f n) ih` is the goal (or unfold first)                           R10 (R9)
-/
-- MILESTONE (optional: change or delete)
theorem I_lt (f : ℕ → ℝ) (n : ℕ) : (I f n).1 < (I f n).2 := by
  sorry

/- SKELETON · left_le_right   (uses step_spec, I_lt)
  1. have hmono : Monotone (fun k => (I f k).1): reduce to one step, `intro k`, and
     that step is a part of `step_spec _ (f k) (I_lt f k)`:                         R12, R10
  2. have hanti : Antitone (fun k => (I f k).2), likewise:                          R13, R10
  3. Go through index `max n m` in a chain of three links:                          R16
       (I f n).1 ≤ (I f (max n m)).1                                                R11, R14
       _ ≤ (I f (max n m)).2               from I_lt                                R15
       _ ≤ (I f m).2                                                                R11, R14
-/
-- MILESTONE (optional: change or delete)
theorem left_le_right (f : ℕ → ℝ) (n m : ℕ) : (I f n).1 ≤ (I f m).2 := by
  sorry

/- SKELETON · real_uncountable   (uses all the milestones)
  1. Name the witness x := sSup (Set.range fun k => (I f k).1):                     R17
  2. hbdd : BddAbove (Set.range fun k => (I f k).1), bound (I f 0).2,
     each element by left_le_right (`exact` accepts the goal's `(fun k => …) k`):   R19, R20
  3. hlo : ∀ k, (I f k).1 ≤ x                                                       R21, R18
     hhi : ∀ k, x ≤ (I f k).2         each element by left_le_right                 R22, R23, R20
  4. Give x and open `f n ≠ x`:  refine ⟨x, fun n hn => ?_⟩                          R24
  5. Specialise h1 := hlo (n + 1), h2 := hhi (n + 1); unfold `I` one step in both:  R9
  6. Split "f n is outside" from step_spec (… (I_lt f n)).2.2.2 with `rcases … with h | h`,
     and each case is a contradiction with hn, h1, h2:                              R10, R5
-/
-- BEGIN SPEC
theorem real_uncountable (f : ℕ → ℝ) : ∃ x : ℝ, ∀ n, f n ≠ x :=
-- END SPEC
  sorry

end H043

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Do the milestones in order. `step_spec` is case analysis on the `if` (R2, R3) and linear
    arithmetic after reducing the pairs (R4, R5, R7). `I_lt` is induction on `n` with `step_spec`.
    The witness is the least upper bound of the left endpoints, `sSup (Set.range fun k => (I f k).1)`.
H2. Left ends increase and right ends decrease (R12, R13 with parts of `step_spec`), so
    `left_le_right n m` goes through index `max n m`: `l n ≤ l (max n m) < r (max n m) ≤ r m` (R16).
    Then `left_le_right` gives `BddAbove`, `(I f k).1 ≤ x` (R21) and `x ≤ (I f k).2` (R22) for all `k`.
    If `f n = x`, then `x` lies in interval `n + 1`, which `f n` misses.
H3. `step_spec`: `unfold step; split_ifs with hz`, then `refine ⟨by simp only; linarith, …⟩`, with
    `push Not at hz` in the else branch. Last step: `refine ⟨x, fun n hn => ?_⟩`,
    `have h1 := hlo (n + 1)`, `have h2 := hhi (n + 1)`, `simp only [I] at h1 h2`, then
    `rcases (step_spec (I f n) (f n) (I_lt f n)).2.2.2 with h | h <;> linarith`.
-/
