/- E087 | Unique existence | 2-3 min | ExistsUnique, ∃!, anonymous constructor, obtain, mathlib
GOAL
  Prove `∃! x, p x` ("exactly one `x` satisfies `p`") for two equations, then use a uniqueness
  hypothesis to show that two solutions are equal.

BANNED: simp, simp_all, simpa, norm_num, aesop, grind, ExistsUnique.unique, exact?, try?

GUIDE
  Entries R1–R10: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E087

/- SKELETON · unique_sol
  (`∃! n, p n` means `∃ n, p n ∧ ∀ y, p y → y = n`; optional look:              R1)
  1. Give the witness `3` and prove "3 works" by computation in the same step:    R4 (or R2, then rfl)
     what the goals print as `(fun n => n + 2 = 5) y` is just `y + 2 = 5`:        R3
  2. Uniqueness: take `y` and its hypothesis `hy : y + 2 = 5`:                    R5
  3. Close `y = 3` from `hy` (linear arithmetic over ℕ):                          R6
-/
-- BEGIN SPEC
theorem unique_sol : ∃! n : ℕ, n + 2 = 5 :=
-- END SPEC
  sorry

/- SKELETON · unique_real
  1. Same shape as `unique_sol`: witness `3`, existence, uniqueness:              R2 (or R8 as one term)
  2. Existence `2 * 3 + 1 = 7` over ℝ: `rfl` fails on real numerals:              R7
  3. Uniqueness: take `y`, `hy`, then close `y = 3` (`omega` fails over ℝ):       R5, R7
-/
-- BEGIN SPEC
theorem unique_real : ∃! x : ℝ, 2 * x + 1 = 7 :=
-- END SPEC
  sorry

/- SKELETON · unique_use
  1. Take `h` apart: the unique `x`, `hx : p x`, `hu : ∀ y, p y → y = x`:         R9
  2. Turn `a` into `x` with `hu a ha`, and `b` into `x` with `hu b hb`;
     the goal becomes `x = x`, which `rw` closes:                                 R10, R10
-/
-- BEGIN SPEC
theorem unique_use (p : ℕ → Prop) (h : ∃! n, p n) (a b : ℕ) (ha : p a) (hb : p b) : a = b :=
-- END SPEC
  sorry

end E087

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. An `∃!` proof is a triple: the witness, a proof that it satisfies the property, and a uniqueness
    function `∀ y, … → y = witness` (R2, R8). A hypothesis `h : ∃! n, p n` comes apart into the
    same three pieces (R9).
H2. Witness `3` in both. Existence: `rfl` over ℕ (R4), `linarith` over ℝ (R7). Uniqueness: `intro y hy`
    (R5), then `omega` over ℕ (R6) and `linarith` over ℝ (R7). For `unique_use`, both `a` and `b`
    equal the unique `x` (R10).
H3. `unique_sol`: `refine ⟨3, rfl, ?_⟩; intro y hy; omega`. `unique_real`: `⟨3, by linarith, fun y hy => …⟩`.
    `unique_use`: `obtain ⟨x, hx, hu⟩ := h; rw [hu a ha, …]`.
-/
