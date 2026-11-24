/- M106 | Bisection invariants | 10-15 min | split_ifs, induction, Prod, pow_succ, loop invariant, mathlib
GOAL
  The bisection loop on `[a, b]` keeps a sign change `f lo ≤ 0 ≤ f hi`, halves the width at every step
  (width `(b - a) / 2ⁿ` after `n` steps), and produces nested intervals inside `[a, b]`.
BANNED: grind, try?

GUIDE
  Entries R1–R11: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M106

-- BEGIN SPEC
/-- one bisection step: keep the half `[lo, mid]` or `[mid, hi]` that still has a sign change -/
noncomputable def step (f : ℝ → ℝ) (I : ℝ × ℝ) : ℝ × ℝ :=
  if f ((I.1 + I.2) / 2) ≤ 0 then ((I.1 + I.2) / 2, I.2) else (I.1, (I.1 + I.2) / 2)

/-- the interval `(lo, hi)` after `n` steps -/
noncomputable def bisect (f : ℝ → ℝ) (a b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a, b)
  | n + 1 => step f (bisect f a b n)
-- END SPEC

/- SKELETON · bisect_invariant
  1. Induction on the step count `n`:                                       R1
  2. zero: unfold `bisect f a b 0` to `(a, b)`, clear `/ 2 ^ 0`, use ha, hb:  R2, R3 (one `simp [..]`)
  3. succ n ih:
       take `ih` apart into h1 h2 h3                                        R4
       unfold one step; the goal now holds the midpoint `if` four times     R2, R5
       split on the midpoint test, naming it `hm`                           R6
     then-branch (`hm : f mid ≤ 0`, new interval `(mid, hi)`):
       the two sign facts are `hm` and `h2`; keep the width as a `?_`       refine
         (`refine` accepts `hm` for `f (mid, hi).1 ≤ 0`: R7's reduction is definitional)
       width: reduce the pairs, `2 ^ (n + 1)` → `2 ^ n * 2`,
         `/ (2 ^ n * 2)` → `/ 2 ^ n / 2`, put the old width back, finish   R7, R8, R9, rw [← h3], R10
     else-branch (`hm : ¬f mid ≤ 0`, new interval `(lo, mid)`):
       sign facts: `h1`, and `0 ≤ f mid` from `hm`                          refine, R11
       width: as in the then-branch                                         R7, R8, R9, rw [← h3], R10
-/
-- BEGIN SPEC
theorem bisect_invariant (f : ℝ → ℝ) (a b : ℝ) (ha : f a ≤ 0) (hb : 0 ≤ f b) (n : ℕ) :
    f (bisect f a b n).1 ≤ 0 ∧ 0 ≤ f (bisect f a b n).2 ∧
      (bisect f a b n).2 - (bisect f a b n).1 = (b - a) / 2 ^ n :=
-- END SPEC
  sorry

/- SKELETON · bisect_nested
  1. MILESTONE first (inside this proof): the statement is not inductive, it relates steps n and n + 1.
       have inv : ∀ n, (bisect f a b n).1 ≤ (bisect f a b n).2 ∧ a ≤ (bisect f a b n).1 ∧
           (bisect f a b n).2 ≤ b
     proof: intro n, then                                                   R1
       zero: `simp [bisect, hab]` (it proves `a ≤ a`, `b ≤ b` itself)       R2
       succ: take ih apart, unfold, split, reduce the pairs,
             split the three conjuncts, each by linear arithmetic           R4, R2, R5, R6, R7, refine, R11
  2. Instantiate it at `n`: h1 h2 h3                                         R4 on `inv n`
  3. Conjuncts 1 and 4 are `h2` and `h3`; leave 2 and 3 as `?_`              refine
  4. In both: unfold the step at `n + 1`, split, reduce, linear arithmetic   R2, R5, R6, R7, R11
     (the midpoint of `lo ≤ hi` lies between them: this is where `h1` is used)
-/
-- BEGIN SPEC
theorem bisect_nested (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (n : ℕ) :
    a ≤ (bisect f a b n).1 ∧ (bisect f a b n).1 ≤ (bisect f a b (n + 1)).1 ∧
      (bisect f a b (n + 1)).2 ≤ (bisect f a b n).2 ∧ (bisect f a b n).2 ≤ b :=
-- END SPEC
  sorry

end M106

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both are loop invariants: induction on `n` (R1). In the step case unfold one step with
    `simp only [bisect, step]` (R2, R5) and split on the midpoint test with `split_ifs` (R6). In either
    branch the new width is half the old one.
H2. `bisect_invariant`: after `obtain ⟨h1, h2, h3⟩ := ih` (R4), unfold and split, fill the two sign facts
    with `refine` and prove the width by `simp only` (R7), R8, R9, `rw [← h3]`, `ring` (R10).
    `bisect_nested` is not inductive as stated: first prove the stronger
    `inv : ∀ n, lo ≤ hi ∧ a ≤ lo ∧ hi ≤ b` by induction, then unfold one step and use `linarith` (R11).
H3. Width step, either branch: `simp only; rw [pow_succ, ← div_div, ← h3]; ring`. Else-branch signs:
    `refine ⟨h1, by linarith, ?_⟩`. Nested, after `obtain ⟨h1, h2, h3⟩ := inv n`:
    `refine ⟨h2, ?_, ?_, h3⟩ <;> simp only [bisect, step] <;> split_ifs <;> simp only <;> linarith`.
-/
