/- M106 | Bisection invariants | 10-15 min | split_ifs, induction, Prod, pow_succ, loop invariant, mathlib
GOAL
  The bisection loop on `[a, b]` keeps a sign change `f lo ≤ 0 ≤ f hi`, halves the width at every step
  (width `(b - a) / 2ⁿ` after `n` steps), and produces nested intervals inside `[a, b]`.

REFERENCE
  example (p : ℝ × ℝ) : p = (p.1, p.2) := rfl      -- pairs: `.1` / `.2` project
  example (c : Prop) [Decidable c] (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ (if c then x else y) := by
    split_ifs with h; exacts [hx, hy]               -- one goal per branch, `h : c` / `h : ¬c`
  example (w : ℝ) (n : ℕ) : w / 2 ^ n / 2 = w / 2 ^ (n + 1) := by rw [pow_succ, div_div]
  example (a b : ℝ) : (a + b) / 2 - a = (b - a) / 2 := by ring
  `simp only [bisect, step]` unfolds one step; after `split_ifs`, `simp only` reduces `(x, y).1` to `x`.
BANNED: grind, try?
NOTE: `fun_induction bisect <;> grind` closes both; the point here is to write the loop invariant yourself.
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

-- BEGIN SPEC
theorem bisect_invariant (f : ℝ → ℝ) (a b : ℝ) (ha : f a ≤ 0) (hb : 0 ≤ f b) (n : ℕ) :
    f (bisect f a b n).1 ≤ 0 ∧ 0 ≤ f (bisect f a b n).2 ∧
      (bisect f a b n).2 - (bisect f a b n).1 = (b - a) / 2 ^ n :=
-- END SPEC
  by
    induction n with
    | zero => simp [bisect, ha, hb]
    | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      simp only [bisect, step]
      split_ifs with hm
      · refine ⟨hm, h2, ?_⟩
        simp only
        rw [pow_succ, ← div_div, ← h3]
        ring
      · refine ⟨h1, by linarith, ?_⟩
        simp only
        rw [pow_succ, ← div_div, ← h3]
        ring

-- BEGIN SPEC
theorem bisect_nested (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (n : ℕ) :
    a ≤ (bisect f a b n).1 ∧ (bisect f a b n).1 ≤ (bisect f a b (n + 1)).1 ∧
      (bisect f a b (n + 1)).2 ≤ (bisect f a b n).2 ∧ (bisect f a b n).2 ≤ b :=
-- END SPEC
  by
    -- WHY: the statement mentions step `n + 1`, so it is not its own induction hypothesis
    have inv : ∀ n, (bisect f a b n).1 ≤ (bisect f a b n).2 ∧ a ≤ (bisect f a b n).1 ∧
        (bisect f a b n).2 ≤ b := by
      intro n
      induction n with
      | zero => simp [bisect, hab]
      | succ n ih =>
        obtain ⟨h1, h2, h3⟩ := ih
        simp only [bisect, step]
        split_ifs <;> simp only <;> refine ⟨?_, ?_, ?_⟩ <;> linarith
    obtain ⟨h1, h2, h3⟩ := inv n
    refine ⟨h2, ?_, ?_, h3⟩ <;> simp only [bisect, step] <;> split_ifs <;> simp only <;> linarith

end M106

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both are loop invariants: `induction n`, and in the step case unfold `bisect`/`step` and split on the
    `if`. The new width is half the old one in either branch.
H2. `bisect_nested` is not inductive as stated (it mentions step `n + 1` but the IH only knows step `n`).
    First prove the stronger invariant `inv : ∀ n, lo ≤ hi ∧ a ≤ lo ∧ hi ≤ b` by induction, then unfold one step.
H3. Step case of the first: `obtain ⟨h1, h2, h3⟩ := ih; simp only [bisect, step]; split_ifs with hm`; in
    the `if`-true branch `refine ⟨hm, h2, ?_⟩`, in the else branch `refine ⟨h1, by linarith, ?_⟩`, then
    `simp only; rw [pow_succ, ← div_div, ← h3]; ring`. Second: after `obtain ⟨h1, h2, h3⟩ := inv n`,
    `refine ⟨h2, ?_, ?_, h3⟩ <;> simp only [bisect, step] <;> split_ifs <;> simp only <;> linarith`.
-/
