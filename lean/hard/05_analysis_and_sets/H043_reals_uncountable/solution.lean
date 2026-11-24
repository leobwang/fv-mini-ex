/- H043 | ℝ is uncountable | 1-1.5 h | nested intervals, recursive def, split_ifs, sSup, mathlib
GOAL
  No sequence `f : ℕ → ℝ` lists every real. Build nested closed intervals `[l n, r n]`: step `n`
  keeps a third of the current interval that misses `f n`. `x = sSup {l n}` (least upper bound of
  the left endpoints) lies in every interval, so `x ≠ f n` for all `n` (Cantor's argument).

REFERENCE
  example (p : ℝ × ℝ) : ℝ × ℝ := (p.2, p.1)   -- pairs `(a, b)`; projections `p.1`, `p.2`
  noncomputable example (z : ℝ) : ℝ := if z < 0 then -z else z   -- `if` on reals: `noncomputable`
  -- `split_ifs with h` splits a goal containing `if c then .. else ..` into the two cases (h : c / h : ¬c)
  -- recursive def: `| 0 => base  | n + 1 => step (I f n) (f n)`;  `simp only [I] at h` unfolds one step
  #check monotone_nat_of_le_succ  -- (∀ n, f n ≤ f (n + 1)) → Monotone f   (Monotone: a ≤ b → f a ≤ f b)
  #check antitone_nat_of_succ_le  -- (∀ n, f (n + 1) ≤ f n) → Antitone f
  #check le_csSup                 -- BddAbove s → a ∈ s → a ≤ sSup s
  #check csSup_le                 -- s.Nonempty → (∀ b ∈ s, b ≤ a) → sSup s ≤ a
  #check Set.range_nonempty       -- (f : ℕ → α) : (Set.range f).Nonempty
  example (f : ℕ → ℝ) (n : ℕ) : f n ∈ Set.range f := ⟨n, rfl⟩
BANNED: import, Surjective, cantor_surjective
NOTE: imports are frozen (no `import` may be added): ℝ's order and `sSup`; no countability, measure or topology.
-/
-- BEGIN SPEC
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
-- END SPEC

namespace H043

-- MILESTONE (optional: change or delete)
-- From `p = (a, b)` keep `[(a + 2b)/3, b]` if `z` is left of `(a + 2b)/3`, else `[a, (2a + b)/3]`.
noncomputable def step (p : ℝ × ℝ) (z : ℝ) : ℝ × ℝ :=
  if z < (p.1 + 2 * p.2) / 3 then ((p.1 + 2 * p.2) / 3, p.2) else (p.1, (2 * p.1 + p.2) / 3)

-- MILESTONE (optional: change or delete)
noncomputable def I (f : ℕ → ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, 1)
  | n + 1 => step (I f n) (f n)

-- MILESTONE (optional: change or delete)
-- The new interval is nonempty, nested in `p`, and `z` lies strictly outside it.
theorem step_spec (p : ℝ × ℝ) (z : ℝ) (h : p.1 < p.2) :
    (step p z).1 < (step p z).2 ∧ p.1 ≤ (step p z).1 ∧ (step p z).2 ≤ p.2 ∧
    (z < (step p z).1 ∨ (step p z).2 < z) := by
  unfold step
  split_ifs with hz
  · refine ⟨by simp only; linarith, by simp only; linarith, le_rfl, Or.inl hz⟩
  · push Not at hz
    refine ⟨by simp only; linarith, le_rfl, by simp only; linarith, Or.inr (by simp only; linarith)⟩

-- MILESTONE (optional: change or delete)
theorem I_lt (f : ℕ → ℝ) (n : ℕ) : (I f n).1 < (I f n).2 := by
  induction n with
  | zero => simp [I]
  | succ n ih => exact (step_spec _ (f n) ih).1

-- MILESTONE (optional: change or delete)
theorem left_le_right (f : ℕ → ℝ) (n m : ℕ) : (I f n).1 ≤ (I f m).2 := by
  have hmono : Monotone (fun k => (I f k).1) :=
    monotone_nat_of_le_succ fun k => (step_spec _ (f k) (I_lt f k)).2.1
  have hanti : Antitone (fun k => (I f k).2) :=
    antitone_nat_of_succ_le fun k => (step_spec _ (f k) (I_lt f k)).2.2.1
  calc (I f n).1 ≤ (I f (max n m)).1 := hmono (le_max_left _ _)
    _ ≤ (I f (max n m)).2 := (I_lt f _).le
    _ ≤ (I f m).2 := hanti (le_max_right _ _)

-- BEGIN SPEC
theorem real_uncountable (f : ℕ → ℝ) : ∃ x : ℝ, ∀ n, f n ≠ x :=
-- END SPEC
  by
    set x := sSup (Set.range fun k => (I f k).1)
    have hbdd : BddAbove (Set.range fun k => (I f k).1) :=
      ⟨(I f 0).2, by rintro _ ⟨k, rfl⟩; exact left_le_right f k 0⟩
    have hlo : ∀ k, (I f k).1 ≤ x := fun k => le_csSup hbdd ⟨k, rfl⟩
    have hhi : ∀ k, x ≤ (I f k).2 := fun k =>
      csSup_le (Set.range_nonempty _) (by rintro _ ⟨j, rfl⟩; exact left_le_right f j k)
    refine ⟨x, fun n hn => ?_⟩
    have h1 := hlo (n + 1)
    have h2 := hhi (n + 1)
    simp only [I] at h1 h2
    rcases (step_spec (I f n) (f n) (I_lt f n)).2.2.2 with h | h <;> linarith

end H043

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `step_spec`: `unfold step; split_ifs with hz`, then each part is `linarith` (use `push Not at hz` in the else-branch; `simp only` reduces `((u, v)).1` to `u`). `I_lt`: induction on `n`.
H2. Left endpoints are monotone and right endpoints antitone (`step_spec` + the `_succ` lemmas). For `left_le_right n m`, go through index `max n m`: `l n ≤ l (max n m) < r (max n m) ≤ r m`.
H3. `x := sSup (Set.range fun n => (I f n).1)`; then `(I f k).1 ≤ x ≤ (I f k).2` for every `k`. Given `f n = x`, take `k = n + 1`, `simp only [I] at h1 h2`, and `rcases (step_spec (I f n) (f n) (I_lt f n)).2.2.2 with h | h <;> linarith`.
-/
