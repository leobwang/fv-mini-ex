/- E049 | Naming goals | 2-3 min | case, next, rename_i, intros, inaccessible names
GOAL
  `cases`, `induction` and `intros` without `with` leave tagged goals and unnamed hypotheses
  (shown as `a✝`, which you cannot type). Name them afterwards with `case`, `next` and `rename_i`.

BANNED: with, intro, rintro, fun, λ, flip, simp, simpa, simp_all, grind, decide, omega, ac_rfl, Nat.zero_add, Nat.add_comm, Nat.eq_zero_or_pos, assumption, apply_assumption, solve_by_elim, exact?, apply?, rw?, try?

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E049

/- SKELETON · zero_or_pos
  1. Split `n` without names: goals tagged `zero` and `succ` (`n✝ : Nat`):  R1
  2. `case zero`: goal `0 = 0 ∨ 1 ≤ 0`; prove the left side by `rfl`:       R2 → R3
  3. `case succ k`: name `n✝` as `k`; goal `k + 1 = 0 ∨ 1 ≤ k + 1`;
     prove the right side with the lemma at `n := 1`, `m := k`:            R2 → R3 → R4
-/
-- BEGIN SPEC
theorem zero_or_pos (n : Nat) : n = 0 ∨ 1 ≤ n :=
-- END SPEC
  sorry

/- SKELETON · intros_rename
  1. Move both premises into the context: `a✝¹ : P`, `a✝ : P → Q`:          R5
  2. Name them, oldest first:                                               R6
  3. Apply the function hypothesis to the other one:                        exact
-/
-- BEGIN SPEC
theorem intros_rename (P Q : Prop) : P → (P → Q) → Q :=
-- END SPEC
  sorry

/- SKELETON · next_bool
  1. Split `b`: goals `false`, `true`; `h` is rewritten in each:            R7
  2. First goal (`false`): `h : (false && c) = true` computes to
     `false = true`, an impossible hypothesis:                              R8 → R9
  3. Second goal (`true`): the goal `true = true`:                          R8, rfl
-/
-- BEGIN SPEC
theorem next_bool (b c : Bool) (h : (b && c) = true) : b = true :=
-- END SPEC
  sorry

/- SKELETON · zero_add'
  1. Induction on `n` without names: goals `zero`, `succ` (`n✝`, `a✝`):    R10
  2. `case zero`: `0 + 0 = 0` computes:                                     R2, rfl
  3. `case succ k ih`: name the variable and the IH
       ih : 0 + k = k      goal: 0 + (k + 1) = k + 1                        R11
  4. Pull the `+ 1` out of the left side, then use the IH:                  R12 → rw [ih]
-/
-- BEGIN SPEC
theorem zero_add' (n : Nat) : 0 + n = n :=
-- END SPEC
  sorry

end E049

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every proof here is "split first, name afterwards". Run `cases n`, `intros`, `cases b` or
    `induction n` with no names (R1, R5, R7, R10), then read the goal tags (`case zero`, `case succ`,
    `case false`) and the `✝` names in the infoview; those tell you what to write next.
H2. `zero_or_pos`: one `case` per tag, `Or.inl rfl` / `Or.inr …` (R2, R3, R4). `intros_rename`:
    `intros`, then `rename_i` with two names, oldest first (R6). `next_bool`: `cases b`, then two
    `next` blocks; in the first, `h : (false && c) = true` computes to `false = true` (R8, R9).
    `zero_add'`: `induction n`, `case zero`, then `case succ k ih` and rewrite (R11, R12).
H3. `zero_or_pos`: `case succ k => exact Or.inr (Nat.le_add_left 1 k)`.
    `intros_rename`: `rename_i hp hpq`, then apply `hpq`. `next_bool`: `next => nomatch h`.
    `zero_add'`: `case zero => rfl` and `case succ k ih => rw [Nat.add_succ, ih]`.
-/
