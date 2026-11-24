/- E049 | Naming goals | 2-3 min | case, next, rename_i, intros, inaccessible names
GOAL
  `cases`, `induction` and `intros` without `with` leave tagged goals and unnamed hypotheses
  (shown as `a✝`, which you cannot type). Name them afterwards with `case`, `next` and `rename_i`.

REFERENCE
  example (n : Nat) : n + 0 = n := by
    cases n
    case zero => rfl                -- pick the goal tagged `zero`
    case succ k => rfl              -- `case tag x y =>` also names the goal's new variables/IHs
  example (b : Bool) : (b || false) = b := by
    cases b
    next => rfl                     -- `next =>` takes the first remaining goal
    next => rfl
  example (P : Prop) : P → P := by
    intros; rename_i hp; exact hp   -- `intros` makes `a✝ : P`; `rename_i hp` names it
  #check @Nat.add_succ   -- n + m.succ = (n + m).succ       (Nat.le_add_left : n ≤ m + n)
BANNED: with, intro, rintro, fun, λ, flip, simp, simpa, simp_all, grind, decide, omega, ac_rfl, Nat.zero_add, Nat.add_comm, Nat.eq_zero_or_pos, assumption, apply_assumption, solve_by_elim, exact?, apply?, rw?, try?
NOTE: honor system: `intros` takes no names here; name its `a✝`s with `rename_i` (or `‹T›`, E046). `nomatch h` closes a goal when `h : false = true`.
-/

namespace E049

-- BEGIN SPEC
theorem zero_or_pos (n : Nat) : n = 0 ∨ 1 ≤ n :=
-- END SPEC
  by
    cases n
    case zero => exact Or.inl rfl
    case succ k => exact Or.inr (Nat.le_add_left 1 k)

-- BEGIN SPEC
theorem intros_rename (P Q : Prop) : P → (P → Q) → Q :=
-- END SPEC
  by
    intros
    rename_i hp hpq
    exact hpq hp

-- BEGIN SPEC
theorem next_bool (b c : Bool) (h : (b && c) = true) : b = true :=
-- END SPEC
  by
    cases b
    next => nomatch h
    next => rfl

-- BEGIN SPEC
theorem zero_add' (n : Nat) : 0 + n = n :=
-- END SPEC
  by
    induction n
    case zero => rfl
    case succ k ih => rw [Nat.add_succ, ih]

end E049

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Run the splitting tactic first (`cases n`, `intros`, `cases b`, `induction n`), then look at
    the goal tags (`case zero`, `case succ`) and the `✝` names in the infoview.
H2. `rename_i x y` names the most recent inaccessible hypotheses, in order. In `next_bool` the
    `false` branch has `h : (false && c) = true`, which computes to `false = true`.
H3. `zero_add'`: `induction n`, then `case zero => rfl` and `case succ k ih => rw [Nat.add_succ, ih]`.
    `zero_or_pos`, succ branch: `case succ k => exact Or.inr (Nat.le_add_left 1 k)`.
-/
