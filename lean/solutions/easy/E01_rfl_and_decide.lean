/- E01 | rfl, decide, #eval | 1-3 min | rfl, decide, #eval, def
GOAL
  Define `double` and prove three small facts about concrete numbers.

REFERENCE
  def f (n : Nat) : Nat := n + 1      -- a function; `f 3` evaluates to 4
  #eval f 3                           -- run it; result shows in the infoview
  example : f 3 = 4 := rfl            -- `rfl`: both sides compute to the same value
  example : 10 < 20 := by decide      -- `decide`: evaluate a decidable proposition
  theorem name : P := proof           -- named theorem; `example` is an anonymous one
  Replace every `sorry` with a proof (or, in a `def`, an expression).
-/

-- BEGIN SPEC
def double (n : Nat) : Nat :=
-- END SPEC
  2 * n

-- BEGIN SPEC
theorem double_three : double 3 = 6 :=
-- END SPEC
  rfl

-- BEGIN SPEC
theorem small_lt : 2 ^ 5 < 50 :=
-- END SPEC
  by decide

-- BEGIN SPEC
theorem bool_fact : (true && !false) = true :=
-- END SPEC
  rfl

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `double 3` should reduce to the literal `6` by computation alone.
H2. All three theorems are closed terms, so `rfl` or `by decide` work for each.
H3. `def double (n : Nat) : Nat := 2 * n` (or `n + n`), then `rfl`, `by decide`, `rfl`.
-/
