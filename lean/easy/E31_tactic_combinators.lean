/- E31 | Tactic combinators | 3 min | <;>, all_goals, refine, first, assumption
GOAL
  Handle several similar goals at once with tactic combinators.

REFERENCE
  example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by refine ⟨?_, ?_⟩ <;> assumption
    -- `?_` leaves a goal; `t <;> s` runs s on all goals from t; `assumption` searches context
  example (n : Nat) : n + 0 = n ∧ 0 + n = n := by constructor; all_goals simp
  example (n : Nat) : n = n ∧ n ≤ n + 1 := by constructor <;> first | rfl | omega
  example (n : Nat) (h : n < 2) : n * n < 4 := by
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> decide          -- case split on values, then compute
-/

-- BEGIN SPEC
theorem three_goals (a b : Nat) (h : a = b) : a + 0 = b ∧ 0 + a = b ∧ a * 1 = b :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem nested_and (p q r : Prop) (hp : p) (hq : q) (hr : r) : (p ∧ q) ∧ (r ∧ p) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem small_square (n : Nat) (h : n < 3) : n * n < 9 :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each goal splits into parts that all close with the same tactic.
H2. `refine ⟨?_, ?_, ?_⟩ <;> simp [h]`; `constructor <;> constructor <;> assumption`.
H3. `small_square`: `omega` cannot square, so list the cases: `have : n = 0 ∨ n = 1 ∨ n = 2 := by omega` then `rcases this with rfl | rfl | rfl <;> decide`.
-/
