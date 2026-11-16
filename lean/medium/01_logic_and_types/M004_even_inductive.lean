/- M004 | Even as an inductive predicate | 10-15 min | inductive Prop, induction on derivations, cases inversion
GOAL
  `Ev n` holds when it can be derived from the two rules. Prove it agrees with `∃ k, n = 2 * k`
  and use inversion to refute and peel derivations.

REFERENCE
  inductive Small : Nat → Prop | zero : Small 0 | one : Small 1
  example : Small 1 := .one                         -- apply a rule (constructor)
  example (n : Nat) (h : Small n) : n ≤ 1 := by
    induction h with                                -- induction on the derivation
    | zero => decide
    | one => decide
  example : ¬ Small 2 := by intro h; cases h        -- inversion: no rule produces Small 2
  -- `cases h` on `h : Ev (n + 2)` leaves only the `step` case, giving `Ev n`.
-/

namespace M004

-- BEGIN SPEC
inductive Ev : Nat → Prop
  | zero : Ev 0
  | step (n : Nat) : Ev n → Ev (n + 2)
-- END SPEC

-- BEGIN SPEC
theorem ev_four : Ev 4 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem ev_double (n : Nat) : Ev (2 * n) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem ev_exists (n : Nat) (h : Ev n) : ∃ k, n = 2 * k :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem not_ev_one : ¬ Ev 1 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem ev_minus_two (n : Nat) (h : Ev (n + 2)) : Ev n :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Rules are functions: `Ev.step n h : Ev (n + 2)`. Hypotheses `h : Ev n` can be inducted or inverted.
H2. `ev_double`: induction on `n`, rewriting `2 * (n + 1)` to `2 * n + 2`. `ev_exists`: `induction h`.
H3. `induction h with | zero => exact ⟨0, rfl⟩ | step m _ ih => obtain ⟨k, hk⟩ := ih; exact ⟨k + 1, by omega⟩`; inversions are `intro h; cases h` and `cases h with | step _ h' => exact h'`.
-/
