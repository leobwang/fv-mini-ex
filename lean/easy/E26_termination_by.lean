/- E26 | termination_by | 3 min | termination_by, well-founded recursion, rw unfold
GOAL
  Define `halvings n` (how often `n` can be halved before it is ≤ 1) by well-founded recursion.

REFERENCE
  def cd (n : Nat) : List Nat := if n = 0 then [] else n :: cd (n - 1) termination_by n
    -- `n - 1` is not a structural subterm, so give a measure; Lean proves it decreases
  example : cd 2 = [2, 1] := by simp [cd]     -- simp unfolds the equation on literals
  example (n : Nat) (h : n ≠ 0) : cd n = n :: cd (n - 1) := by rw [cd, if_neg h]
    -- `rw [f]` unfolds one step; `if_pos h` / `if_neg h` pick a branch
  Well-founded definitions do not reduce by `rfl`/`decide`; use `rw`/`simp` with the name.
-/

-- BEGIN SPEC
def halvings (n : Nat) : Nat :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem halvings_small : halvings 0 = 0 ∧ halvings 1 = 0 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem halvings_step (n : Nat) (h : 2 ≤ n) : halvings n = 1 + halvings (n / 2) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem halvings_eight : halvings 8 = 3 :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The two spec theorems describe the base cases and the recursive case: an `if` on `n ≤ 1`.
H2. Recurse on `n / 2` and add `termination_by n` after the body.
H3. `if n ≤ 1 then 0 else 1 + halvings (n / 2)` + `termination_by n`; then `simp [halvings]` and `rw [halvings, if_neg (by omega)]`.
-/
