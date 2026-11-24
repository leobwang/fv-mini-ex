/- E002 | Factorial by pattern matching | 2-3 min | def, match, structural recursion
GOAL
  Define `fact` by structural recursion so that the three theorems hold, then prove them.

GUIDE
  Entries R1–R5: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · fact (definition body)
  1. Case on the shape of `n`, two arms `0` and `k + 1`; `fact_zero` gives the
     `0` arm's value, `fact_succ` (read with `n := k`) the other one:               R1
  2. In the `k + 1` arm, call `fact` on `k`; write the value in exactly the
     form of `fact_succ`'s right side, parentheses included:                       R2
-/
-- BEGIN SPEC
def fact (n : Nat) : Nat :=
-- END SPEC
  match n with
  | 0 => 1
  | k + 1 => (k + 1) * fact k

/- SKELETON · fact_zero
  1. `fact 0` unfolds to the `0` arm: proof by computation:                         R3
-/
-- BEGIN SPEC
theorem fact_zero : fact 0 = 1 :=
-- END SPEC
  rfl

/- SKELETON · fact_succ
  1. `n + 1` fits the pattern `k + 1`, so `fact (n + 1)` unfolds one step to the
     second arm's value; it must match the right side as written:                  R4
-/
-- BEGIN SPEC
theorem fact_succ (n : Nat) : fact (n + 1) = (n + 1) * fact n :=
-- END SPEC
  rfl

/- SKELETON · fact_five
  1. (optional) `#eval fact 5` should print `120`
  2. A numeral argument: everything computes:                                       R5
-/
-- BEGIN SPEC
theorem fact_five : fact 5 = 120 :=
-- END SPEC
  rfl

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `fact_zero` and `fact_succ` are the two arms of the definition, read off: one arm for `0`, one for a
    successor (R1). Once `fact` is defined that way, all three theorems hold by computation.
H2. `match n with` with arms `0` and `k + 1`; in the second arm recurse on `k` (R2), writing the value in the
    same order as the right side of `fact_succ`. Then `rfl` for each theorem (R3, R4, R5).
H3. `match n with | 0 => 1 | k + 1 => (k + 1) * fact k`, and `rfl` for all three theorems.
-/
