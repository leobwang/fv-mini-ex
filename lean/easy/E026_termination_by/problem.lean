/- E026 | termination_by | 3 min | termination_by, well-founded recursion, rw unfold
GOAL
  Define `halvings n` (how often `n` can be halved before it is ≤ 1) by well-founded recursion.

GUIDE
  Entries R1–R6: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · halvings (definition body)
  1. The theorems below fix the shape: `0` when `n ≤ 1`, otherwise one halving
     plus the halvings of `n / 2`: an `if` (E012), the recursive call in `else`.
  2. `n / 2` is not a pattern variable: state a measure on its own line after
     the body (Lean would try to guess one; write it explicitly):           R1
     Lean then proves `n / 2 < n` from the branch condition `¬n ≤ 1` itself:  R2
-/
-- BEGIN SPEC
def halvings (n : Nat) : Nat :=
-- END SPEC
  sorry

/- SKELETON · halvings_small
  1. Both equations are closed computations (numerals only): one `simp` with
     the name unfolds, decides each `if`, and splits the `∧`:                R3
     (`rfl` and `decide` fail on a well-founded definition)
-/
-- BEGIN SPEC
theorem halvings_small : halvings 0 = 0 ∧ halvings 1 = 0 :=
-- END SPEC
  sorry

/- SKELETON · halvings_step
  1. `n` is a variable, so `simp [halvings]` would unfold forever: unfold one
     step, the `halvings n` on the left only:                                R4
  2. Take the `else` branch; its condition `¬n ≤ 1` follows from `h`, proved
     in place as the lemma's argument:                                       R5 with R6
  3. Both sides are now identical: `rw` closes the goal itself (E009).
-/
-- BEGIN SPEC
theorem halvings_step (n : Nat) (h : 2 ≤ n) : halvings n = 1 + halvings (n / 2) :=
-- END SPEC
  sorry

/- SKELETON · halvings_eight
  1. A closed computation again: `simp` with the name repeats the unfolding
     8 → 4 → 2 → 1 and adds up the 1s:                                       R3
-/
-- BEGIN SPEC
theorem halvings_eight : halvings 8 = 3 :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The theorems describe an `if` on `n ≤ 1`: `0` below, one more than the recursive value at `n / 2`
    above. A well-founded definition does not compute by `rfl`/`decide`: prove things about it with
    `simp [halvings]` (numerals only) or `rw [halvings]` (one unfolding step).
H2. Body: the `if`, with `termination_by n` on the line after it. `halvings_small` and `halvings_eight`:
    `simp [halvings]`. `halvings_step`: unfold once with `rw`, then take the `else` branch with `if_neg`,
    proving `¬n ≤ 1` from `h` with `omega`.
H3. `if n ≤ 1 then 0 else 1 + halvings (n / 2)`, then `termination_by n`; `halvings_step`:
    `rw [halvings, if_neg (by omega)]`.
-/
