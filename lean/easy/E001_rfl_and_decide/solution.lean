/- E001 | rfl, decide, #eval | 1-3 min | rfl, decide, #eval, def
GOAL
  Define `double` and prove three small facts about concrete values.
  Replace every `sorry` with a proof (or, in the `def`, an expression of type `Nat`).

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · double
  1. Write the body: an expression of type `Nat` in the parameter `n`
     that is twice `n` (operators `+`, `*` on `Nat`):                       R1
  2. Optional: test it on a few inputs before proving anything:            R2
-/
-- BEGIN SPEC
def double (n : Nat) : Nat :=
-- END SPEC
  2 * n

/- SKELETON · double_three
  1. Both sides are concrete: `double 3` unfolds to your body with `n := 3`
     and evaluates to a numeral. Check it is `6` (R2), then close the
     equation by computation, as a term or inside `by`:                    R3, R4 (or R5)
-/
-- BEGIN SPEC
theorem double_three : double 3 = 6 :=
-- END SPEC
  rfl

/- SKELETON · small_lt
  1. An inequality, so not `rfl`. Concrete numbers only: let Lean evaluate
     the statement inside `by`:                                            R5, R6
-/
-- BEGIN SPEC
theorem small_lt : 2 ^ 5 < 50 :=
-- END SPEC
  by decide

/- SKELETON · bool_fact
  1. Evaluate the `Bool` expression on the left (`!false` first, then `&&`):  R7
  2. It computes to `true`, so the equation closes by computation:          R4 (or R6)
-/
-- BEGIN SPEC
theorem bool_fact : (true && !false) = true :=
-- END SPEC
  rfl

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every statement here is about concrete values, so Lean can settle it by computing. Test `double`
    with `#eval double 3` (R2) before proving anything about it.
H2. Equations between values that compute to the same thing: `rfl` (R4). An inequality between
    concrete numbers: `by decide` (R6). The `Bool` equation is an equation: `rfl` (or `decide`).
H3. `def double (n : Nat) : Nat := 2 * n` (or `n + n`); then `double_three` is `rfl`, `small_lt` is
    `by decide` (`2 ^ 5` is `32`), and `bool_fact` is `rfl` (`true && !false` evaluates to `true`).
-/
