/- E032 | Option-returning functions | 3 min | Option, if-then-else, match
GOAL
  Implement two partial functions returning `Option`, specified by their behaviour.

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · safeDiv (definition body)
  1. Fail exactly when dividing by zero (safeDiv_spec): an `if` on `b = 0` whose
     branches are both `Option Nat`, `none` and the result wrapped in `some`:        R1
-/
-- BEGIN SPEC
def safeDiv (a b : Nat) : Option Nat :=
-- END SPEC
  sorry

/- SKELETON · second (definition body)
  1. No named argument: the body is a function, by pattern matching on the list:     R2
  2. Arms, top to bottom: lists with at least two elements give their second
     element; a catch-all arm, LAST, gives `none` (covers `[]` and `[a]`):          R2
-/
-- BEGIN SPEC
def second : List Nat → Option Nat :=
-- END SPEC
  sorry

/- SKELETON · safeDiv_spec
  1. Split the `∧`:                                                                  R3
  2. First half: assume `b = 0`, unfold `safeDiv` and take the `then` branch:        R4 → R5
  3. Second half: assume `b ≠ 0`, unfold `safeDiv` and take the `else` branch:       R4 → R6
     (in 2 and 3 one `simp` with the name and the assumption does the unfold too)
-/
-- BEGIN SPEC
theorem safeDiv_spec (a b : Nat) : (b = 0 → safeDiv a b = none) ∧ (b ≠ 0 → safeDiv a b = some (a / b)) :=
-- END SPEC
  sorry

/- SKELETON · safeDiv_bound
  1. Case on `b = 0`:                                                                R7
  2. `case pos`: unfold `safeDiv` and decide the `if` INSIDE `h`; `h` becomes
     `none = some q`, which closes the goal:                                         R5 + R8 (at h)
  3. `case neg`: the same `simp … at h` leaves `h : a / b = q`:                      R6 + R9 (at h)
     put `a / b` back in place of `q`, then the library bound:                      R10 → R11
-/
-- BEGIN SPEC
theorem safeDiv_bound (a b q : Nat) (h : safeDiv a b = some q) : q * b ≤ a :=
-- END SPEC
  sorry

/- SKELETON · second_spec
  1. Three equations at once, one anonymous constructor:                             R12
  2. Each holds by computation: the list's shape picks the arm of `second`:          R13
-/
-- BEGIN SPEC
theorem second_spec (a b : Nat) (rest : List Nat) :
    second [] = none ∧ second [a] = none ∧ second (a :: b :: rest) = some b :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `safeDiv` fails exactly when dividing by zero; `second` needs at least two elements. The
    theorems then follow by unfolding the definitions and deciding the `if` (or the match).
H2. `safeDiv_spec`: split the `∧`, `intro` each premise, and `simp [safeDiv, h]` (R3, R4, R5/R6).
    `safeDiv_bound`: `by_cases hb : b = 0`, then `simp [safeDiv, hb] at h` in each case; the first case
    closes, the second leaves `h : a / b = q` (R7, R8, R9). `second_spec`: every part is `rfl` (R12, R13).
H3. `if b = 0 then none else some (a / b)`; `second` is `fun | _ :: y :: _ => some y | _ => none`;
    `safeDiv_bound` ends with `rw [← h]; exact Nat.div_mul_le_self a b`.
-/
