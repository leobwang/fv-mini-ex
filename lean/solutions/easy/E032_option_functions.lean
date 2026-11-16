/- E032 | Option-returning functions | 3 min | Option, if-then-else, match
GOAL
  Implement two partial functions returning `Option`, specified by their behaviour.

REFERENCE
  def safePred (n : Nat) : Option Nat := if n = 0 then none else some (n - 1)
  example : safePred 0 = none := by simp [safePred]
  example (n : Nat) (h : n ≠ 0) : safePred n = some (n - 1) := by simp [safePred, h]
  def first? : List Nat → Option Nat | [] => none | x :: _ => some x
  #check Nat.div_mul_le_self   -- (m n : Nat) : m / n * n ≤ m
  From `h : some a = some b`, `simp at h` gives `a = b`; `none = some _` simplifies to False.
-/

-- BEGIN SPEC
def safeDiv (a b : Nat) : Option Nat :=
-- END SPEC
  if b = 0 then none else some (a / b)

-- BEGIN SPEC
def second : List Nat → Option Nat :=
-- END SPEC
  fun
  | _ :: y :: _ => some y
  | _ => none

-- BEGIN SPEC
theorem safeDiv_spec (a b : Nat) : (b = 0 → safeDiv a b = none) ∧ (b ≠ 0 → safeDiv a b = some (a / b)) :=
-- END SPEC
  by
    constructor
    · intro h; simp [safeDiv, h]
    · intro h; simp [safeDiv, h]

-- BEGIN SPEC
theorem safeDiv_bound (a b q : Nat) (h : safeDiv a b = some q) : q * b ≤ a :=
-- END SPEC
  by
    by_cases hb : b = 0
    · simp [safeDiv, hb] at h
    · simp [safeDiv, hb] at h
      rw [← h]
      exact Nat.div_mul_le_self a b

-- BEGIN SPEC
theorem second_spec (a b : Nat) (rest : List Nat) :
    second [] = none ∧ second [a] = none ∧ second (a :: b :: rest) = some b :=
-- END SPEC
  ⟨rfl, rfl, rfl⟩

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `safeDiv` fails exactly when dividing by zero; `second` needs at least two elements.
H2. For `safeDiv_bound`, case on `b = 0`; in each case simplify `h` with `simp [safeDiv, hb] at h`.
H3. `if b = 0 then none else some (a / b)`; `second` by `fun | _ :: y :: _ => some y | _ => none`; finish with `Nat.div_mul_le_self`.
-/
