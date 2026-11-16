/- E013 | Max of two | 2-3 min | by_cases [R02]
GOAL
  Implement `myMax` on `Int` and prove it is an upper bound equal to one of its arguments.

REFERENCE
  example (n : Nat) : n = 0 ∨ n ≠ 0 := by
    by_cases h : n = 0         -- two goals: one with h : n = 0, one with h : ¬n = 0
    · exact Or.inl h
    · exact Or.inr h
  def pick (b : Bool) (x y : Int) : Int := if b then x else y
  example (x y : Int) : pick true x y = x := by simp [pick]   -- simp decides `if true`
  `simp [f, h]` reduces `if c then .. else ..` when `h : c` or `h : ¬c` is given.
-/

-- BEGIN SPEC
def myMax (a b : Int) : Int :=
-- END SPEC
  if a ≤ b then b else a

-- BEGIN SPEC
theorem myMax_spec (a b : Int) :
    a ≤ myMax a b ∧ b ≤ myMax a b ∧ (myMax a b = a ∨ myMax a b = b) :=
-- END SPEC
  by
    by_cases h : a ≤ b
    · simp [myMax, h]
    · simp [myMax, h]
      omega

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `myMax` with an `if`, then case on the condition of that `if`.
H2. `by_cases h : a ≤ b`; in each branch `simp [myMax, h]` removes the `if`.
H3. `by_cases h : a ≤ b` then `· simp [myMax, h]` and `· simp [myMax, h]; omega`.
-/
