/- E12 | Absolute value | 2-3 min | if-then-else, split, unfold [R01]
GOAL
  Implement `myAbs` on `Int` and prove it returns a non-negative value equal to `x` or `-x`.

REFERENCE
  def clamp (x : Int) : Int := if x < 0 then 0 else x   -- `if c then a else b` (c decidable)
  example (x : Int) : clamp x ≥ 0 := by unfold clamp; split <;> omega
    -- `unfold f` exposes the body; `split` makes one goal per branch of the `if`,
    -- adding `h : c` or `h : ¬c` to the context
  example (x : Int) (h : 0 ≤ x) : clamp x = x := by simp [clamp]; omega
-/

-- BEGIN SPEC
def myAbs (x : Int) : Int :=
-- END SPEC
  if x < 0 then -x else x

-- BEGIN SPEC
theorem myAbs_spec (x : Int) : 0 ≤ myAbs x ∧ (myAbs x = x ∨ myAbs x = -x) :=
-- END SPEC
  by
    unfold myAbs
    split <;> omega

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The spec determines `myAbs` completely: think about the sign of `x`.
H2. Write it with `if x < 0 then ... else ...`, then unfold and split on the `if`.
H3. `unfold myAbs` then `split <;> omega`.
-/
