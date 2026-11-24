/- E012 | Absolute value | 2-3 min | if-then-else, split, unfold [R01]
GOAL
  Implement `myAbs` on `Int` and prove it returns a non-negative value equal to `x` or `-x`.

GUIDE
  Entries R1–R4: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · myAbs (definition body)
  1. (optional) Read off the value from `myAbs_spec`: `≥ 0` and `x` or `-x`
     forces `-x` for negative `x` and `x` otherwise
  2. Case split on the sign condition `x < 0`, one value per branch:         R1
  3. (optional) Check with `#eval myAbs (-3)` and `#eval myAbs 4`:            W1
-/
-- BEGIN SPEC
def myAbs (x : Int) : Int :=
-- END SPEC
  if x < 0 then -x else x

/- SKELETON · myAbs_spec
  1. Expose the body of `myAbs`, so the `if` appears in the goal:           R2
  2. One goal per branch; each gains `h✝ : x < 0` or `h✝ : ¬x < 0`:          R3
  3. In both goals: linear arithmetic with `∧`, `∨`, `-x`, closed using
     the branch hypothesis (combine 2 and 3 with `<;>`):                     R4
-/
-- BEGIN SPEC
theorem myAbs_spec (x : Int) : 0 ≤ myAbs x ∧ (myAbs x = x ∨ myAbs x = -x) :=
-- END SPEC
  by
    unfold myAbs
    split <;> omega

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The spec determines `myAbs` completely: think about the sign of `x`. `omega` cannot look inside
    `myAbs x`, so the proof has to expose the definition first.
H2. Define it with `if x < 0 then … else …` (R1). In the proof, unfold `myAbs` (R2), split on the `if`
    (R3), and finish each branch, where the sign of `x` is now a hypothesis, with `omega` (R4).
H3. Body: `if x < 0 then -x else x`. Proof: `unfold myAbs` then `split <;> omega`.
-/
