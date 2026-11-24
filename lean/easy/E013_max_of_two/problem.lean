/- E013 | Max of two | 2-3 min | by_cases [R02]
GOAL
  Implement `myMax` on `Int` and prove it is an upper bound equal to one of its arguments.

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · myMax
  1. One case distinction on a comparison of `a` and `b`; each branch returns
     one of the two arguments:                                              R1
-/
-- BEGIN SPEC
def myMax (a b : Int) : Int :=
-- END SPEC
  sorry

/- SKELETON · myMax_spec
  1. Split on the condition of the `if` in your `myMax`, written literally:  R2
  2. Focus each case with `·` (TACTIC_STATES). In each one: unfold `myMax`,
     pick the branch with `h`, drop the parts that became true, all in one
     `simp` call naming `myMax` and `h`:                     R3 → R4 or R5 → R6
  3. A case may leave a comparison that holds only because of `h`
     (with `if a ≤ b`: only `case neg`, from `h : ¬a ≤ b`; a case `simp`
     already closed needs nothing more). Close it with arithmetic:          R7
-/
-- BEGIN SPEC
theorem myMax_spec (a b : Int) :
    a ≤ myMax a b ∧ b ≤ myMax a b ∧ (myMax a b = a ∨ myMax a b = b) :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `myMax` with an `if` on `a ≤ b` (R1). The theorem then depends on which branch the `if`
    takes, so case on that condition (R2).
H2. `by_cases h : a ≤ b`. In each case `simp [myMax, h]` unfolds `myMax` and removes the `if` (R3–R5)
    and the conjuncts that became trivial (R6); what remains in `case neg` is linear (R7).
H3. `by_cases h : a ≤ b` then `· simp [myMax, h]` and `· simp [myMax, h]; omega`.
-/
