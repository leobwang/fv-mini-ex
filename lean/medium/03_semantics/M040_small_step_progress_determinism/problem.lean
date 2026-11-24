/- M040 | Small-step arithmetic: progress and determinism | 10-15 min | small-step semantics, inductive relation, cases inversion, induction on derivations
GOAL
  For a left-to-right small-step semantics of arithmetic expressions, prove that numerals cannot
  step, that every non-numeral can step (progress), and that stepping is deterministic.

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M040

-- BEGIN SPEC
inductive Expr where
  | num (n : Nat)
  | plus (a b : Expr)
  | times (a b : Expr)

/-- Left-to-right small-step reduction: reduce the left operand to a numeral first, then the
right one, then combine two numerals. -/
inductive Step : Expr → Expr → Prop
  | plusNum {m n : Nat} : Step (.plus (.num m) (.num n)) (.num (m + n))
  | timesNum {m n : Nat} : Step (.times (.num m) (.num n)) (.num (m * n))
  | plusL {a a' b : Expr} : Step a a' → Step (.plus a b) (.plus a' b)
  | plusR {m : Nat} {b b' : Expr} : Step b b' → Step (.plus (.num m) b) (.plus (.num m) b')
  | timesL {a a' b : Expr} : Step a a' → Step (.times a b) (.times a' b)
  | timesR {m : Nat} {b b' : Expr} : Step b b' → Step (.times (.num m) b) (.times (.num m) b')
-- END SPEC

/- SKELETON · num_stuck   (used in step_det, step 3)
  1. Move the step into the context; the goal becomes `False`:                         R1
  2. Invert it: no rule of `Step` has a numeral on the left, so no case is left:       R2
-/
-- BEGIN SPEC
theorem num_stuck (n : Nat) (e : Expr) : ¬ Step (.num n) e :=
-- END SPEC
  sorry

/- SKELETON · progress
  1. Induction on the syntax `e`, naming arguments and IHs; goals num, plus, times:    R3
  2. num: the left side, witness `n`:                                                   R4
  3. plus: go right, split the IH of `a` (substituting `a := .num m`):                  R5, R6
       1st goal, `a` a numeral: split the IH of `b`:                                    R6
         `b` a numeral           → `Step.plusNum`                                       R7
         `b` steps               → `Step.plusR`                                         R8
       2nd goal, `a` steps       → `Step.plusL`                                         R8
  4. times: the same with `timesL`, `timesR`, `timesNum`.
-/
-- BEGIN SPEC
theorem progress (e : Expr) : (∃ n, e = .num n) ∨ ∃ e', Step e e' :=
-- END SPEC
  sorry

/- SKELETON · step_det
  Prove num_stuck first; step 3 uses it.
  1. Induction on `h1`, keeping `e2` general; six goals, one per rule (alternatives
     with the same shape may share one `=> tac`):                                       R9
  2. In each goal invert `h2`: one goal per rule pair:                                  R10
  3. Different rules: one side is a step out of a numeral; same computation rule:
     `x = x`. Both closed by `simp_all [num_stuck]`:                                    R11
  4. Same congruence rule: `simp_all` leaves `a' = a''`; close it with the IH:          R12, R13
-/
-- BEGIN SPEC
theorem step_det {e e1 e2 : Expr} (h1 : Step e e1) (h2 : Step e e2) : e1 = e2 :=
-- END SPEC
  sorry

end M040

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `num_stuck`: introduce the step and invert it (R1, R2). `progress`: induction on `e`; in the
    `plus a b` case split the IH of `a` first (if `a` steps, use `plusL`), then the IH of `b`
    (`plusR` if it steps, `plusNum` if both are numerals).
H2. `step_det`: induct on `h1` generalizing `e2`, and invert `h2` in each case. Mismatched rule
    pairs contain a step out of a numeral (kill it with `num_stuck`); matching congruence pairs
    reduce to an equation of the subterms that the IH proves.
H3. `progress`, plus: `right; rcases iha with ⟨m, rfl⟩ | ⟨a', ha⟩`, then `exact ⟨_, .plusL ha⟩`
    etc. `step_det`: `induction h1 generalizing e2 with | plusNum | timesNum => … | plusL _ ih | … =>`,
    each `cases h2 <;> simp_all [num_stuck]`, and in the congruence cases `exact ih ‹_›`.
-/
