/- M038 | Constant folding | 15 min | inductive, evaluator, compiler optimisation, split
GOAL
  `fold` simplifies arithmetic expressions (adds constants, drops `+ 0`, `* 1`, `* 0`).
  Prove the optimisation preserves the meaning of every expression in every environment.

GUIDE
  Entries R1–R6: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M038

-- BEGIN SPEC
inductive Expr where
  | num (n : Nat)
  | var (i : Nat)
  | plus (a b : Expr)
  | times (a b : Expr)

def eval (env : Nat → Nat) : Expr → Nat
  | .num n => n
  | .var i => env i
  | .plus a b => eval env a + eval env b
  | .times a b => eval env a * eval env b

def mkPlus : Expr → Expr → Expr
  | .num a, .num b => .num (a + b)
  | .num 0, e => e
  | e, .num 0 => e
  | a, b => .plus a b

def mkTimes : Expr → Expr → Expr
  | .num a, .num b => .num (a * b)
  | .num 0, _ => .num 0
  | _, .num 0 => .num 0
  | .num 1, e => e
  | e, .num 1 => e
  | a, b => .times a b

def fold : Expr → Expr
  | .plus a b => mkPlus (fold a) (fold b)
  | .times a b => mkTimes (fold a) (fold b)
  | e => e
-- END SPEC

/- SKELETON · fold_correct
  0. MILESTONES first: state and prove two helpers above this theorem, outside the spec.
       eval_mkPlus  (env : Nat → Nat) (a b : Expr) : eval env (mkPlus a b)  = eval env a + eval env b
       eval_mkTimes (env : Nat → Nat) (a b : Expr) : eval env (mkTimes a b) = eval env a * eval env b
     For each:
       open the smart constructor's `match`:                                   R1
       one goal per arm (4 for mkPlus, 6 for mkTimes):                          R2
       on every arm (`<;>`): compute `eval`, simplify `0 + x`, `x * 1`, …:     R3
  1. Induct on `e`, naming the IHs of `plus` and `times`:                       R4
  2. num n, var i: `fold` leaves them alone, both sides compute alike:         R5
  3. plus a b: one `simp` with `fold`'s equation, then eval_mkPlus, then
     `eval`, then iha, ihb:                                                     R6
  4. times a b: the same with eval_mkTimes:                                     R6
-/
-- BEGIN SPEC
theorem fold_correct (env : Nat → Nat) (e : Expr) : eval env (fold e) = eval env e :=
-- END SPEC
  sorry

/- SKELETON · fold_example
  1. A closed term: both sides compute to the same `Expr`:                      R5
     (`decide` does not apply: `Expr` has no `DecidableEq`.)
-/
-- BEGIN SPEC
theorem fold_example : fold (.plus (.times (.num 1) (.var 0)) (.plus (.num 2) (.num 3))) =
    .plus (.var 0) (.num 5) :=
-- END SPEC
  sorry

end M038

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `fold` does all its work through `mkPlus`/`mkTimes`: first prove that each smart constructor keeps
    `eval` on its own (milestones), then `fold_correct` by induction on `e`. `fold_example` is a
    closed computation.
H2. Milestone: `unfold` the smart constructor to expose its `match` (R1), `split` it into one goal per
    arm (R2), and close every arm by computing `eval` (R3). Main theorem: `induction e with` (R4);
    `num`/`var` by `rfl` (R5); `plus`/`times` by `simp` with `fold`, the milestone, `eval` and the IHs (R6).
H3. `theorem eval_mkPlus (env : Nat → Nat) (a b : Expr) : eval env (mkPlus a b) = eval env a + eval env b := by
      unfold mkPlus; split <;> simp_all [eval]`
    and in `fold_correct`: `| plus a b iha ihb => simp [fold, eval_mkPlus, eval, iha, ihb]`.
-/
