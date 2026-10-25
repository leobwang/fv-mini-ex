/- M15 | Constant folding | 15 min | inductive, evaluator, compiler optimisation, split
GOAL
  `fold` simplifies arithmetic expressions (adds constants, drops `+ 0`, `* 1`, `* 0`).
  Prove the optimisation preserves the meaning of every expression in every environment.

REFERENCE
  -- Prove one lemma per smart constructor, then the main theorem by induction on `e`.
  example (a b : Nat) : (match a, b with | 0, y => y | x, y => x + y) = a + b := by
    split <;> omega       -- `split` handles a `match` in the goal (one goal per arm)
  -- after `unfold mkPlus` + `split`, hypotheses like `h : a = .num 0` appear; `simp_all [eval]`
  -- substitutes them and evaluates.
-/

namespace M15

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

-- BEGIN SPEC
theorem fold_correct (env : Nat → Nat) (e : Expr) : eval env (fold e) = eval env e :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem fold_example : fold (.plus (.times (.num 1) (.var 0)) (.plus (.num 2) (.num 3))) =
    .plus (.var 0) (.num 5) :=
-- END SPEC
  sorry

end M15

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `fold` is built from `mkPlus`/`mkTimes`; each smart constructor must preserve `eval` on its own.
H2. Prove `eval env (mkPlus a b) = eval env a + eval env b` (and the `mkTimes` analogue) by `unfold` + `split`.
H3. `unfold mkPlus; split <;> simp_all [eval]`; main theorem: `induction e` with `simp [fold, eval_mkPlus, eval, iha, ihb]`.
-/
