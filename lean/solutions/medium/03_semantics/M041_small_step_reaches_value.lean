/- M041 | Small-step arithmetic reaches its value | 15-20 min | multi-step closure, congruence lemmas, Star, evaluator agreement
GOAL
  Relate M040's small-step semantics to the evaluator `eval`: a step preserves `eval`, every
  expression reduces in many steps to the numeral of its value, and that is the only numeral it reaches.

REFERENCE
  -- `Star e e'` : `e` reduces to `e'` in zero or more steps (`refl`, or one `Step` then a `Star`)
  example : M041.Star (.plus (.num 1) (.num 2)) (.num 3) := .step .plusNum (.refl _)
  -- Facts about a `Star` proof `h` go by induction on it:
  --   induction h with
  --   | refl e => ...
  --   | step s _ ih => ...     -- s : Step a b, ih : the claim for the remaining `Star b c`
  -- Helpers you will want (state and prove them yourself, outside the spec):
  --   transitivity of `Star`, and congruence: `Star a a' → Star (.plus a b) (.plus a' b)`, …
  -- `refine star_trans ?_ ?_` applies a lemma and leaves each `?_` as a new goal.
BANNED: try?, grind
NOTE: `grind` is banned so that `try?`'s printed one-liner for `step_eval` does not count; use `simp`.
  Do not leave search tactics (`exact?`, `apply?`) in the file.
-/

namespace M041

-- BEGIN SPEC
inductive Expr where
  | num (n : Nat)
  | plus (a b : Expr)
  | times (a b : Expr)

def eval : Expr → Nat
  | .num n => n
  | .plus a b => eval a + eval b
  | .times a b => eval a * eval b

/-- Left-to-right small-step reduction (as in M040). -/
inductive Step : Expr → Expr → Prop
  | plusNum {m n : Nat} : Step (.plus (.num m) (.num n)) (.num (m + n))
  | timesNum {m n : Nat} : Step (.times (.num m) (.num n)) (.num (m * n))
  | plusL {a a' b : Expr} : Step a a' → Step (.plus a b) (.plus a' b)
  | plusR {m : Nat} {b b' : Expr} : Step b b' → Step (.plus (.num m) b) (.plus (.num m) b')
  | timesL {a a' b : Expr} : Step a a' → Step (.times a b) (.times a' b)
  | timesR {m : Nat} {b b' : Expr} : Step b b' → Step (.times (.num m) b) (.times (.num m) b')

/-- Reflexive-transitive closure of `Step`. -/
inductive Star : Expr → Expr → Prop
  | refl (e : Expr) : Star e e
  | step {a b c : Expr} : Step a b → Star b c → Star a c
-- END SPEC

-- BEGIN SPEC
theorem step_eval {e e' : Expr} (h : Step e e') : eval e' = eval e :=
-- END SPEC
  by induction h <;> simp_all [eval]

theorem star_trans {a b c : Expr} (h1 : Star a b) (h2 : Star b c) : Star a c := by
  induction h1 with
  | refl => exact h2
  | step s _ ih => exact .step s (ih h2)

/-- Congruence: any context `f` that lifts single steps lifts `Star`. -/
theorem star_map (f : Expr → Expr) (hf : ∀ {a b}, Step a b → Step (f a) (f b)) {a b : Expr}
    (h : Star a b) : Star (f a) (f b) := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (hf s) ih

theorem star_eval {e e' : Expr} (h : Star e e') : eval e' = eval e := by
  induction h with
  | refl => rfl
  | step s _ ih => rw [ih, step_eval s]

-- BEGIN SPEC
theorem reaches_value (e : Expr) : Star e (.num (eval e)) :=
-- END SPEC
  by
    induction e with
    | num n => exact .refl _
    | plus a b iha ihb =>
      -- WHY: left operand first, because `plusR` needs a numeral on the left
      refine star_trans (star_map (fun x => .plus x b) .plusL iha) ?_
      refine star_trans (star_map (fun x => .plus (.num (eval a)) x) .plusR ihb) ?_
      exact .step .plusNum (.refl _)
    | times a b iha ihb =>
      refine star_trans (star_map (fun x => .times x b) .timesL iha) ?_
      refine star_trans (star_map (fun x => .times (.num (eval a)) x) .timesR ihb) ?_
      exact .step .timesNum (.refl _)

-- BEGIN SPEC
theorem star_value {e : Expr} {n : Nat} (h : Star e (.num n)) : n = eval e :=
-- END SPEC
  star_eval h

end M041

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `step_eval`: induction on the step. `reaches_value`: induction on `e`; for `plus a b`, chain
    three stretches: `a` down to `.num (eval a)`, then `b` down to `.num (eval b)`, then `plusNum`.
H2. `plusR` only fires once the left operand is a numeral, so the order of the stretches matters.
    `star_value`: the target `.num n` is not a variable, so first prove `Star e e' → eval e' = eval e`
    by induction on the `Star`, then specialise it (`eval (.num n)` is `n` by `rfl`).
H3. One lemma gives all four congruences:
    `theorem star_map (f : Expr → Expr) (hf : ∀ {a b}, Step a b → Step (f a) (f b)) {a b : Expr} (h : Star a b) : Star (f a) (f b)`,
    used as `star_map (fun x => .plus x b) .plusL iha`.
-/
