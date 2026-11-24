/- M041 | Small-step arithmetic reaches its value | 15-20 min | multi-step closure, congruence lemmas, Star, evaluator agreement
GOAL
  Relate M040's small-step semantics to the evaluator `eval`: a step preserves `eval`, every
  expression reduces in many steps to the numeral of its value, and that is the only numeral it reaches.
BANNED: try?, grind

GUIDE
  Entries R1–R10: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · step_eval
  1. Induct on the step `h`: six goals, one per rule (`plusNum` … `timesR`):    R1
       e.g. plusL:  a_ih✝ : eval a'✝ = eval a✝¹ ⊢ eval (a'✝.plus b✝) = eval (a✝¹.plus b✝)
  2. On every goal (`<;>`): unfold `eval` on both sides and rewrite with the
     IH `a_ih✝` where there is one:                                            R2
-/
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

/- SKELETON · reaches_value
  0. MILESTONES first: state and prove two helpers above this theorem, outside the spec.
       star_trans : Star a b → Star b c → Star a c
         induct on the FIRST run, the second stays in the context:            R4 (R3)
         refl: the second run itself; step: one step, then the IH on it:      R5
       star_map (f : Expr → Expr) (hf : ∀ {a b}, Step a b → Step (f a) (f b)) :
           Star a b → Star (f a) (f b)
         induct on the run:                                                     R3
         refl: R5 (`.refl _`); step: R5 with `hf s` and the IH
  1. Induct on `e`:                                                             R8
  2. num n: `.num (eval (.num n))` is `.num n`, a run of zero steps:            R7, R5
  3. plus a b: glue three stretches with star_trans, left operand first:       R9
       a → num (eval a) inside `.plus · b`: star_map with the rule `plusL`
         and the IH `iha`:                                                      R10
       b → num (eval b) inside `.plus (.num (eval a)) ·`: star_map with `plusR`
         and `ihb` (glue with R9 again):                                        R9, R10
       the final `plusNum` step, then zero steps; its end `.num (eval a + eval b)`
         is `.num (eval (a.plus b))` by unfolding, no rewrite needed:          R5, R7
  4. times a b: as step 3 with `timesL`, `timesR`, `timesNum`.
-/
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

/- SKELETON · star_value
  0. MILESTONE first: `induction h` fails here (the end `.num n` is not a variable),
     so prove the claim for EVERY end e' as a helper, outside the spec:
       star_eval : Star e e' → eval e' = eval e
         induct on the run:                                                     R3
         refl: `eval e = eval e`:                                               R7 (rfl)
         step s _ ih: rewrite with `ih`, then with `step_eval s`:               R6
  1. Apply star_eval to `h`: its type `eval (.num n) = eval e` unfolds to the
     goal `n = eval e`:                                                         R7
-/
-- BEGIN SPEC
theorem star_value {e : Expr} {n : Nat} (h : Star e (.num n)) : n = eval e :=
-- END SPEC
  star_eval h

end M041

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `step_eval`: induct on the step (R1) and compute (R2). `reaches_value`: induct on `e` (R8); for
    `plus a b` chain three stretches: `a` down to `.num (eval a)`, then `b` down to `.num (eval b)`,
    then `plusNum`. `star_value`: a fact about all runs ending anywhere, then specialised.
H2. Prove two helpers first: transitivity of `Star` (induction on the first run, R4) and congruence
    through a context `f` (R3, R10). `plusR` only fires once the left operand is a numeral, so run the
    left operand first. `star_value`: `induction h` fails on the end `.num n`; prove
    `Star e e' → eval e' = eval e` by induction on the `Star` (R3, R6), then apply it (R7).
H3. `step_eval`: `induction h <;> simp_all [eval]`. One lemma gives all four congruences:
    `theorem star_map (f : Expr → Expr) (hf : ∀ {a b}, Step a b → Step (f a) (f b)) {a b : Expr} (h : Star a b) : Star (f a) (f b)`,
    used as `refine star_trans (star_map (fun x => .plus x b) .plusL iha) ?_` (R9, R10).
-/
