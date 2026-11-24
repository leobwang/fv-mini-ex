/- M039 | Except evaluator | 15 min | Except, do notation, throw, monadic code
GOAL
  `eval` runs in the `Except String` monad and fails on division by zero. Prove it never fails
  on division-free expressions, and always fails when dividing by the literal 0.

GUIDE
  Entries R1–R14: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M039

-- BEGIN SPEC
inductive Expr where
  | num (n : Int)
  | add (a b : Expr)
  | div (a b : Expr)

def eval : Expr → Except String Int
  | .num n => pure n
  | .add a b => do
    let x ← eval a
    let y ← eval b
    pure (x + y)
  | .div a b => do
    let x ← eval a
    let y ← eval b
    if y = 0 then throw "division by zero" else pure (x / y)

def NoDiv : Expr → Prop
  | .num _ => True
  | .add a b => NoDiv a ∧ NoDiv b
  | .div _ _ => False

def evalPure : Expr → Int
  | .num n => n
  | .add a b => evalPure a + evalPure b
  | .div a b => evalPure a / evalPure b
-- END SPEC

@[simp] theorem ok_bind {α β : Type} (x : α) (f : α → Except String β) :
    (Except.ok x >>= f) = f x := rfl
@[simp] theorem error_bind {α β : Type} (e : String) (f : α → Except String β) :
    (Except.error e >>= f) = Except.error e := rfl
@[simp] theorem map_ok {α β : Type} (x : α) (f : α → β) :
    (f <$> (Except.ok x : Except String α)) = Except.ok (f x) := rfl
@[simp] theorem map_error {α β : Type} (e : String) (f : α → β) :
    (f <$> (Except.error e : Except String α)) = Except.error e := rfl

/- SKELETON · eval_noDiv
  1. Induct on `e`; `h : NoDiv e` comes along, so each IH is `NoDiv a → eval a = …`:      R1
  2. num: both sides compute to `Except.ok n` (`pure n` is `.ok n`):                        R2
  3. add: split `h` into `ha : NoDiv a`, `hb : NoDiv b`:                                    R3
     then one `simp` with `eval`, `iha ha`, `ihb hb`, `evalPure`. It unfolds `eval`,
     rewrites both sub-evaluations, turns the inner `let y ← .ok _; pure (x + y)` into a
     map and computes it, runs the outer `let x ← .ok _`, then unfolds `evalPure`:
                                                                    R4 → R5 → R7 → R8 → R6 → R4
  4. div: `h : NoDiv (.div a b)` is `False` by definition:                                 R9
  Model: guide R1–R9 on `Tm`, `run`, `Clean`.
-/
-- BEGIN SPEC
theorem eval_noDiv (e : Expr) (h : NoDiv e) : eval e = .ok (evalPure e) :=
-- END SPEC
  sorry

/- SKELETON · div_zero_fails
  1. Split on the result of `eval a`, keeping the equation `h`:                             R10
  2. error e: the witness is `e`; prove the equation with `simp [eval, h]`. It unfolds
     `eval`, runs `let y ← pure 0`, decides `0 = 0`, rewrites `eval a` with `h`, and the
     error skips the rest:                                       R11, R4 → R12 → R13 → rw [h] → R14
  3. ok x: the witness is `"division by zero"`; the same `simp [eval, h]` runs
     `let x ← .ok x` instead (R6) and stops at `throw "…" = Except.error "…"`,
     which holds by definition:                                  R11, R4 → R12 → R13 → rw [h] → R6, then R2
  Model: guide W3 (the same split on `run`).
-/
-- BEGIN SPEC
theorem div_zero_fails (a : Expr) : ∃ msg, eval (.div a (.num 0)) = .error msg :=
-- END SPEC
  sorry

end M039

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `eval_noDiv`: induction on `e` (R1); `h` mentions `e`, so each IH needs `NoDiv a` first. The `div`
    case is impossible because `NoDiv (.div a b)` is `False` (R9). `div_zero_fails`: you cannot compute
    `eval a`, so split on its result and remember which one it was (R10).
H2. `add` case: split `h` (R3), then one `simp` with `eval`, the IHs applied to `ha`, `hb` (R5), and
    `evalPure`; `simp` runs the `do` block by itself with `bind_pure_comp` and the given `map_ok`,
    `ok_bind` (R7, R8, R6). `div_zero_fails`: in each case give the witness (R11): the error `e` of
    `eval a`, or `"division by zero"`, and prove it with `simp [eval, h]`; in the `ok` case `simp`
    leaves `throw … = Except.error …`, which `rfl` closes (R2).
H3. `add`: `obtain ⟨ha, hb⟩ := h; simp [eval, iha ha, ihb hb, evalPure]`; `div`: `exact absurd h id`.
    `div_zero_fails`: `cases h : eval a with | error e => exact ⟨e, by simp [eval, h]⟩
    | ok x => exact ⟨"division by zero", by simp [eval, h]; rfl⟩`.
-/
