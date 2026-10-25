/- M19 | Except evaluator | 15 min | Except, do notation, throw, monadic code
GOAL
  `eval` runs in the `Except String` monad and fails on division by zero. Prove it never fails
  on division-free expressions, and always fails when dividing by the literal 0.

REFERENCE
  def halve (n : Int) : Except String Int := if n % 2 = 0 then pure (n / 2) else throw "odd"
  example : halve 4 = .ok 2 := rfl         -- `pure` is `.ok`, `throw e` is `.error e`
  def quarter (n : Int) : Except String Int := do let m ← halve n; halve m   -- `←` binds
  example : quarter 6 = .error "odd" := rfl  -- an error short-circuits the rest
  -- The simp lemmas below (given) compute `>>=` and `<$>` on `.ok` / `.error`.
  -- `cases h : eval a with | ok x => .. | error e => ..` splits on a sub-result.
-/

namespace M19

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

-- BEGIN SPEC
theorem eval_noDiv (e : Expr) (h : NoDiv e) : eval e = .ok (evalPure e) :=
-- END SPEC
  by
    induction e with
    | num n => rfl
    | add a b iha ihb =>
      obtain ⟨ha, hb⟩ := h
      simp [eval, iha ha, ihb hb, evalPure]
    | div a b => exact absurd h id

-- BEGIN SPEC
theorem div_zero_fails (a : Expr) : ∃ msg, eval (.div a (.num 0)) = .error msg :=
-- END SPEC
  by
    cases h : eval a with
    | error e => exact ⟨e, by simp [eval, h]⟩
    | ok x => exact ⟨"division by zero", by simp [eval, h]; rfl⟩

end M19

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `eval_noDiv`: induction on `e`; the `div` case is impossible because `NoDiv (.div a b)` is `False`.
H2. In the `add` case rewrite both sub-evaluations with the IHs, then the given simp lemmas finish the `do` block.
H3. `div_zero_fails`: `cases h : eval a with | error e => exact ⟨e, by simp [eval, h]⟩ | ok x => exact ⟨"division by zero", by simp [eval, h]; rfl⟩`.
-/
