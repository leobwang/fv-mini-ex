/- M012 | Depth-indexed stack code | 15-20 min | indexed families, dependent pattern matching, typed compiler, induction generalizing, fun_induction
GOAL
  Instructions and code carry the stack depth in their type (`Instr n m` turns a depth-`n` stack into
  a depth-`m` one), so `run` needs no error case. Prove that running appended code composes, that the
  peephole optimiser `opt` preserves meaning and never lengthens code, and that `compile e`, run on
  any stack `s`, pushes exactly `e.eval` (`e.eval` = the value of expression `e`).

REFERENCE
  example : Code 0 1 := .cons (.push 2) (.cons (.push 3) (.cons .add .nil))  -- a well-typed program
  example : (Code.cons (.push 2) (.cons (.push 3) (.cons .add .nil))).run .nil = .cons 5 .nil := rfl
  example : (compile (n := 0) (.add (.num 2) (.num 3))).run .nil = .cons 5 .nil := rfl
    -- `(n := 0)` fixes the implicit start depth; `compile e : Code n (n + 1)` for every `n`
  -- `induction e with | num k => _ | add a b iha ihb => _ | mul a b iha ihb => _`
  -- `simp [Code.run, Instr.run, h]`: unfold those definitions and rewrite with lemma/hypothesis `h`
BANNED: import, exact?, apply?, try?, grind, solve_by_elim
NOTE: Do not add imports or leave search tactics (`exact?`, `apply?`, `try?`) in the file.
-/

namespace M012

-- BEGIN SPEC
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)

/-- An instruction that turns a stack of depth `n` into one of depth `m`. -/
inductive Instr : Nat → Nat → Type where
  | push {n : Nat} (k : Nat) : Instr n (n + 1)
  | add {n : Nat} : Instr (n + 2) (n + 1)
  | mul {n : Nat} : Instr (n + 2) (n + 1)

/-- Well-typed code: the depths of consecutive instructions match up. -/
inductive Code : Nat → Nat → Type where
  | nil {n : Nat} : Code n n
  | cons {n m k : Nat} (i : Instr n m) (c : Code m k) : Code n k

/-- No error case: `add` only accepts stacks of depth `n + 2`, which always have two elements. -/
def Instr.run : {n m : Nat} → Instr n m → Vec Nat n → Vec Nat m
  | _, _, .push k, s => .cons k s
  | _, _, .add, .cons b (.cons a s) => .cons (a + b) s
  | _, _, .mul, .cons b (.cons a s) => .cons (a * b) s

def Code.run : {n m : Nat} → Code n m → Vec Nat n → Vec Nat m
  | _, _, .nil, s => s
  | _, _, .cons i c, s => c.run (i.run s)

def Code.append : {n m k : Nat} → Code n m → Code m k → Code n k
  | _, _, _, .nil, d => d
  | _, _, _, .cons i c, d => .cons i (c.append d)

def Code.len : {n m : Nat} → Code n m → Nat
  | _, _, .nil => 0
  | _, _, .cons _ c => c.len + 1

/-- Peephole optimiser: `push a; push b; add` becomes `push (a + b)` (same for mul). -/
def opt : {n m : Nat} → Code n m → Code n m
  | _, _, .cons (.push a) (.cons (.push b) (.cons .add c)) => .cons (.push (a + b)) (opt c)
  | _, _, .cons (.push a) (.cons (.push b) (.cons .mul c)) => .cons (.push (a * b)) (opt c)
  | _, _, .cons i c => .cons i (opt c)
  | _, _, .nil => .nil

/-- Arithmetic expressions. -/
inductive Expr where
  | num (k : Nat)
  | add (a b : Expr)
  | mul (a b : Expr)

def Expr.eval : Expr → Nat
  | .num k => k
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval

/-- Compile to typed code: on a stack of any depth `n` it leaves exactly one more value. -/
def compile {n : Nat} : Expr → Code n (n + 1)
  | .num k => .cons (.push k) .nil
  | .add a b => (compile a).append ((compile b).append (.cons .add .nil))
  | .mul a b => (compile a).append ((compile b).append (.cons .mul .nil))
-- END SPEC

-- BEGIN SPEC
theorem run_append {n m k : Nat} (c : Code n m) (d : Code m k) (s : Vec Nat n) :
    (c.append d).run s = d.run (c.run s) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem opt_correct {n m : Nat} (c : Code n m) (s : Vec Nat n) : (opt c).run s = c.run s :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem opt_len {n m : Nat} (c : Code n m) : (opt c).len ≤ c.len :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem compile_correct {n : Nat} (e : Expr) (s : Vec Nat n) :
    (compile e).run s = .cons e.eval s :=
-- END SPEC
  sorry

end M012

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `run_append` is structural induction on `c`. The two `opt` lemmas follow the shape of `opt`, not of
    `Code`. `compile_correct` is induction on `e`; `run_append` splits the code of `add a b` into its parts.
H2. Plain `induction c` on `opt_correct` stalls: in the `cons` case `opt` does not unfold until you split
    on the next two instructions by hand. `fun_induction opt c` (E084) gives one goal per arm of `opt`,
    overlapping arms included. In `compile_correct`, `compile b` starts at depth `n + 1`, so the IH for
    `b` is needed at a different depth than the goal's `n`.
H3. `opt_correct`: `fun_induction opt c`, then in each arm unfold `Code.run`, `Instr.run` and use the IH
    (`opt_len`: the same with `Code.len`, and `omega` for the leftover arithmetic). `compile_correct`:
    `induction e generalizing n`; in `add`, unfold `compile`, rewrite with `run_append` and both IHs, then
    unfold `Code.run`, `Instr.run`, `Expr.eval`.
-/
