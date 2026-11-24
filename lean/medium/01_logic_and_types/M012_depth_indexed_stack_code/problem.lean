/- M012 | Depth-indexed stack code | 15-20 min | indexed families, dependent pattern matching, typed compiler, induction generalizing, fun_induction
GOAL
  Instructions and code carry the stack depth in their type (`Instr n m` turns a depth-`n` stack into
  a depth-`m` one), so `run` needs no error case. Prove that running appended code composes, that the
  peephole optimiser `opt` preserves meaning and never lengthens code, and that `compile e`, run on
  any stack `s`, pushes exactly `e.eval` (`e.eval` = the value of expression `e`).

BANNED: import, exact?, apply?, try?, grind, solve_by_elim

GUIDE
  Entries R1–R9: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · run_append
  1. Induction on the code `c`. `d` and `s` mention its indices, so Lean generalizes them:  R1
       ih : ∀ (d : Code k✝ k) (s : Vec Nat m✝), (c.append d).run s = d.run (c.run s)
  2. nil: both sides compute to `d.run s`:                                    rfl (R2)
  3. cons: unfold `Code.append`, then `Code.run`, on the constructor;
     then the IH, instantiated at the stack `i.run s`:                        R2 → R3
-/
-- BEGIN SPEC
theorem run_append {n m k : Nat} (c : Code n m) (d : Code m k) (s : Vec Nat n) :
    (c.append d).run s = d.run (c.run s) :=
-- END SPEC
  sorry

/- SKELETON · opt_correct
  1. One goal per arm of `opt` (four), not per constructor of `Code`:         R5
  2. Every arm (`<;>`): unfold `Code.run` on the constructors and `Instr.run`
     on the pushed stack (that is what lets `add`/`mul` compute), and let the
     unnamed IH `ih1✝` finish:                                                R2, R4, R6
-/
-- BEGIN SPEC
theorem opt_correct {n m : Nat} (c : Code n m) (s : Vec Nat n) : (opt c).run s = c.run s :=
-- END SPEC
  sorry

/- SKELETON · opt_len
  1. One goal per arm of `opt`:                                               R5
  2. Every arm (`<;>`): unfold `Code.len` and use the unnamed IH:             R2, R6
  3. The two folding arms are left as `(opt c✝).len ≤ c✝.len + 2`:            R7
-/
-- BEGIN SPEC
theorem opt_len {n m : Nat} (c : Code n m) : (opt c).len ≤ c.len :=
-- END SPEC
  sorry

/- SKELETON · compile_correct
  1. Induction on `e`, generalizing the depth `n` (the IH for `b` is needed
     at depth `n + 1`):                                                       R8
       iha : ∀ {n : Nat} (s : Vec Nat n), (compile a).run s = Vec.cons a.eval s
  2. num: both sides compute:                                                 rfl (R2)
  3. add (mul is the same):
       unfold `compile`                                                       R2
       split the code with `run_append` (Part 1), use `iha` at depth `n`;
       split again, use `ihb` at depth `n + 1`                                rw [run_append], R9
       compute `Code.run`, `Instr.run` on the pushed stack, then `Expr.eval`  R2, R4
-/
-- BEGIN SPEC
theorem compile_correct {n : Nat} (e : Expr) (s : Vec Nat n) :
    (compile e).run s = .cons e.eval s :=
-- END SPEC
  sorry

end M012

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `run_append` is structural induction on `c` (R1). The two `opt` lemmas follow the arms of `opt`, not
    the constructors of `Code`. `compile_correct` is induction on `e`; `run_append` splits the code of
    `add a b` into its parts.
H2. Plain `induction c` on `opt_correct` stalls: `opt (.cons i c)` does not unfold until you split the next
    two instructions by hand. `fun_induction opt c` (R5) gives one goal per arm of `opt`; its IH is
    unnamed, so finish each arm with `simp_all` (R6), and `omega` (R7) for the lengths. In
    `compile_correct`, `compile b` starts at depth `n + 1`: use `induction e generalizing n` (R8).
H3. `run_append`, `cons` case: `simp [Code.append, Code.run, ih]`. `opt_correct`: `fun_induction opt c`,
    then in every arm `simp_all` with `Code.run` and `Instr.run` (`opt_len`: `Code.len`, then `omega`).
    `compile_correct`, `add` case: `simp [compile, run_append, iha, ihb, Code.run, Instr.run, Expr.eval]`.
-/
