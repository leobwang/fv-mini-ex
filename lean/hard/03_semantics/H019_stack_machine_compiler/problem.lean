/- H019 | Compiling expressions to a stack machine | 45-75 min | compiler correctness, induction generalizing, List
GOAL
  Prove that compiling arithmetic expressions to stack-machine code is correct: running the code
  on an empty stack leaves exactly the expression's value. Then do the same for a compiler that
  emits code in continuation-passing style (no `++`).

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace H019

-- BEGIN SPEC
inductive Expr where
  | num (n : Nat)
  | var (x : Nat)
  | add (a b : Expr)
  | mul (a b : Expr)

def eval (env : Nat → Nat) : Expr → Nat
  | .num n => n
  | .var x => env x
  | .add a b => eval env a + eval env b
  | .mul a b => eval env a * eval env b

inductive Instr where
  | push (n : Nat)
  | load (x : Nat)
  | add
  | mul

def step (env : Nat → Nat) : Instr → List Nat → List Nat
  | .push n, s => n :: s
  | .load x, s => env x :: s
  | .add, b :: a :: s => (a + b) :: s
  | .mul, b :: a :: s => (a * b) :: s
  | _, s => s

def exec (env : Nat → Nat) : List Instr → List Nat → List Nat
  | [], s => s
  | i :: is, s => exec env is (step env i s)

def compile : Expr → List Instr
  | .num n => [.push n]
  | .var x => [.load x]
  | .add a b => compile a ++ compile b ++ [.add]
  | .mul a b => compile a ++ compile b ++ [.mul]

def compileAcc : Expr → List Instr → List Instr
  | .num n, k => .push n :: k
  | .var x, k => .load x :: k
  | .add a b, k => compileAcc a (compileAcc b (.add :: k))
  | .mul a b, k => compileAcc a (compileAcc b (.mul :: k))
-- END SPEC

/- SKELETON · exec_append   (milestone 1: used in compile_gen, cases add and mul)
  1. Induct on `p`, generalizing the stack `s` (`exec` changes the stack as it runs):   R1
  2. nil: both sides compute to `exec env q s`:                                          R2
  3. cons: one `simp` with `exec` and `ih`. It moves `i` out of the append, applies
     `exec`'s cons equation on both sides, then uses `ih` at the stack `step env i s`:  R3 → R4 → R5
  Model: guide W1 (same shape on `run`).
-/
-- MILESTONE (optional: change or delete)
theorem exec_append (env : Nat → Nat) (p q : List Instr) (s : List Nat) :
    exec env (p ++ q) s = exec env q (exec env p s) := by
  sorry

/- SKELETON · compile_gen   (milestone 2: compile_correct is its case `s = []`)
  Prove exec_append first; step 3 uses it.
  1. Induct on `e`, generalizing `s`: four goals; `add`, `mul` get two IHs `iha ihb`:     R6
  2. num, var: both sides compute:                                                       R2
  3. add (mul is the same): one `simp` that unfolds `compile`, regroups the `++`,
     splits the run with exec_append, runs `compile a` on `s` (iha) and `compile b` on
     `eval env a :: s` (ihb), executes the last instruction, then unfolds `eval`:       R4, R7, R8, R5, R9, R4
-/
-- MILESTONE (optional: change or delete)
theorem compile_gen (env : Nat → Nat) (e : Expr) (s : List Nat) :
    exec env (compile e) s = eval env e :: s := by
  sorry

/- SKELETON · compileAcc_eq   (milestone 3: used in compileAcc_correct)
  1. Induct on `e`, generalizing the continuation `k`:                                   R6
  2. num, var: `Instr.push n :: k` and `[Instr.push n] ++ k` compute to the same list:  R2
  3. add (mul is the same): one `simp` with `compileAcc`, `compile`, `iha`, `ihb`.
     It unfolds `compileAcc`, uses ihb at `Instr.add :: k` and iha at
     `compile b ++ Instr.add :: k`, unfolds `compile` on the right side, and the
     append lemmas then make the two sides match:                                        R4, R5, R4, R7, R3, R10
  Model: guide W2, W3 (same shape on `flatAcc`).
-/
-- MILESTONE (optional: change or delete)
theorem compileAcc_eq (e : Expr) (k : List Instr) : compileAcc e k = compile e ++ k := by
  sorry

/- SKELETON · compile_correct
  Prove compile_gen first; it is the whole proof.
  1. compile_gen at the stack `[]` (`eval env e :: []` is `[eval env e]`):               R11
-/
-- BEGIN SPEC
theorem compile_correct (env : Nat → Nat) (e : Expr) : exec env (compile e) [] = [eval env e] :=
-- END SPEC
  sorry

/- SKELETON · compileAcc_correct
  Prove compileAcc_eq first (milestone 3); compile_correct is just above.
  1. Rewrite `compileAcc e []` with compileAcc_eq:                                        R8
  2. Drop the `++ []`:                                                                    R12
  3. Finish with compile_correct; `rw` closes the goal with `rfl`:                       R13
-/
-- BEGIN SPEC
theorem compileAcc_correct (env : Nat → Nat) (e : Expr) :
    exec env (compileAcc e []) [] = [eval env e] :=
-- END SPEC
  sorry

end H019

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `compile_correct` is too weak to induct on: its stack is `[]`, but the code of `b` in `add a b`
    runs on `eval env a :: s`. Prove the milestones in order: `exec` distributes over `++`
    (exec_append), compiled code pushes its value on ANY stack (compile_gen), and
    `compileAcc e k = compile e ++ k` (compileAcc_eq). The two spec theorems then follow directly.
H2. Each milestone is an induction generalizing the argument that changes in recursive calls:
    `induction p generalizing s` (R1), `induction e generalizing s` / `generalizing k` (R6). Base
    cases are `rfl` (R2); each step case is one `simp` with the definitions, the IHs and, in
    compile_gen, exec_append.
H3. compile_gen add case: `simp [compile, exec_append, iha, ihb, exec, step, eval]`;
    compileAcc_eq add case: `simp [compileAcc, compile, iha, ihb]`; compile_correct is the term
    `compile_gen env e []`; compileAcc_correct: `rw [compileAcc_eq, List.append_nil, compile_correct]`.
-/
