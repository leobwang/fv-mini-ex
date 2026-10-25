/- H01 | Compiling expressions to a stack machine | 45-75 min | compiler correctness, induction generalizing, List
GOAL
  Prove that compiling arithmetic expressions to stack-machine code is correct: running the code
  on an empty stack leaves exactly the expression's value. Then do the same for a compiler that
  emits code in continuation-passing style (no `++`).

REFERENCE
  -- Run a program on a stack: `exec env (i :: is) s = exec env is (step env i s)`.
  example (env : Nat → Nat) : H01.exec env [.push 2, .push 3, .add] [] = [5] := rfl
  example (env : Nat → Nat) (s : List Nat) (a b : Nat) :
      H01.step env .add (b :: a :: s) = (a + b) :: s := rfl
  #check List.append_assoc   -- as ++ bs ++ cs = as ++ (bs ++ cs)
  -- The statement for `[]` is too weak to induct on: generalise to an arbitrary initial stack.
  -- Code for `add a b` runs `compile a` then `compile b`: you need a lemma about `exec` on `p ++ q`.
-/

namespace H01

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

-- MILESTONE (optional: change or delete)
theorem exec_append (env : Nat → Nat) (p q : List Instr) (s : List Nat) :
    exec env (p ++ q) s = exec env q (exec env p s) := by
  induction p generalizing s with
  | nil => rfl
  | cons i p ih => simp [exec, ih]

-- MILESTONE (optional: change or delete)
theorem compile_gen (env : Nat → Nat) (e : Expr) (s : List Nat) :
    exec env (compile e) s = eval env e :: s := by
  induction e generalizing s with
  | num n => rfl
  | var x => rfl
  | add a b iha ihb => simp [compile, exec_append, iha, ihb, exec, step, eval]
  | mul a b iha ihb => simp [compile, exec_append, iha, ihb, exec, step, eval]

-- MILESTONE (optional: change or delete)
theorem compileAcc_eq (e : Expr) (k : List Instr) : compileAcc e k = compile e ++ k := by
  induction e generalizing k with
  | num n => rfl
  | var x => rfl
  | add a b iha ihb => simp [compileAcc, compile, iha, ihb]
  | mul a b iha ihb => simp [compileAcc, compile, iha, ihb]

-- BEGIN SPEC
theorem compile_correct (env : Nat → Nat) (e : Expr) : exec env (compile e) [] = [eval env e] :=
-- END SPEC
  compile_gen env e []

-- BEGIN SPEC
theorem compileAcc_correct (env : Nat → Nat) (e : Expr) :
    exec env (compileAcc e []) [] = [eval env e] :=
-- END SPEC
  by rw [compileAcc_eq, List.append_nil, compile_correct]

end H01

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Three facts do all the work: `exec` distributes over `++`, compiled code pushes its value on any stack, and `compileAcc e k = compile e ++ k`.
H2. Each milestone is an induction generalising the "extra" argument (the stack `s`, or the continuation `k`).
H3. `compile_gen` add case: `simp [compile, exec_append, iha, ihb, exec, step, eval]`; `compileAcc_correct`: `rw [compileAcc_eq, List.append_nil, compile_correct]`.
-/
