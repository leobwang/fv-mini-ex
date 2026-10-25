// H07 | Expression compiler | 45-90 min | datatypes, compiler correctness, generalized lemma
// GOAL
//   Write Compile from arithmetic expressions to a stack machine and prove that running the
//   code on an empty stack leaves exactly the expression's value.
//
// REFERENCE
//   Compile(e1) + Compile(e2) + [IAdd]                 // postfix code for e1 + e2
//   lemma L(c1: seq<Instr>, c2: seq<Instr>, st: seq<int>) ensures Exec(c1 + c2, st, env) == ...
//   assert (c1 + c2)[1..] == c1[1..] + c2;             // tail of a concatenation (M14)
//   assert (st + [a] + [b])[..|st|] == st;             // dropping the two top elements
//   // Generalize: the empty-stack statement is too weak as an induction hypothesis. Prove what
//   // Compile(e) does to ANY stack and ANY code that follows it.

// BEGIN SPEC
datatype Expr = Const(n: int) | Var(name: string) | Add(a: Expr, b: Expr) | Mul(a: Expr, b: Expr)

function Eval(e: Expr, env: string -> int): int
{
  match e
  case Const(n) => n
  case Var(x) => env(x)
  case Add(a, b) => Eval(a, env) + Eval(b, env)
  case Mul(a, b) => Eval(a, env) * Eval(b, env)
}

datatype Instr = Push(n: int) | Load(name: string) | IAdd | IMul

function Step(i: Instr, st: seq<int>, env: string -> int): seq<int>
{
  match i
  case Push(n) => st + [n]
  case Load(x) => st + [env(x)]
  case IAdd => if |st| < 2 then st else st[..|st| - 2] + [st[|st| - 2] + st[|st| - 1]]
  case IMul => if |st| < 2 then st else st[..|st| - 2] + [st[|st| - 2] * st[|st| - 1]]
}

function Exec(code: seq<Instr>, st: seq<int>, env: string -> int): seq<int>
  decreases |code|
{
  if |code| == 0 then st else Exec(code[1..], Step(code[0], st, env), env)
}

function Compile(e: Expr): seq<Instr>
// END SPEC
{
  match e
  case Const(n) => [Push(n)]
  case Var(x) => [Load(x)]
  case Add(a, b) => Compile(a) + Compile(b) + [IAdd]
  case Mul(a, b) => Compile(a) + Compile(b) + [IMul]
}

// BEGIN SPEC
lemma CompileCorrect(e: Expr, env: string -> int)
  ensures Exec(Compile(e), [], env) == [Eval(e, env)]
// END SPEC
{
  CompileGen(e, [], env);
}

// MILESTONE (optional: change or delete)
lemma ExecAppend(c1: seq<Instr>, c2: seq<Instr>, st: seq<int>, env: string -> int)
  ensures Exec(c1 + c2, st, env) == Exec(c2, Exec(c1, st, env), env)
  decreases |c1|
{
  if |c1| == 0 {
    assert c1 + c2 == c2;
  } else {
    assert (c1 + c2)[1..] == c1[1..] + c2;
    ExecAppend(c1[1..], c2, Step(c1[0], st, env), env);
  }
}

// MILESTONE (optional: change or delete)
lemma CompileGen(e: Expr, st: seq<int>, env: string -> int)
  ensures Exec(Compile(e), st, env) == st + [Eval(e, env)]
{
  match e
  case Const(n) =>
  case Var(x) =>
  case Add(a, b) =>
    ExecAppend(Compile(a) + Compile(b), [IAdd], st, env);
    ExecAppend(Compile(a), Compile(b), st, env);
    CompileGen(a, st, env);
    CompileGen(b, st + [Eval(a, env)], env);
    var s2 := st + [Eval(a, env)] + [Eval(b, env)];
    assert s2[..|s2| - 2] == st;
  case Mul(a, b) =>
    ExecAppend(Compile(a) + Compile(b), [IMul], st, env);
    ExecAppend(Compile(a), Compile(b), st, env);
    CompileGen(a, st, env);
    CompileGen(b, st + [Eval(a, env)], env);
    var s2 := st + [Eval(a, env)] + [Eval(b, env)];
    assert s2[..|s2| - 2] == st;
}
/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Compile in postfix order: operands first, then the operator. The empty-stack lemma follows
    from a stronger one.
H2. Milestones: Exec distributes over code concatenation (induction on c1), and running
    Compile(e) on any stack st pushes Eval(e, env) (structural induction on e). For Add/Mul,
    split the code with ExecAppend twice, use the two induction hypotheses, then one Step.
H3. lemma CompileGen(e: Expr, st: seq<int>, env: string -> int)
      ensures Exec(Compile(e), st, env) == st + [Eval(e, env)]
    Add case: ExecAppend(Compile(a) + Compile(b), [IAdd], st, env);
              ExecAppend(Compile(a), Compile(b), st, env); CompileGen(a, st, env);
              CompileGen(b, st + [Eval(a, env)], env);
*/
