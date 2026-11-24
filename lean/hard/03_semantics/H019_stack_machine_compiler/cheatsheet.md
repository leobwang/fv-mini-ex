# H019 · Compiling expressions to a stack machine: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): inductive types and functions defined by pattern
matching, `List` with `::`, `++` and `[a, b]`, `induction`/`cases` on `Nat` and lists, `rfl`, `exact`,
`rw`, `simp`. **New here:** compiler correctness as a theorem about two functions, induction on your own
expression type with two induction hypotheses, `induction … generalizing` (the IH must hold for every
stack / every continuation), and the `List` append lemmas. No Mathlib.

The guide works on its own objects, not on `Expr`/`Instr`:

| Guide object | Plays the role of | Definition |
|---|---|---|
| `Cmd`, `act`, `run cs n` | `Instr`, `step`, `exec env p s` | `run [] n = n`, `run (c :: cs) n = run cs (act c n)` |
| `Tree` (`leaf n`, `node l r`) | `Expr` (`num n`, `add a b`, …) | a type with two recursive arguments in one constructor |
| `flat`, `flatAcc t k` | `compile`, `compileAcc e k` | `flat (node l r) = flat l ++ flat r`; `flatAcc (node l r) k = flatAcc l (flatAcc r k)` |
| `pop2` | `step env .add` | `pop2 (b :: a :: s) = (a + b) :: s`, any other stack unchanged |

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- A hypothesis that itself contains `, ` (such as `ih : ∀ (s : β), P l s`) sits in its own code span on
  the line above the `⊢` span.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- Placeholders are Lean binders: `{α β : Type}` are any types, `(as bs : List α)` any lists.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `env : Nat → Nat` | the environment: variable number `x` ↦ its value `env x` |
| `s : List Nat` | a stack; the head of the list is the top of the stack |
| `n :: s` | push `n` on `s` |
| `[a]`, `[a, b]` | `a :: []`, `a :: b :: []` |
| `p ++ q` | run program `p`, then `q`; `++` groups to the left: `p ++ q ++ r` is `(p ++ q) ++ r` |
| `a :: as ++ bs` | `(a :: as) ++ bs` (`::` binds tighter than `++`) |
| `Expr.num n`, `Expr.var x`, `a.add b`, `a.mul b` | the expressions `num n`, `var x`, `add a b`, `mul a b`: Lean prints `Expr.add a b` as `a.add b` (dot notation, same term) |
| `eval env e` | the value of expression `e`, reading variable `x` as `env x` |
| `compile e` | the instruction list for `e`: code of the operands, then the operator (`compile (a.add b) = compile a ++ compile b ++ [Instr.add]`) |
| `compileAcc e k` | the code of `e` followed by the continuation `k` (code to run afterwards), built with `::` only |
| `Instr.add`, `.push n` | an instruction; in source code `.push n` is short for `Instr.push n` when the type is known |
| `exec env p s` | the stack after running program `p` on stack `s` |
| `step env Instr.add (b :: a :: s)` | pops `b` (top), then `a`, pushes `a + b`: `(a + b) :: s`. With fewer than two values, `step` returns the stack unchanged |
| `iha : ∀ (s : List Nat), …` | an induction hypothesis that holds for every stack (from `generalizing s`) |
| `case nil`, `case cons`, `case num`, `case add` | the goal for that constructor (named by `induction … with`) |

---

## Part 1 · `exec_append` (milestone 1: used in Part 2)

Statement: `exec env (p ++ q) s = exec env q (exec env p s)`: running `p ++ q` is running `p`, then `q`
on the resulting stack. Induct on `p`; `exec` consumes `p` from the left, so induction on `p` matches it.

**R1 · `induction l generalizing s with | nil => … | cons x l ih => …`** changes the **goal list**: one
goal per constructor of `List`. `generalizing s` first removes `s` from the context and puts it back into
each goal, so `ih` says `∀ s, …` and may be used at any stack (needed because `exec` changes the stack as
it runs). Without it, `ih` holds only for the original `s`. Placeholders:
`{α β : Type} (P : List α → β → Prop) (l : List α) (s : β)`.

| Before | After |
|---|---|
| `l : List α, s : β ⊢ P l s` | `s : β ⊢ P [] s`, `ih : ∀ (s : β), P l s`<br>`x : α, l : List α, s : β ⊢ P (x :: l) s` |

**R2 · `rfl`** **closes** an equation whose sides compute to the same term by the defining equations
(`exec env [] s = s`, `[] ++ q = q`, `compile (Expr.num n) = [Instr.push n]`, …). This is the `nil` case
here and the `num`, `var` cases in Parts 2 and 3. Placeholders: `(cs : List Cmd) (n : Nat)` (toy objects).
Guide example:

| Before | After |
|---|---|
| `⊢ run ([] ++ cs) n = run cs (run [] n)` | closed by `rfl` |

**R3 · `List.cons_append`** changes the **goal**. `List.cons_append : a :: as ++ bs = a :: (as ++ bs)`:
the head of the first list moves outside the append, so `exec`'s `cons` equation can fire. Placeholders:
`{α : Type} (a : α) (as bs : List α)`.

| Before | After |
|---|---|
| `⊢ P (a :: as ++ bs)` | `⊢ P (a :: (as ++ bs))` |

**R4 · `simp only [f]`** changes the **goal**: where `f` is applied to a constructor (`[]`, `i :: is`,
`Expr.add a b`, …), it is replaced by the right side of the matching defining equation. `simp [exec]`,
`simp [compile]`, `simp [eval]` work this way. Placeholders: `(c : Cmd) (cs : List Cmd) (n : Nat)` (toy
objects), `(P : Nat → Prop)`. Guide example:

| Before | After |
|---|---|
| `⊢ P (run (c :: cs) n)` | `⊢ P (run cs (act c n))` |

**R5 · `simp only [ih]`** with `ih : ∀ m, f m = g m` changes the **goal**: every `f t` becomes `g t`,
with `m := t` found by matching. That is how a generalized IH is used at the stack the goal has at that
point. Placeholders: `(f g : Nat → Nat) (ih : ∀ m, f m = g m) (k : Nat)`.

| Before | After |
|---|---|
| `⊢ P (f (k + 1))` | `⊢ P (g (k + 1))` |

The whole `cons` case is `simp [exec, ih]`: R3, then R4, then R5 (guide W1).

---

## Part 2 · `compile_gen` (milestone 2: gives `compile_correct` in Part 4)

Statement: `exec env (compile e) s = eval env e :: s`: compiled code pushes the value of `e` on top of
ANY stack `s` and leaves the rest alone. `compile_correct` is the case `s = []`, but that case alone is
too weak to induct on: in `add a b` the code of `b` runs on the stack `eval env a :: s`, not on `[]`.

**R6 · `induction e generalizing s with | num n => … | var x => … | add a b iha ihb => … | mul a b iha ihb => …`**
changes the **goal list**: one goal per constructor of `Expr`, and one IH per recursive argument (`iha`
for `a`, `ihb` for `b`). Name them in the order of the constructor's arguments. Placeholders:
`(P : Tree → List Nat → Prop) (t : Tree) (k : List Nat)`. Guide example (on `Tree`):

| Before | After |
|---|---|
| `t : Tree, k : List Nat ⊢ P t k` | `n : Nat, k : List Nat ⊢ P (Tree.leaf n) k`, `ihl : ∀ (k : List Nat), P l k`<br>`ihr : ∀ (k : List Nat), P r k`<br>`l r : Tree, k : List Nat ⊢ P (l.node r) k` |

**R7 · `List.append_assoc`** changes the **goal**. `List.append_assoc : as ++ bs ++ cs = as ++ (bs ++ cs)`.
`compile (a.add b)` unfolds to `compile a ++ compile b ++ [Instr.add]`, which is
`(compile a ++ compile b) ++ [Instr.add]`; `simp` re-groups it to the right. Placeholders:
`{α : Type} (as bs cs : List α)`.

| Before | After |
|---|---|
| `⊢ P (as ++ bs ++ cs)` | `⊢ P (as ++ (bs ++ cs))` |

**R8 · `rw [L]` / `simp [L]` with a lemma `L` you proved earlier** changes the **goal**: its arguments are
found by matching its left side. Here `L` is `exec_append`, which turns `exec env (p ++ q) s` into
`exec env q (exec env p s)`, once per `++`. The guide uses the library lemma of the same shape,
`List.foldl_append : List.foldl f b (l ++ l') = List.foldl f (List.foldl f b l) l'`. Placeholders:
`{α β : Type} (f : β → α → β) (b : β) (l l' : List α)`.

| Before | After |
|---|---|
| `⊢ P (List.foldl f b (l ++ l'))` | `⊢ P (List.foldl f (List.foldl f b l) l')` |

**R9 · `simp only [step]` on a `match` with a catch-all case** changes the **goal**, but only when the
argument visibly has the shape of an earlier case. `step env Instr.add (b :: a :: s)` reduces to
`(a + b) :: s`; `step env Instr.add s` with a bare variable `s` does not reduce (the catch-all `_` might
apply). So `iha` and `ihb` (R5) must first turn the stack into `eval env b :: eval env a :: s`; `simp`
keeps rewriting until all of them fire. Placeholders: `(a b : Nat) (s : List Nat) (P : List Nat → Prop)`.
Guide example (on `pop2`):

| Before | After |
|---|---|
| `⊢ P (pop2 (b :: a :: s))` | `⊢ P ((a + b) :: s)` |

The `add` case is one `simp` call with `compile`, `exec_append`, `iha`, `ihb`, `exec`, `step`, `eval`:
R4, R7, R8, R5, R9. `simp?` prints the lemmas it used, in order:
`compile, List.append_assoc, exec_append, iha, exec, step, ihb, eval`. The `mul` case is the same.

---

## Part 3 · `compileAcc_eq` (milestone 3: used in Part 5)

Statement: `compileAcc e k = compile e ++ k`. `compileAcc` emits the code of `e` followed by the
continuation `k` without ever calling `++`. Induct on `e`, generalizing `k` (R6): in `add a b`, the IH for
`b` is used at `Instr.add :: k` and the IH for `a` at `compileAcc b (Instr.add :: k)` (W3 has the same shape).
`num`, `var`: R2. `add`, `mul`: `simp` with `compileAcc`, `compile`, `iha`, `ihb` (R4, R5), which also
applies R7, R3 and R10 to the right side. `simp?` prints, in order:
`compileAcc, ihb, iha, compile, List.append_assoc, List.cons_append, List.nil_append`.

**R10 · `List.nil_append`** changes the **goal**. `List.nil_append : [] ++ as = as`. With R3 it turns
`[Instr.add] ++ k`, that is `Instr.add :: [] ++ k`, into `Instr.add :: k` (`List.singleton_append` does both
at once). Placeholders: `{α : Type} (as : List α)`.

| Before | After |
|---|---|
| `⊢ P ([] ++ as)` | `⊢ P as` |

---

## Part 4 · `compile_correct`

Statement: `exec env (compile e) [] = [eval env e]`. No induction: it is milestone 2 at `s = []`.

**R11 · `exact H []`** (or the bare term `H []` after `:=`) **closes** the goal: `H : ∀ s, …` used at the
argument `[]`. It works without any rewriting because `[a]` is notation for `a :: []`, so
`eval env e :: []` and `[eval env e]` are the same term. Placeholders:
`(f : List Nat → List Nat) (a : Nat) (H : ∀ s, f s = a :: s)`.

| Before | After |
|---|---|
| `⊢ f [] = [a]` | closed by `exact H []` |

---

## Part 5 · `compileAcc_correct`

Statement: `exec env (compileAcc e []) [] = [eval env e]`. Rewrite `compileAcc` away with milestone 3
(R8), drop the `++ []` (R12), and finish with Part 4 (R13).

**R12 · `List.append_nil`** changes the **goal**. `List.append_nil : as ++ [] = as`. Placeholders:
`{α : Type} (as : List α)`.

| Before | After |
|---|---|
| `⊢ P (as ++ [])` | `⊢ P as` |

**R13 · `rw [L]` closes the goal**: after rewriting, `rw` tries `rfl`, so if the goal becomes `x = x`
it is closed and no tactic may follow. `rw [compile_correct]` does this as the last step. Placeholders:
`(f g : List Nat → List Nat) (L : ∀ s, f s = g s)`.

| Before | After |
|---|---|
| `⊢ f [] = g []` | closed by `rw [L]` |

---

### Worked combinations (W1–W4, on the toy objects)

**W1:** `run (cs ++ ds) n = run ds (run cs n)`: R1 on `cs` generalizing `n`; `nil` by `rfl` (R2); `cons` by
`simp only [List.cons_append, run, ih]` (R3, R4, R5).

**W2:** `flatAcc t k = flat t ++ k`: R6 on `t` generalizing `k`; `leaf` by `rfl`; `node` by
`simp only [flatAcc, flat, ihl, ihr, List.append_assoc]`.

**W3:** W2's `node` case one rewrite at a time. `ihr` is used at `k`, `ihl` at `flat r ++ k`, a list
that is not the original `k`; that is why `generalizing k` is needed:

```lean-goal
⊢ flatAcc (l.node r) k = flat (l.node r) ++ k
⊢ flatAcc l (flatAcc r k) = flat (l.node r) ++ k
⊢ flatAcc l (flat r ++ k) = flat (l.node r) ++ k
⊢ flat l ++ (flat r ++ k) = flat (l.node r) ++ k
⊢ flat l ++ (flat r ++ k) = flat l ++ flat r ++ k
```

The last `rw [List.append_assoc]` makes both sides equal and closes the goal (R13).

**W4:** on a concrete stack, `simp only [pop2]` fires twice and evaluates the numerals:

```lean-goal
⊢ pop2 (pop2 (3 :: 2 :: 1 :: s)) = 6 :: s
```

---

## Traps

- **Forgetting `generalizing`.** `induction e` with `s` fixed gives `iha : exec env (compile a) s = …` for
  that one `s`, but the `add` case needs `ihb` at `eval env a :: s`. Generalize the stack (Parts 1, 2) and
  the continuation (Part 3).
- **Inducting on `compile_correct` directly.** Its stack is `[]`, which is not general enough; prove
  milestone 2 and specialise (R11).
- `step env Instr.add s` does not reduce while `s` is a variable (R9): rewrite with the IHs first, or let
  one `simp` call do all of it.
- Lean prints `Expr.add a b` as `a.add b`: same term, dot notation. In `induction … with`, the
  alternative names are the constructor names (`| add a b iha ihb`), not the printed form.
- The milestones must come before the theorems that use them (Lean reads the file top to bottom); a
  milestone's statement may be changed, a `BEGIN SPEC` region may not.
- `rw` ends with `rfl` (R13): writing another tactic after a `rw` that closed the goal is an error
  ("no goals").

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induct on a program, IH for every stack | `induction p generalizing s with \| nil => … \| cons i p ih => …` | R1 |
| induct on an expression, two IHs | `induction e generalizing s with \| num n => … \| var x => … \| add a b iha ihb => … \| mul a b iha ihb => …` | R6 |
| base cases that just compute | `rfl` | R2 |
| unfold `exec`, `compile`, `eval`, `step` on constructors | `simp [exec, compile, eval, step]` | R4, R9 |
| `(i :: p) ++ q → i :: (p ++ q)` | `List.cons_append` | R3 |
| `p ++ q ++ r → p ++ (q ++ r)` | `List.append_assoc` | R7 |
| `[] ++ k → k` / `k ++ [] → k` | `List.nil_append` / `List.append_nil` | R10, R12 |
| use a generalized IH or an earlier lemma | `simp [iha, ihb, exec_append]` / `rw [compileAcc_eq]` | R5, R8 |
| a `∀`-lemma at one argument | `exact H []` or the term `H []` | R11 |
| finish by rewriting | `rw [L]` (closes with `rfl`) | R13 |
| see which lemmas `simp` used | `simp?` | |
