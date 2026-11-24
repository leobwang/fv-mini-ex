# M012 · Depth-indexed stack code: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `induction`, `simp`, `rw`, `rfl`, `omega`, `<;>`,
`all_goals`. **New here:** indexed families (types such as `Code n m` that carry numbers), dependent
pattern matching, induction on an indexed family, `fun_induction`, `simp_all`, and
`induction … generalizing`. Core Lean only: no Mathlib.

The guide works on its own Boolean stack machine (`Stack n`, `Op n m`, `Prog n m`, `simpl`), not on the
exercise's `Vec`, `Instr`, `Code`, `opt`.

## How to read an entry

Each entry is one tactic, or one definition unfolded with `simp only`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Prop`, or `P : {n m : Nat} → Prog n m → Prop` for a
  predicate on programs of any depth). The step changes only the part inside `P (…)`.
- Placeholders are written as Lean binders. `{n : Nat}` is an implicit argument: Lean fills it in from
  the other arguments' types.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Vec Nat n`, `Code n m`, `Instr n m` | a stack of exactly `n` naturals; code (instruction) taking depth `n` to depth `m`. The numbers are *indices*: part of the type, checked by Lean |
| `inductive Code : Nat → Nat → Type` | `Code` is a family of types, one for each pair of numbers; each constructor's result type (`Code n n`, `Code n k`) says which member it builds |
| `def f : {n m : Nat} → Code n m → …` with arms `\| _, _, .cons i c => …` | `f` takes the depths as implicit arguments; each arm matches them with `_` (Lean works them out from the constructor) and then matches the code |
| `.cons i c`, `.nil` | `Code.cons i c`, `Code.nil` (or `Vec.cons`, `Vec.nil`): the expected type tells Lean which `cons` |
| `c.run s`, `c.append d`, `a.eval` | `Code.run c s`, `Code.append c d`, `Expr.eval a` (dot notation: the namespace comes from the type of `c`) |
| `a.add b` | the expression `Expr.add a b`, so `(a.add b).eval` is `Expr.eval (Expr.add a b)` |
| `Code.nil.run s` | `Code.run Code.nil s`; `simp`/`rfl` reduce it to `s` |
| `compile (n := 0) e` | `compile e` with its implicit start depth `n` set to `0`; `compile e : Code n (n + 1)` for every `n` |
| `n✝`, `x✝¹`, `c✝`, `ih1✝` | inaccessible names: Lean made them up (after `induction` on an index, `fun_induction`, `intros`). You cannot type them; `simp_all` still uses them |
| `x✝.succ` | `x✝ + 1` |
| `a ≍ b` | `HEq a b`, heterogeneous equality: `a` and `b` are equal although Lean cannot yet see that their types are equal (here `Code m k` vs `Code (n + 1) k`) |
| `∀ (a b : Nat) (c : …), … → i✝ ≍ Instr.push a → … → False` | "this case is not an earlier arm of the match": the code does not start with that pattern |
| `case cons`, `case case3` | the goal for constructor `cons`; the goal for the third arm of the function (after `fun_induction`) |
| `!b`, `x && y` (guide only) | Boolean not and Boolean and, on the guide's `Bool` stacks |
| `∀ {n : Nat} (s : Vec Nat n), …` | holds at every depth `n` (implicit: `iha s` works for any `s`, Lean infers `n`) |

---

## Part 1 · `run_append`

Statement: `(c.append d).run s = d.run (c.run s)`: running `c` followed by `d` is running `c`, then
`d` on the result. `c : Code n m`, `d : Code m k`, `s : Vec Nat n`.

**R1 · `induction p with | stop => ?_ | seq o p ih => ?_`** changes the **goal list and the context**:
one goal per constructor of `Prog`. Because `p : Prog n m` has indices, Lean reverts and re-introduces
every hypothesis whose type mentions them (`s : Stack n`), so the IH holds for **all** stacks. The
original `n m` stay as unused names; the case's own depths are `n✝ m✝ k✝`. `?_` leaves each case open
under the name you gave. Placeholders: `(P : {n m : Nat} → Prog n m → Stack n → Prop)`,
`{n m : Nat} (p : Prog n m) (s : Stack n)`. In the exercise the same happens to `d` and `s`, so
`ih : ∀ (d : Code k✝ k) (s : Vec Nat m✝), …`.

| Before | After |
|---|---|
| `p : Prog n m, s : Stack n ⊢ P p s` | `s : Stack n✝ ⊢ P Prog.stop s` and, with `ih : ∀ (s : Stack m✝), P p s`, `o : Op n✝ m✝, p : Prog m✝ k✝, s : Stack n✝ ⊢ P (Prog.seq o p) s` |

**R2 · `simp only [f]` on a constructor** changes the **goal**: one defining equation of `f` fires. A
function defined by pattern matching computes only where its argument is a constructor
(`Prog.seq o p`, `Code.cons i c`), never on a variable `p`. If both sides then agree, `simp` closes the
goal; in the `nil` case of `run_append` both sides compute to `d.run s`, so `rfl` closes it directly.
Placeholders: `{n m k : Nat} (o : Op n m) (p : Prog m k) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (Prog.seq o p).size` | `⊢ P (p.size + 1)` |

**R3 · `simp only [ih]` with a `∀` hypothesis** changes the **goal**: `simp` instantiates the
quantifier itself (`s := t s`) wherever the left side occurs, then closes `g (t s) = g (t s)` by `rfl`.
Placeholders: `{n m : Nat} (f g : Stack n → Stack m) (t : Stack n → Stack n)`,
`(ih : ∀ (s : Stack n), f s = g s)`. In Part 1 the IH is needed at the stack `i.run s`.

| Before | After |
|---|---|
| `s : Stack n ⊢ f (t s) = g (t s)` | no goals |

---

## Part 2 · `opt_correct`

Statement: `(opt c).run s = c.run s`: the peephole optimiser preserves the result on every stack.

**R4 · `simp only [Op.exec]` on a forced stack shape** changes the **goal**: a dependent match fires.
`Instr.run .add` (here `Op.exec .both`) matches the stack against `.cons b (.cons a s)` and has no error
case: its type `Vec Nat (n + 2)` already guarantees two elements. The equation fires only when the
stack is *written* with two constructors on top, which is what two pushes produce. On a variable stack
`s : Stack (n + 2)` it does nothing. Placeholders: `{n : Nat} (x y : Bool) (st : Stack n)`,
`(P : Stack (n + 1) → Prop)`.

| Before | After |
|---|---|
| `⊢ P (Op.both.exec (Stack.top y (Stack.top x st)))` | `⊢ P (Stack.top (x && y) st)` |

**R5 · `fun_induction simpl p`** changes the **goal list and the context**: one goal per arm of the
function, in the order of its equations, with an IH (`ih1✝`) for each recursive call on that arm. The
catch-all arm also gets hypotheses saying the earlier arms did not match (`x✝ : ∀ x y p, … ≍ … → False`).
Plain `induction` follows the constructors of `Prog` instead, and then `opt` does not unfold until you
split the next two instructions by hand. Placeholders: `(P : {n m : Nat} → Prog n m → Prop)`,
`{n m : Nat} (p : Prog n m)`.

| Before | After |
|---|---|
| `p : Prog n m ⊢ P (simpl p)` | `ih1✝ : P (simpl p✝) ⊢ P (Prog.seq (Op.lit (x✝ && y✝)) (simpl p✝))`, `ih1✝ : P (simpl p✝) ⊢ P (Prog.seq o✝ (simpl p✝))`, `⊢ P Prog.stop` |

In the exercise `fun_induction opt c` gives four goals: `case1` (push; push; add), `case2`
(push; push; mul), `case3` (any other `cons`, with two "not an earlier arm" hypotheses) and `case4`
(`nil`). The IH is `ih1✝ : ∀ (s : Vec Nat _), (opt c✝).run s = c✝.run s`: `s` was generalized as in R1.

**R6 · `simp_all`** changes the **goal and the context**: it simplifies every hypothesis and the goal,
using each hypothesis to rewrite the others, and closes the goal if it can. It uses inaccessible
hypotheses (`a✝`, `ih1✝`) that you cannot name in `simp [ih]`. Add definitions to unfold:
`simp_all [Code.run, Instr.run]`. Placeholders: `(f g : Nat → Nat) (P : Nat → Prop)`; `intros` first
moves both premises into the context without names.

| Before | After |
|---|---|
| `⊢ (∀ (x : Nat), f x = g x) → P (g 3) → P (f 3)` | after `intros`: `a✝ : P (g 3) ⊢ P (f 3)` (and `a✝¹ : ∀ (x : Nat), f x = g x`) |
| `a✝ : P (g 3) ⊢ P (f 3)` | no goals |

---

## Part 3 · `opt_len`

Statement: `(opt c).len ≤ c.len`: the optimiser never lengthens code. Same shape as Part 2 (R5, R6),
with `Code.len` unfolded instead of `run`; what is left is arithmetic.

**R7 · `omega`** **closes** a goal of linear arithmetic over `Nat` or `Int` (`+`, `-`, `≤`, `<`,
numerals, multiplication by numerals), using the hypotheses in the context. Placeholders: `(x y : Nat)`.

| Before | After |
|---|---|
| `h : x ≤ y ⊢ x ≤ y + 2` | no goals |

After `simp_all [Code.len]` the two folding arms are left exactly in this form (W2):
`ih1✝ : (opt c✝).len ≤ c✝.len ⊢ (opt c✝).len ≤ c✝.len + 2`.

---

## Part 4 · `compile_correct`

Statement: `(compile e).run s = .cons e.eval s`: compiled code, run on any stack `s` of any depth `n`,
pushes exactly the value of `e`.

**R8 · `induction l generalizing n`** changes the **context**: the IH quantifies over `n` and over every
hypothesis that mentions it (`s : Stack n`). This is needed because the code of `add a b` runs
`compile b` on the stack that `compile a` left, which has depth `n + 1`: the IH for `b` is used at a
different depth than the goal's. Without `generalizing n` the IH is stuck at the goal's own `n` and `s`.
Placeholders: `(P : {n : Nat} → List Bool → Stack n → Prop)`, `{n : Nat} (l : List Bool) (s : Stack n)`.

| Tactic | Before | After (the `cons` case) |
|---|---|---|
| `induction l generalizing n with …` | `⊢ P l s` | `ih : ∀ {n : Nat} (s : Stack n), P bs s` and `s : Stack n ⊢ P (b :: bs) s` |
| `induction l with …` | `⊢ P l s` | `ih : P bs s ⊢ P (b :: bs) s` |

**R9 · `rw [ih]` at another depth** changes the **goal**: the implicit `{n}` of
`ih : ∀ {n : Nat} (s : Stack n), f s = g s` is found by matching `f s` in the goal, here with
`s : Stack (n + 1)`. Placeholders: `(f g : {n : Nat} → Stack n → Stack (n + 1))`,
`(P : Stack (n + 2) → Prop)`. In Part 4, `iha` is used at depth `n`, `ihb` at depth `n + 1`.

| Before | After |
|---|---|
| `s : Stack (n + 1) ⊢ P (f s)` | `⊢ P (g s)` |

`run_append` (Part 1) is the rewrite rule that splits `compile (a.add b)` into its three pieces:
`rw [run_append]` or `simp [run_append]` (TACTIC_STATES, "Rewriting and simplifying").

---

### Worked combinations (W1–W3, on the guide's Boolean machine)

**W1** chains R1 → R2 → R3 → R7: `(p.cat q).size = p.size + q.size` by induction on `p`. After R1 the
`seq` case has `ih : ∀ (q : Prog k✝ k), (p.cat q).size = p.size + q.size`, with `q` generalized:

```lean-goal
⊢ ((Prog.seq o p).cat q).size = (Prog.seq o p).size + q.size
```

**W2** chains R5 → R6 → R7: `(simpl p).size ≤ p.size`. After `all_goals simp_all [Prog.size]` only the
folding arm is left:

```lean-goal
⊢ (simpl p✝).size ≤ p✝.size + 2
```

**W3** runs a concrete program: R2 for `Prog.exec`, then R4 for `Op.exec`:

```lean-goal
⊢ (Prog.seq (Op.lit x) (Prog.seq (Op.lit y) (Prog.seq Op.both Prog.stop))).exec st = Stack.top (x && y) st
⊢ Op.both.exec ((Op.lit y).exec ((Op.lit x).exec st)) = Stack.top (x && y) st
```

The exercise's analogue: `(Code.cons (.push 2) (.cons (.push 3) (.cons .add .nil))).run .nil = .cons 5 .nil`
holds by `rfl`, and so does `(compile (n := 0) (.add (.num 2) (.num 3))).run .nil = .cons 5 .nil`.

---

## Traps

- Do not add imports or leave search tactics (`exact?`, `apply?`, `try?`) in the file; they, `grind` and
  `solve_by_elim` are on the `BANNED:` line.
- Plain `induction c` on `opt_correct` stalls: in the `cons` case `opt (Code.cons i c)` does not unfold,
  because `opt` matches two more instructions deep. Use `fun_induction opt c` (R5).
- `induction e` without `generalizing n` gives an IH at depth `n` only; the `add` case needs it at
  `n + 1` (R8).
- After `fun_induction` the IH is `ih1✝`: you cannot write `simp [ih1✝]`. Use `simp_all` (R6), or name
  it with `rename_i`.
- `simp [Instr.run]` does nothing on a stack variable `s : Vec Nat (n + 2)`: the equation needs the
  stack written as `.cons b (.cons a s)` (R4). In this exercise the stack always comes from pushes.
- `t1 ; t2` runs `t2` on the first goal only. After `fun_induction`, use `<;>` or `all_goals`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction on `c : Code n m` (IH for all `d`, `s`) | `induction c with \| nil => ?_ \| cons i c ih => ?_` | R1 |
| compute a definition on a constructor | `simp only [Code.append, Code.run]`, or `rfl` | R2 |
| rewrite with a `∀` IH | `simp [ih]` | R3 |
| run `add`/`mul` on a pushed stack | `simp [Instr.run]` | R4 |
| one goal per arm of `opt` | `fun_induction opt c` | R5 |
| simplify with unnamed hypotheses | `simp_all [defs]` | R6 |
| linear `Nat` arithmetic | `omega` | R7 |
| IH at every depth | `induction e generalizing n` | R8 |
| IH at depth `n + 1` | `rw [ihb]` / `simp [ihb]` | R9 |
| split compiled code | `simp [compile, run_append]` | Part 1 |
| run on all arms | `fun_induction opt c <;> tac` | TACTIC_STATES |
| see the state | infoview | |
