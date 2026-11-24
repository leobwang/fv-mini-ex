# M039 · Except evaluator: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): inductive types, functions defined by pattern matching,
`induction`/`cases`, `obtain`, `∃` and `⟨w, proof⟩`, `rfl`, `exact`, `rw`, `simp`. **New here:** the
`Except ε α` type as a monad (a computation that returns a value of type `α` or fails with an error of
type `ε`), `do` notation with `←`, `pure`, `throw`, and the simp lemmas that run a `do` block on `.ok`
and `.error`. No Mathlib.

The guide works on its own objects, not on `Expr`/`eval`/`NoDiv`:

| Guide object | Plays the role of | Definition |
|---|---|---|
| `Tm` (`lit n`, `sub a b`, `oops`) | `Expr` (`num n`, `add a b`, `div a b`) | a type with two recursive arguments in one constructor |
| `run : Tm → Except String Nat` | `eval` | `sub` fails with `"negative"` when `x < y`; `oops` always fails |
| `Clean : Tm → Prop` | `NoDiv` | `True` at `lit`, `∧` at `sub`, `False` at `oops` |
| `ok_bind`, `error_bind`, `map_ok`, `map_error` | the same four lemmas in `problem.lean` | copied verbatim (they are given, not part of the spec) |

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- Placeholders are Lean binders: `{α β : Type}` are any types; `(m : Except String α)` any computation.
- A `do` block in the infoview spans several lines; such states are shown in a `text` block under the
  table, copied from the infoview.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Except String Int` | a computation that gives `Except.ok v` (`v : Int`) or `Except.error msg` (`msg : String`) |
| `Except.ok v`, `.ok v` | success with value `v`; `.ok v` is short for `Except.ok v` when the type is known |
| `Except.error msg` | failure with message `msg` |
| `pure v` | in `Except`, by definition `Except.ok v` (R2) |
| `throw msg` | in `Except String`, by definition `Except.error msg` (R2) |
| `do let x ← m; rest` (on several lines) | `m >>= fun x => rest`: run `m`; on `.ok v` continue with `rest` where `x := v`; on `.error e` the whole block is `.error e` |
| `m >>= f` | "bind": `Except.ok v >>= f = f v`, `Except.error e >>= f = Except.error e` (R6, R14) |
| `f <$> m` | "map": apply `f : α → β` to the value inside `m`, keep an error as it is (R8) |
| `HAdd.hAdd x` | the function `fun y => x + y` (`HAdd.hAdd` is the name behind `+`); appears as `HAdd.hAdd x <$> m` after R7 |
| `(do …) = v` | an equation whose left side is a `do` block; Lean wraps the block in parentheses and indents `= v` |
| `let _ ← m` | a bind whose value is no longer used (here after `if True` picked the `throw` branch) |
| `if True then a else b` | an `if` whose test `simp` has already decided; `↓reduceIte` then picks `a` (R13) |
| `a.add b`, `Expr.num 0` | the expressions `Expr.add a b` and `Expr.num 0`: Lean prints `Expr.add a b` as `a.add b` |
| `iha : NoDiv a → eval a = …` | an induction hypothesis that needs `NoDiv a` before it gives the equation (R1) |
| `a_ih✝` | an IH you did not name (the `div` case); `✝` marks a name you cannot type |
| `x / y` on `Int` | integer division; Lean defines `x / 0 = 0`, which is why `eval` tests `y = 0` itself |
| `case add`, `case ok` | the goal for that constructor / that result |

---

## Part 1 · `eval_noDiv`

Statement: if `e` contains no division (`NoDiv e`) then `eval e = .ok (evalPure e)`: the monadic
evaluator succeeds with the value of the plain evaluator `evalPure`. Induct on `e`; the `h : NoDiv e`
in the context comes along into each case.

### Induction with a hypothesis about the induction variable

**R1 · `induction t with | lit n => … | sub a b iha ihb => … | oops => …`** changes the **goal list**:
one goal per constructor of `Tm`, one IH per recursive argument. Because `h : Q t` mentions `t`, Lean
reverts `h` before inducting and reintroduces it in each case, so `h` becomes `Q (Tm.lit n)` etc. and each
IH is an implication `Q a → P a`: to use it, apply it to a proof of `Q a` (R5). Placeholders:
`(P Q : Tm → Prop) (t : Tm) (h : Q t)`.

| Before | After |
|---|---|
| `t : Tm, h : Q t ⊢ P t` | `n : Nat, h : Q (Tm.lit n) ⊢ P (Tm.lit n)` |
| | `iha : Q a → P a, ihb : Q b → P b, h : Q (a.sub b) ⊢ P (a.sub b)` |
| | `h : Q Tm.oops ⊢ P Tm.oops` |

**R2 · `rfl`** **closes** an equation that holds by computation. In `Except`, `pure x` is by definition
`Except.ok x` and `throw e` is `Except.error e`; a function applied to a constructor unfolds by its
defining equation. This is the `num` case of Part 1 and the last step of Part 2. `simp` does **not**
use these two definitional facts, so it can leave `throw e = Except.error e` behind. Placeholders:
`{α : Type} (x : α) (e : String) (n : Nat)`.

| Before | After |
|---|---|
| `⊢ pure x = Except.ok x` | closed by `rfl` |
| `⊢ throw e = Except.error e` | closed by `rfl` |
| `⊢ run (Tm.lit n) = Except.ok n` | closed by `rfl` |

**R3 · `obtain ⟨ha, hb⟩ := h`** changes the **context**. `Clean (.sub a b)` is by definition
`Clean a ∧ Clean b`; `obtain` unfolds the definition to find the `∧` and splits it. Placeholders:
`(a b : Tm) (G : Prop)`.

| Before | After |
|---|---|
| `h : Clean (a.sub b) ⊢ G` | `ha : Clean a, hb : Clean b ⊢ G` |

### Unfolding and computing a `do` block

**R4 · `simp only [run]`** changes the **goal**: `run` applied to a constructor becomes that case's body,
here a `do` block. The same `simp [evalPure]` turns `evalPure (a.add b)` into `evalPure a + evalPure b`.
Placeholders: `(a b : Tm) (P : Except String Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (run (a.sub b))` | the `do` block below |

```text
⊢ P do
    let x ← run a
    let y ← run b
    if x < y then throw "negative" else pure (x - y)
```

**R5 · `simp only [iha ha]`** changes the **goal**. With `iha : Q a → f a = g a` and `ha : Q a`, the
term `iha ha` is the equation `f a = g a`, which `simp` (or `rw`) uses left to right. Pass several:
`simp [iha ha, ihb hb]`. Placeholders: `{α β : Type} (f g : α → β) (Q : α → Prop) (a : α)`.

| Before | After |
|---|---|
| `iha : Q a → f a = g a, ha : Q a ⊢ P (f a)` | `⊢ P (g a)` |

**R6 · `ok_bind`** (given in `problem.lean`) changes the **goal**:
`ok_bind : (Except.ok x >>= f) = f x`. A `let y ← Except.ok x` line disappears and `x` takes the place
of `y` in the rest of the block. Placeholders: `{α β : Type} (x : α) (k : α → Except String β)`.

| Before | After |
|---|---|
| the `do` block below | `⊢ P (k x)` |

```text
⊢ P do
    let y ← Except.ok x
    k y
```

**R7 · `bind_pure_comp`** (core Lean, a simp lemma, so plain `simp` uses it) changes the **goal**:
`bind_pure_comp : (m >>= fun y => pure (f y)) = f <$> m`. A block whose last line is `pure (…)` becomes
a map. In Part 1 this turns `let y ← Except.ok (evalPure b); pure (x + y)` into
`HAdd.hAdd x <$> Except.ok (evalPure b)` (`HAdd.hAdd x` is `fun y => x + y`), which R8 then computes. Placeholders:
`{α β : Type} (m : Except String α) (f : α → β)`.

| Before | After |
|---|---|
| the `do` block below | `⊢ P (f <$> m)` |

```text
⊢ P do
    let y ← m
    pure (f y)
```

**R8 · `map_ok`** (given) changes the **goal**: `map_ok : (f <$> Except.ok x) = Except.ok (f x)`.
Placeholders: `{α β : Type} (x : α) (f : α → β)`.

| Before | After |
|---|---|
| `⊢ P (f <$> Except.ok x)` | `⊢ P (Except.ok (f x))` |

### The impossible case

**R9 · `exact absurd h id`** **closes** any goal when the type of `h` unfolds to `False`.
`absurd : a → ¬a → b`, and `¬a` is `a → False`. Since `Clean .oops` is `False` by definition, `id` has
type `¬ Clean .oops`. `exact h.elim` works the same way. Placeholders: `(G : Prop)`.

| Before | After |
|---|---|
| `h : Clean Tm.oops ⊢ G` | closed |

---

## Part 2 · `div_zero_fails`

Statement: for every `a`, `eval (.div a (.num 0))` is `.error msg` for some `msg`. You cannot compute
`eval a`, so split on its result: if it fails, the whole block fails with the same message (R14); if
it succeeds, the test `0 = 0` makes the block `throw "division by zero"` (R12, R13).

**R10 · `cases h : m with | error e => … | ok x => …`** changes the **goal list and the context**: one
goal per constructor of `Except`, and `h` records which one `m` is, so `simp [h]` can replace `m`.
Without `h :` the case split forgets that the value came from `m`. Placeholders:
`{α : Type} (m : Except String α) (G : Prop)`.

| Before | After |
|---|---|
| `m : Except String α ⊢ G` | `e : String, h : m = Except.error e ⊢ G`, `x : α, h : m = Except.ok x ⊢ G` |

**R11 · `exact ⟨w, by tac⟩`** **closes** `∃ y, P y`: `w` is the witness and `by tac` proves `P w`. It is
`refine ⟨w, ?_⟩` (TACTIC_STATES) followed by `tac`. Placeholders: `(P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ ∃ y, P y` | closed |

**R4 again:** `simp [eval]` unfolds the `div` case; `eval (.num 0)` unfolds to `pure 0`.

**R12 · `pure_bind`** (core Lean, a simp lemma) changes the **goal**: `pure_bind : (pure x >>= f) = f x`,
the `pure` version of R6. Placeholders: `{α β : Type} (x : α) (k : α → Except String β)`.

| Before | After |
|---|---|
| the `do` block below | `⊢ P (k x)` |

```text
⊢ P do
    let y ← pure x
    k y
```

**R13 · `↓reduceIte`** (a *simproc*, a built-in simplification procedure that `simp` runs by itself)
changes the **goal**: `if c then a else b` becomes `a` when `simp` proves `c`, `b` when it refutes `c`.
Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `⊢ P (if 0 = 0 then a else b)` | `⊢ P a` |

**R14 · `error_bind`** (given) changes the **goal**: `error_bind : (Except.error e >>= f) = Except.error e`.
A failure skips the rest of the block. Placeholders: `{α β : Type} (e : String) (k : α → Except String β)`.

| Before | After |
|---|---|
| the `do` block below | `⊢ P (Except.error e)` |

```text
⊢ P do
    let y ← Except.error e
    k y
```

In the `ok` case R6 runs instead of R14, and `simp` stops at `throw "…" = Except.error "…"`: close it
with `rfl` (R2).

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1.** `halve n` is `pure (n / 2)` on even `n`, `throw "odd"` otherwise; `quarter n` halves twice in a
`do` block. `halve 4 = .ok 2` and `quarter 6 = .error "odd"` hold by `rfl` (R2): `halve 6 = .ok 3`,
then `halve 3` fails and the error is the result.

**W2: a closed term.** `simp only [run]` (R4), then `simp` (R12, R13), then `rfl` (R2):

```lean-goal
⊢ run ((Tm.lit 2).sub (Tm.lit 5)) = Except.error "negative"
⊢ throw "negative" = Except.error "negative"
```

The state between the two lines is

```text
⊢ (do
      let x ← pure 2
      let y ← pure 5
      if x < y then throw "negative" else pure (x - y)) =
    Except.error "negative"
```

**W3: split on a sub-result.** `run (.sub a (.lit 0)) = run a`. `cases h : run a` (R10), then
`simp [run, h]` closes both goals (R4, R12, R13, then R14 or R6):

| Before | After |
|---|---|
| `a : Tm ⊢ run (a.sub (Tm.lit 0)) = run a` | `h : run a = Except.error e ⊢ run (a.sub (Tm.lit 0)) = Except.error e`, `h : run a = Except.ok x ⊢ run (a.sub (Tm.lit 0)) = Except.ok x` |

---

## Traps

- `simp` leaves `throw "division by zero" = Except.error "division by zero"`: true by definition but not
  a simp lemma. Finish with `; rfl` (R2).
- `cases eval a` without `h :` gives goals that no longer mention `eval a`, and `simp [eval]` cannot use
  the result. Write `cases h : eval a with …` (R10).
- The IHs are implications (R1). `simp [iha]` rewrites only if `simp` can prove `NoDiv a` by itself,
  which it cannot: it reports `iha` as unused and stops at `(do let x ← eval a; HAdd.hAdd x <$> eval b) = …`.
  Split `h` with R3 and give `simp [iha ha, ihb hb]` (R5).
- If you drop `evalPure` from the `simp` list, `simp` reduces `.ok u = .ok v` to `u = v` (`Except.ok.injEq`)
  and stops at `evalPure a + evalPure b = evalPure (a.add b)`; add `evalPure` (R4).
- `map_error` (given) is for `f <$> Except.error e`; the solution does not need it, but `simp` may use it.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induct with `h : NoDiv e` in context | `induction e with \| num n => … \| add a b iha ihb => … \| div a b => …` | R1 |
| `pure x = .ok x`, `throw e = .error e`, unfold-and-compare | `rfl` | R2 |
| split `h : NoDiv (.add a b)` | `obtain ⟨ha, hb⟩ := h` | R3 |
| unfold `eval` / `evalPure` at a constructor | `simp [eval, evalPure]` | R4 |
| use an implication IH | `simp [iha ha]` | R5 |
| run `let x ← .ok v` / `← pure v` / `← .error e` | `simp` (`ok_bind`, `pure_bind`, `error_bind`) | R6, R12, R14 |
| `do … pure (f y)` → `f <$> m` → `.ok (f v)` | `simp` (`bind_pure_comp`, `map_ok`) | R7, R8 |
| `h` unfolds to `False` | `exact absurd h id` | R9 |
| split on the result of `eval a` | `cases h : eval a with \| error e => … \| ok x => …` | R10 |
| prove `∃ msg, …` | `exact ⟨msg, by simp [eval, h]⟩` | R11 |
| `if 0 = 0 then a else b` → `a` | `simp` (`↓reduceIte`) | R13 |
| see the state | infoview | |
