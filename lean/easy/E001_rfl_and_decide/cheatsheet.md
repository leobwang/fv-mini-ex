# E001 · rfl, decide, #eval: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** nothing; this is the first Lean exercise.
**New here:** a Lean file is a list of **declarations**. `def` defines a value or function, `theorem` and
`example` state a proposition and prove it, `#eval` runs a computation. A **proposition** (type `Prop`) is a
statement; a **proof** of `P` is a term whose type is `P`, and Lean checks the type. Two ways to prove an
equation or inequality between concrete values: **`rfl`** (both sides compute to the same value) and
**`decide`** (Lean evaluates the statement to `true`). `sorry` is a placeholder that Lean accepts with a
warning; the exercise is to replace every `sorry`.

## How to read an entry

Each entry is one command, term or tactic. It says what changes (the **goal**, the **context**, the
**goal list**, or only the **environment**: the set of names declared so far), lists the placeholders with
their types, then shows the state before and after.

- `Γ ⊢ G` is a proof state: hypotheses (the **context**) `Γ`, **goal** `G`. It appears in the infoview
  only inside a `by` block (R5). A cell shows only the hypotheses that matter.
- `n a : Nat` stand for any natural number, `f : Nat → Nat` for any function from `Nat` to `Nat`.
- "no goals" means the step closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Nat` | the natural numbers `0, 1, 2, …` |
| `3`, `50` | numerals; as `Nat` they are concrete values Lean can compute with |
| `3 * n`, `2 ^ 5` | multiplication and power on `Nat` |
| `double 3` | the function `double` applied to `3` (a space, no parentheses) |
| `a < b`, `a ≤ b` | the propositions "`a` is less than (or equal to) `b`" |
| `Bool`, `true`, `false` | the type of booleans and its two values |
| `b && c`, `b \|\| c`, `!b` | boolean and, or, not; they compute to `true` or `false` |
| `b = true` | the proposition "`b` evaluates to `true`" (a `Bool` itself is not a statement) |
| `(true && !false) = true` | the parentheses matter: `=` binds tighter than `&&`, `\|\|` and `!`, so without them Lean reads `true && !(false = true)` |
| `f : Nat → Nat` | `f` is a function from `Nat` to `Nat` |
| ⊢ in front of a statement | that statement is the goal: what is left to prove |

---

## Part 1 · `double`

Statement: give the body of `def double (n : Nat) : Nat`, a function that doubles its argument. The
theorem in Part 2 checks it on `3`.

**R1 · `def f (n : Nat) : Nat := e`** changes only the **environment**: it adds a function `f : Nat → Nat`.
`(n : Nat)` names the parameter and its type, the `: Nat` after it is the result type, and the body `e`
is an expression of type `Nat` in which `n` may appear. Arithmetic on `Nat`: `+`, `*`, `^`, and `-`, which
stops at `0` (`2 - 5 = 0`). Placeholders: `(n : Nat)`. Example: `def triple (n : Nat) : Nat := 3 * n`.

| Before | After |
|---|---|
| `triple` unknown | `triple : Nat → Nat`, `triple n` computes `3 * n` |

**R2 · `#eval e`** changes nothing: it computes `e` and prints the value in the infoview. Use it to test a
definition. It is not a proof. Placeholders: any expression `e`, for example `triple 4`.

| Before | After |
|---|---|
| `#eval triple 4` | infoview prints `12` |

**W1** (R1, R2): `def square (n : Nat) : Nat := n * n`, then `#eval square 7` prints `49`.

## Part 2 · `double_three`

Statement: `double 3 = 6`. Both sides are concrete: Lean can unfold `double`, substitute `n := 3` and
evaluate the body. When the result is the numeral `6`, `rfl` proves the equation.

**R3 · `example : P := proof`** (or `theorem name : P := proof`) states the proposition `P` and proves it
with the term `proof`. `theorem` also gives the fact a name for later use; `example` is anonymous. The
statement is everything between the first `:` and `:=`. Placeholders: `(P : Prop)`, for instance
`(a : Nat) : a = a`, proved by `rfl` (R4).

| Before | After |
|---|---|
| `example (a : Nat) : a = a := rfl` | accepted: Lean checks that `rfl` has type `a = a` |

**R4 · `rfl`** (as a term after `:=`) **closes** `a = b` when `a` and `b` compute to the same value. It
unfolds definitions and evaluates arithmetic. Placeholders: `(a b : Nat)` closed enough to evaluate, e.g.
`triple 3 = 9`: `triple 3` unfolds to `3 * 3`, which evaluates to `9`. `rfl` only proves `=`, never `<`.

| Before | After |
|---|---|
| `example : triple 3 = 9 := rfl` | accepted: both sides evaluate to `9` |

As a term, `rfl` shows no goal. The same proof written inside `by` (R5) shows it, as in W2:

| Before | After |
|---|---|
| `⊢ square 4 = 16` | no goals |

**R5 · `by tac`** switches from a term to **tactic mode**: the goal appears in the infoview as `⊢ P`, and
each tactic changes it until none is left. `rfl` is also a tactic, so `:= rfl` and `:= by rfl` do the same.
Placeholders: `(f : Nat → Nat) (a : Nat)`; `rfl` works even on symbolic values when both sides are the same.

| Before | After |
|---|---|
| `f : Nat → Nat, a : Nat ⊢ f a = f a` | no goals |

## Part 3 · `small_lt`

Statement: `2 ^ 5 < 50`. This is an inequality, so `rfl` does not apply. It is a statement about concrete
numbers that Lean can evaluate: `decide`.

**R6 · `decide`** **closes** a decidable proposition about concrete values: `<`, `≤`, `=`, `≠` on `Nat`,
equalities of `Bool`, and `∧`, `∨`, `¬` of those. Lean evaluates the statement to a `Bool`; if it is `true`
the goal is closed, if `false` the tactic fails. It needs no variables in the goal. Placeholders: none
(concrete numerals), e.g. `3 ^ 3 < 30`.

| Before | After |
|---|---|
| `⊢ 3 ^ 3 < 30` | no goals |

`decide` unfolds definitions too (W3):

| Before | After |
|---|---|
| `⊢ square 5 ≤ triple 9` | no goals |

**W2** (R4, R5, R6): `square 4 = 16` is proved by `rfl`, by `by rfl`, and by `by decide`.

## Part 4 · `bool_fact`

Statement: `(true && !false) = true`. The left side is a `Bool` expression that evaluates to a value; the
statement says that value is `true`. Evaluate it in your head, then pick `rfl` (R4) or `decide` (R6).

**R7 · `&&`, `||`, `!` on `Bool`** are functions that compute: `true && b = b`, `false && b = false`,
`true || b = true`, `false || b = b`, `!true = false`, `!false = true`. So `rfl` closes `e = true` when the
`Bool` expression `e` evaluates to `true`. Each operator computes by looking at its first argument, so a
rule such as `true && b = b` holds by `rfl` even for an unknown `b`. Placeholders: `(b : Bool)`, or concrete
`Bool` values.

| Before | After |
|---|---|
| `b : Bool ⊢ (true && b) = b` | no goals |
| `⊢ (!(false && true)) = true` | no goals |

**W4** (R7 with R6): `decide` closes the same kind of goal.

| Before | After |
|---|---|
| `⊢ (true && !(true && false)) = true` | no goals |

---

## Traps

- `sorry` makes a file compile with a warning ("declaration uses 'sorry'"); it is not a proof. The checker
  counts a theorem as solved only when no `sorry` is left.
- `rfl` proves only equations. On `2 ^ 5 < 50` it fails, with the confusing message "The left-hand side
  `2 ^ 5` is not definitionally equal to the right-hand side `50`"; use `decide`.
- Keep the parentheses in `(b && c) = true`. Without them `=` is applied first and the statement means
  something else.
- `decide` needs concrete values. On a goal with a variable, such as `n + 0 = n` for an arbitrary `n`, it
  fails.
- `rfl` fails if the two sides compute to different values: check a definition with `#eval` first (R2).
- `#eval` prints a value but proves nothing; a `#eval` line is not a substitute for a theorem.
- Application is a space: `double 3`. Write `double (n + 1)` with parentheses when the argument is itself an
  expression; `double n + 1` means `(double n) + 1`.
- `Nat` subtraction stops at `0`: `3 - 5 = 0`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| define a function on `Nat` | `def f (n : Nat) : Nat := e` | R1 |
| test a definition | `#eval f 3` | R2 |
| state and prove a fact | `theorem name : P := proof` / `example : P := proof` | R3 |
| equation of concrete values | `rfl` | R4 |
| see the goal in the infoview | `:= by tac` | R5 |
| `<`, `≤`, `≠`, `=` on concrete numbers | `by decide` | R6 |
| `Bool` expression `= true` | `rfl` or `by decide` | R7 |
| see the state | infoview (cursor after a tactic) | |
