# E002 · Factorial by pattern matching: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** E001 (`def`, `theorem`/`example`, `rfl`, `decide`, `#eval`). **New here:** defining a function
on `Nat` by `match` with the two patterns `0` and `k + 1`; **structural recursion** (the function calls
itself on `k`, the part of `k + 1` the pattern names); and proving facts about such a function by
computation with `rfl`, both on numerals and on a symbolic `n + 1`. No library lemmas.

## How to read an entry

Each entry is one term or one tactic. It says what changes (**goal**, **context**, or **goal list**), lists
the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses (the **context**) `Γ`, **goal** `G`. When the goal is a type such as
  `Nat` instead of a statement, "prove `G`" means "produce a value of type `G`": that is what a `def` body does.
- `by` switches to tactic mode, where the infoview shows the proof state; `exact t` closes the goal with the
  term `t`. E003 introduces both properly; here they only make the goal of a `def` body visible.
- Placeholders: `n k : Nat` are arbitrary natural numbers. "no goals" means the step closed the goal.
- All entries use the guide's `tri n = 0 + 1 + ⋯ + n`, defined by `| 0 => 0 | k + 1 => (k + 1) + tri k`.
  In the exercise, `fact` plays the role of `tri`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## `Nat`, patterns and structural recursion in one paragraph

`Nat` is built from two constructors: `0` and "successor", written `k + 1`. Every natural number is exactly
one of `0` or `k + 1` for a unique `k`, so a `match n with | 0 => a | k + 1 => b` covers all `n`, and in the
second arm `k` is the predecessor of `n` (R1, R2). A function may call itself in its own body only on a
**structurally smaller** argument: a variable bound by the pattern, such as `k` inside `k + 1` (R2). Lean then
knows the recursion ends (`n, n − 1, …, 0`) and accepts the definition without any proof of termination.
Because such a definition is a computation, `tri 0` *is* `0` and `tri (n + 1)` *is* `(n + 1) + tri n` by
unfolding, so `rfl` proves these equations (R3–R5).

## Reading the goals

| You see | It means |
|---|---|
| `Nat` (as the goal, in a `def` body) | produce a natural number |
| `fact 0`, `fact 5` | `fact` applied to a numeral; computes all the way down |
| `fact (n + 1)` | `fact` applied to the successor of an unknown `n`; unfolds exactly one step (R4) |
| `(n + 1) * fact n` | the right side of `fact_succ`. `*` binds tighter than `+`, so the parentheses are needed |
| `n + 1 + tri n` | `(n + 1) + tri n`: `+` groups to the left, so Lean drops these parentheses when printing |
| `n k : Nat` | two hypotheses of the same type on one line: `n : Nat` and `k : Nat` |
| `\| k + 1 => …` | a `match` arm: the pattern `k + 1` fits every nonzero number and names its predecessor `k` |

---

## Part 1 · `fact` (definition body)

Statement: `def fact (n : Nat) : Nat`. You write the body. `fact_zero` and `fact_succ` pin it down: `fact 0` is
`1`, and `fact (n + 1)` is `(n + 1) * fact n`. Match on `n` (R1) and, in the `k + 1` arm, call `fact k` (R2).

**R1 · `match n with | 0 => a | k + 1 => b`** is a **term**: it inspects whether `n` is `0` or a successor
`k + 1` and returns that arm's value. The two arms cover every `Nat`; a missing arm is an error. In a `def` body
you write it directly after `:=`, with each arm on its own line starting with `|`. As a tactic,
`exact match n with …` **closes** a goal of type `Nat`. Placeholders: `(n : Nat)`; `a b : Nat` are the arm
values, and `b` may use `k`.

| Before | After |
|---|---|
| `n : Nat ⊢ Nat` | no goals |

**R2 · the arm `k + 1 => …`** changes the **context** for that arm's value: it gains `k : Nat`, the
predecessor of `n` (no hypothesis `n = k + 1` is added; `n` stays in the context unchanged). The value
may call the function being defined on `k`, as `tri` does with `tri k`: that is
**structural recursion**, and Lean accepts it because `k` is a piece of the pattern. A call on `n` itself or on
`n - 1` is rejected (Lean cannot see that `n - 1` is smaller). In the guide, `?_` leaves the value as a goal so
that you can see the arm's context. Placeholders: `(n : Nat)`.

| Before | After `refine match n with \| 0 => 0 \| k + 1 => ?_` |
|---|---|
| `n : Nat ⊢ Nat` | `n k : Nat ⊢ Nat` |

## Part 2 · `fact_zero`

Statement: `fact 0 = 1`. The argument is the numeral `0`, so `fact 0` unfolds to the `0` arm (R3).

**R3 · `rfl` on `f 0 = v`** **closes** the goal: `rfl` proves `a = b` when both sides compute to the same value;
`tri 0` unfolds to the `match` with `n := 0`, which picks the `0` arm. In term mode write `:= rfl`, as in E001.

| Before | After |
|---|---|
| `⊢ tri 0 = 0` | no goals |

## Part 3 · `fact_succ`

Statement: `∀ n, fact (n + 1) = (n + 1) * fact n`. Here `n` is a variable, yet `rfl` still works (R4).

**R4 · `rfl` on `f (n + 1) = …`** **closes** the goal by **one** step of unfolding. `n` is unknown, but
`n + 1` has the shape of the pattern `k + 1` (with `k := n`), so `tri (n + 1)` unfolds to the second arm's
value `(n + 1) + tri n`. The step stops there: `tri n` with unknown `n` cannot unfold further. So the right
side must be the arm's value **written the same way**. Placeholders: `(n : Nat)`.

| Before | After |
|---|---|
| `n : Nat ⊢ tri (n + 1) = n + 1 + tri n` | no goals |

W1 does the same for `pow2 : Nat → Nat`, defined by `| 0 => 1 | k + 1 => 2 * pow2 k`:

| Before | After |
|---|---|
| `n : Nat ⊢ pow2 (n + 1) = 2 * pow2 n` | no goals |

## Part 4 · `fact_five`

Statement: `fact 5 = 120`. A numeral argument: everything computes (R5).

**R5 · `rfl` (or `by decide`) on `f 5 = v`** **closes** the goal by full evaluation: `tri 5` unfolds five times
down to `tri 0`, and the numbers are added. `decide` (E001) also works, since `=` on `Nat` with concrete values is
decidable. Check the value with `#eval tri 5` first (W1 does this for `pow2 10`).

| Before | After |
|---|---|
| `⊢ tri 5 = 15` | no goals |

W2, structural recursion on a list (`| [] => 0 | _ :: xs => 1 + len xs`, the call is on the tail `xs`):

| Before | After `decide` |
|---|---|
| `⊢ len [7, 8, 9] = 3` | no goals |

---

## Traps

- `k + 1 * fact k` parses as `k + (1 * fact k)`: `*` binds tighter than `+`. Write `(k + 1) * fact k`. With the
  wrong version `#eval` gives `fact 3 = 4` instead of `6`, and `fact_five` fails.
- Write the arm in the order `fact_succ` uses. `rfl` unfolds `fact (n + 1)` to exactly the arm's value, and with
  `n` unknown it cannot reorder a product: an arm `fact k * (k + 1)` computes the same numbers, but `rfl` on
  `fact_succ` then fails (term `rfl`: "Type mismatch"; `by rfl`: "is not definitionally equal to the
  right-hand side"), because `a * b = b * a` is a theorem, not a computation.
- Recurse on the pattern variable `k`, not on `n - 1`: an arm `| n => n * fact (n - 1)` (even after a `0` arm) is
  not structural recursion, and Lean rejects it with "fail to show termination" (E026 shows how to justify such
  calls). The pattern `k + 1` is what makes the call structural.
- The pattern is `k + 1`, with the `+ 1` on the right (`| 1 + k => …` is rejected: "Invalid
  pattern(s)"); any fresh name works (`k`, `m`, even `n`, which then hides the outer `n` inside that arm).
- `#eval fact 5` before proving: if it does not print `120`, no proof will help.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| define `f : Nat → Nat` by cases | `match n with \| 0 => a \| k + 1 => b` | R1 |
| the same without naming the argument | `def f : Nat → Nat \| 0 => a \| k + 1 => b` | W1 |
| recursive call | `f k` inside the `k + 1` arm (structural recursion) | R2 |
| see what an arm's value can use | `refine match n with \| 0 => … \| k + 1 => ?_` | R2 |
| `f 0 = v` | `rfl` | R3 |
| `f (n + 1) = (arm value)` with `n` a variable | `rfl` (right side written exactly as the arm) | R4 |
| `f 5 = v` | `rfl` or `by decide` | R5 |
| test a definition | `#eval f 5` | W1 |
| see the state | `by` + infoview | |
