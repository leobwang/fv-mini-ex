# E011 · omega: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** E001 (`decide`), E003 (tactic mode, `exact`), E005 (`∧`, `constructor`), E009 (`rw`),
E010 (`simp`).
**New here:** the decision procedure `omega`, `Nat` truncated subtraction, `Int`, and the cast `↑` from
`Nat` to `Int`. `omega` proves any true statement of **linear integer arithmetic**: facts built from
variables of type `Nat` or `Int`, numerals, `+`, `-`, multiplication by a numeral, `/` and `%` by a numeral,
the comparisons `= ≤ < ≥ >`, and the connectives `∧ ∨ ¬ → ↔`. It reads every such hypothesis in the
context by itself, and either closes the goal or fails with "omega could not prove the goal". It never
leaves a changed goal behind, so every entry below goes from one state to "no goals".

## How to read an entry

Each entry is one call of `omega` on one kind of goal. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses (the **context**) `Γ`, **goal** `G`. A cell shows only the
  hypotheses that matter (the variables `a b : Nat` are left out).
- `a b c : Nat` are natural numbers `0, 1, 2, …`; `x y : Int` are integers `…, -1, 0, 1, …`.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `n m : Nat` | natural numbers, `0, 1, 2, …` |
| `x y : Int` | integers, negatives included |
| `n - m` with `n m : Nat` | **truncated** subtraction: `n - m = 0` whenever `m ≥ n`, e.g. `3 - 5 = 0` |
| `x - y` with `x y : Int` | ordinary subtraction: `3 - 5 = -2` |
| `↑n` | the `Nat` `n` cast into `Int` (you write `(n : Int)`; Lean prints `↑n`) |
| `↑(n - 1)` | first the truncated `Nat` subtraction, then the cast; `(n - 1 : Nat)` in the source |
| `↑n - 1` | cast first, then `Int` subtraction (can be `-1`) |
| `a ≥ b` | `b ≤ a` |
| `a % 4`, `a / 4` | remainder and quotient of division by `4` (on `Nat`, `a / 4` rounds down) |
| `2 * x` | numeral times variable: linear, fine for `omega` |
| `x * y` | variable times variable: **not** linear; `omega` sees it as one unknown |

---

## Part 1 · `sub_add_cancel_nat`

Statement: for `n m : Nat` with `h : m ≤ n`, `n - m + m = n`. Without `h` it is false: `0 - 1 + 1 = 1`
(truncation, W1). `omega` needs no help beyond `h` being in the context (R1, R2).

**R1 · `omega`** **closes** a linear goal over `Nat`, combining any number of hypotheses from the context.
You never name them. Placeholders: `(a b c : Nat) (h1 : a ≤ b) (h2 : b + 2 ≤ c)`.

| Before | After |
|---|---|
| `h1 : a ≤ b, h2 : b + 2 ≤ c ⊢ a + 2 ≤ c` | no goals |

**R2 · `omega` with `Nat` subtraction** **closes** the goal. It handles `a - b` by splitting into the two
cases `b ≤ a` (then `a - b` is the true difference) and `a < b` (then `a - b = 0`), and checks the goal in
each. Here `h` kills the second case; without `h` the goal is false (`a = 0`, `b = 1`) and `omega` fails.
Placeholders: `(a b : Nat) (h : b ≤ a)`.

| Before | After |
|---|---|
| `h : b ≤ a ⊢ a - b + 2 * b = a + b` | no goals |

## Part 2 · `truncated`

Statement: `n - (n + 3) = 0` for `n : Nat`. Subtracting something larger truncates to `0` (R3). No
hypothesis is needed: `n ≤ n + 3` is itself linear, so `omega` sees it.

**R3 · `omega` with truncation** **closes** `a - b = 0` from `a ≤ b`. Placeholders: `(a b : Nat) (h : a ≤ b)`.

| Before | After |
|---|---|
| `h : a ≤ b ⊢ a - b = 0` | no goals |

**W1 · truncation computed.** `decide` (E001) evaluates closed arithmetic, so you can check a truncation
before proving anything: `(3 : Nat) - 5 = 0`, `(3 : Int) - 5 = -2`, `(0 : Nat) - 1 + 1 = 1`.

## Part 3 · `solve_system`

Statement: for `x y : Int` with `h1 : 2 * x + y = 7` and `h2 : x - y = 2`, both `x = 3` and `y = 1`.
`omega` solves the linear system and proves both conjuncts at once (R4); no `constructor` needed.

**R4 · `omega` on `Int` with `∧`** **closes** the goal. A conjunction (or `∨`, `¬`, `→`, `↔`) of linear facts
is still in `omega`'s fragment, so the goal does not have to be split first. Placeholders:
`(x y : Int) (h1 : x + y = 5) (h2 : x - y = 1)`.

| Before | After |
|---|---|
| `h1 : x + y = 5, h2 : x - y = 1 ⊢ x = 3 ∧ y = 2` | no goals |

`constructor` (E005) then `omega` on each half also works, one goal at a time.

**W2 · integers, not rationals.** `omega` reasons about whole numbers: from `h : 2 * x = 7` it proves `False`,
since no integer `x` has `2 * x = 7` (over the rationals `x = 7/2` would).

| Before | After |
|---|---|
| `h : 2 * x = 7 ⊢ False` | no goals |

## Part 4 · `cast_sub`

Statement: for `n : Nat`, `↑(n - 1) ≥ ↑n - 1` in `Int`. The left side truncates (`Nat`), the right does not
(`Int`): for `n = 0` it reads `0 ≥ -1`, for `n ≥ 1` both sides are `n - 1`. `omega` makes that case split
itself (R5, with R2 inside).

**R5 · `omega` with casts `↑`** **closes** goals that mix `Nat` and `Int`. It knows that `↑a ≥ 0`, that the cast
commutes with `+` and numeral `*`, and that `↑(a - b)` is the cast of a truncated difference, which it splits
as in R2. Placeholders: `(a b : Nat) (h : b ≤ a)`, goal in `Int`.

| Before | After |
|---|---|
| `h : b ≤ a ⊢ ↑(a - b) = ↑a - ↑b` | no goals |

## Part 5 · `mod_fact`

Statement: for `a : Nat` with `h : a % 4 = 3`, `a % 2 = 1`. Remainders by numerals are linear (R6): `omega`
writes `a = 4q + 3` and `a = 2q' + r` with `0 ≤ r < 2`, and finds `r = 1`.

**R6 · `omega` with `%` (and `/`) by a numeral** **closes** the goal. `a % k` and `a / k` for a numeral `k` become
a new quotient `q` and remainder `r` with `a = k * q + r`, `0 ≤ r < k`. With a variable divisor (`a % b`) this
is not linear and `omega` fails. Placeholders: `(a : Nat) (h : a % 2 = 1)`.

| Before | After |
|---|---|
| `h : a % 2 = 1 ⊢ (a + 1) % 2 = 0` | no goals |

**W5 · `/` by a numeral.** Rounding down on `Nat`:

| Before | After |
|---|---|
| `⊢ a / 2 ≤ a` | no goals |

### Beyond this exercise (W3, W4)

**W3 · connectives and `∀` in the goal.** `omega` introduces `∀ n` and `→` and handles the `∨` itself:

| Before | After |
|---|---|
| `⊢ ∀ (n : Nat), n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2` | no goals |

**W4 · products of variables are atoms.** `omega` treats `x * y` as one unknown `t`. From `h : t ≥ 3` it gets
`t + 1 ≥ 4`, so this closes:

| Before | After |
|---|---|
| `h : x * y ≥ 3 ⊢ x * y + 1 ≥ 4` | no goals |

But `x * y = y * x` (two different atoms) and `x * x ≥ 0` over `Int` need facts about `*`, and `omega` fails on
them.

---

## Traps

- `Nat` subtraction truncates at `0` (`3 - 5 = 0`), so `n - m + m = n` needs `m ≤ n`. When `omega` fails on a
  `Nat` goal with `-`, look for the case where the subtraction truncates: either the statement is false there
  or a hypothesis is missing.
- `(n - 1 : Nat)` cast to `Int` (`↑(n - 1)`) is not `↑n - 1`: they differ at `n = 0`.
- `omega` fails, it never half-succeeds: there is no partial progress to inspect. If it fails, check that every
  fact it needs is in the context and is linear.
- `x * y`, `x ^ 2`, `a % b` with a variable `b`: outside `omega`'s fragment. Products are treated as opaque
  atoms (W4); `x * y` and `y * x` are different atoms.
- `omega` works over `Nat` and `Int` (whole numbers), not `ℝ` or `ℚ`, and uses integrality (W2).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| linear goal over `Nat`/`Int` from context facts | `omega` | R1 |
| `Nat` `-` that is exact because `b ≤ a` is known | `omega` | R2 |
| `a - b = 0` on `Nat` when `a ≤ b` | `omega` | R3 |
| linear system, `∧`/`∨`/`¬`/`→`/`↔` of linear facts | `omega` | R4, W3 |
| mixed `Nat`/`Int` with `↑` | `omega` | R5 |
| `%`, `/` by a numeral | `omega` | R6, W5 |
| contradictory integer hypotheses, goal `False` | `omega` | W2 |
| evaluate closed arithmetic (e.g. a truncation) | `decide` | W1 |
| product of two variables | `omega` only if it can be an opaque atom | W4 |
| see the state | infoview (cursor after a tactic) | |
