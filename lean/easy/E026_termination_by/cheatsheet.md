# E026 · termination_by: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** E001–E025: `def` and structural recursion by pattern matching (E001, E002), `rw` and `rw`
closing `t = t` by itself (E009), `simp [f]` (E010), `omega` (E011), `if c then a else b` (E012).
**New here:** *well-founded recursion*. A recursive call on something that is not a pattern variable
(`f (n / 2)`, `f (n - 1)`) is not structural, so Lean needs a **measure**: `termination_by n` after the
body says "`n` gets smaller at every recursive call". (Without the clause Lean tries to guess a measure, and
for simple cases like this one it succeeds; the clause states it explicitly, and it is what this exercise
practices.) Lean proves the decrease itself, but the price is that the
function no longer computes by `rfl`/`decide`: you reason about it with its unfolding equation, through
`simp [f]` (numerals) or `rw [f]` (one step), plus `if_neg` to pick a branch. No Mathlib.

## How to read an entry

Each entry is one tactic, one clause or one lemma used with `rw`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `P` is "the rest of your goal" (`P : α → Prop`, `P : List Nat → Prop`). The step changes only the part
  inside `P (…)`, wherever it sits in a larger goal. A hypothesis `k` only finishes the example.
- `{α : Type}` is any type. `[Decidable c]` means Lean can compute whether `c` holds; `n = 0`, `n ≤ 1`,
  `n < 10` on `Nat` all meet it, which is why `if` on them is allowed.
- "no goals" means the step closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

The guide's function (not the exercise's):

```lean
def cd (n : Nat) : List Nat := if n = 0 then [] else n :: cd (n - 1)
termination_by n
-- cd 3 = [3, 2, 1];  Lean generates  cd.eq_1 : ∀ (n : Nat), cd n = if n = 0 then [] else n :: cd (n - 1)
```

## Reading the goals

| You see | It means |
|---|---|
| `termination_by n` | a clause after the body, on its own line: the measure `n` decreases at every recursive call |
| `n / 2` | `Nat` division rounded down: `7 / 2 = 3`, `1 / 2 = 0` |
| `n - 1` | `Nat` subtraction, cut off at 0: `0 - 1 = 0` |
| `if c then a else b` | `a` when `c` holds, else `b`; both branches have the same type |
| `¬n ≤ 1` | `n ≤ 1` is false, i.e. `2 ≤ n` (what you know inside the `else` branch) |
| `h✝` | a hypothesis Lean named itself; it is usable by `omega`/`simp`, not by name |
| `f.eq_1` (e.g. `cd.eq_1`) | the unfolding equation `∀ n, f n = <body>` Lean generates for a well-founded `f`; `rw [f]` and `simp [f]` use it |
| `failed to prove termination` | Lean could not prove the measure decreases; the error shows the goal it tried |

---

## Part 1 · `halvings` (definition body)

Statement: `halvings : Nat → Nat`, the number of times `n` can be halved (rounding down) before it is `≤ 1`.
The theorems below pin the shape: `0` for `n ≤ 1`, and `1 + halvings (n / 2)` for `2 ≤ n`. That is an
`if` (E012) with the recursive call in the `else` branch. The call is on `n / 2`, not on a pattern
variable, so the body needs a measure (R1); the obligation it creates is a division fact `omega` proves (R2).

**R1 · `termination_by n`** is a **clause**, written on its own line after the body. It shows no goal while you
type, but it makes Lean prove, for each recursive call `f e`, the obligation `e < n`. The context of that
obligation holds the `if` condition of the branch the call sits in: for `cd`, the call `cd (n - 1)` is in the
`else` branch of `if n = 0`, so Lean's goal is `n - 1 < n` with `h✝ : ¬n = 0` in context. Lean closes it
itself (its `decreasing_tactic` tries `omega`). When it cannot, the error `failed to prove termination`
prints that goal; `decreasing_by omega` after `termination_by` runs `omega` on it explicitly. The guide
example is that obligation with the hypothesis named. Placeholders: `(n : Nat) (h : ¬n = 0)`.

| Before | After `omega` |
|---|---|
| `h : ¬n = 0 ⊢ n - 1 < n` | no goals |

**R2 · `omega` on `n / 3 < n`** **closes** the goal. `omega` handles `/` and `%` by a **numeral** (not by a
variable). This is the obligation of a call `f (n / 3)` in the `else` branch of `if n = 0`; without the
hypothesis it is false (`0 / 3 = 0`). The branch condition is what makes the measure decrease, so the base
case must cover every `n` for which the call would not shrink. Placeholders: `(n : Nat) (h : ¬n = 0)`.

| Before | After |
|---|---|
| `h : ¬n = 0 ⊢ n / 3 < n` | no goals |

## Part 2 · `halvings_small`

Statement: `halvings 0 = 0 ∧ halvings 1 = 0`. Both sides are numerals: a closed computation (R3).

**R3 · `simp [f]`** **closes** `f a = v` when `a` and `v` are numerals. It rewrites `f a` with the unfolding
equation (`cd.eq_1`), decides the `if` on numerals (`3 = 0` is `False`), computes the arithmetic
(`3 - 1 = 2`, `8 / 2 = 4`), and repeats until no `f` is left. It splits an `∧` of such equations itself.
`rfl` and `decide` **fail** on a well-founded function: it does not unfold by computation.
Placeholders: `cd` from the guide.

| Before | After `simp [cd]` |
|---|---|
| `⊢ cd 3 = [3, 2, 1]` | no goals |

## Part 3 · `halvings_step`

Statement: for `h : 2 ≤ n`, `halvings n = 1 + halvings (n / 2)`. `n` is a variable, so `simp [halvings]`
cannot decide the `if` and loops. Unfold exactly one step (R4), take the `else` branch (R5) with its
condition proved in place (R6); then both sides agree and `rw` closes the goal (E009).

**R4 · `rw [f]`** changes the **goal**: the first `f n` in the goal becomes the body of `f` at `n`, once. `rw`
uses the unfolding equation `cd.eq_1 : ∀ (n : Nat), cd n = if n = 0 then [] else n :: cd (n - 1)`,
instantiated at the first `cd _` it finds; every copy of that one instance is rewritten, other calls such as
`cd (n - 1)` stay. Placeholders: `(n : Nat) (P : List Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (cd n)` | `⊢ P (if n = 0 then [] else n :: cd (n - 1))` |

**R5 · `rw [if_neg hc]`** changes the **goal**: the `if` becomes its `else` branch. The lemma is
`if_neg : ¬c → (if c then t else e) = e`; its twin `if_pos : c → (if c then t else e) = t` takes the `then`
branch. Placeholders: `{α : Type} (c : Prop) [Decidable c] (t e : α) (P : α → Prop) (hc : ¬c)`.

| Before | After |
|---|---|
| `hc : ¬c ⊢ P (if c then t else e)` | `hc : ¬c ⊢ P e` |

**R6 · `omega` on `¬n ≤ k`** **closes** the goal from `h : k + 1 ≤ n` (`omega` handles `¬` of a linear fact).
Write it as the argument: `rw [if_neg (by omega)]`. `rw` first matches `if_neg` against the `if` in the
goal, which fixes `c`, and only then runs `omega` on `¬c` with your hypotheses in context.
Placeholders: `(n k : Nat) (h : k + 1 ≤ n)`.

| Before | After |
|---|---|
| `h : k + 1 ≤ n ⊢ ¬n ≤ k` | no goals |

**W2** (R4, R5, R6 on `cd`): from `h : 0 < n`, `cd n = n :: cd (n - 1)`. After `rw [cd]` only the left `cd n`
is unfolded; after `rw [if_neg (by omega)]` both sides are `n :: cd (n - 1)` and `rw` closes the goal.

| Step | State |
|---|---|
| start | `h : 0 < n ⊢ cd n = n :: cd (n - 1)` |
| `rw [cd]` | `⊢ (if n = 0 then [] else n :: cd (n - 1)) = n :: cd (n - 1)` |
| `rw [if_neg (by omega)]` | no goals |

## Part 4 · `halvings_eight`

Statement: `halvings 8 = 3`. A closed computation again (R3): `simp` repeats the unfolding along
8 → 4 → 2 → 1 and adds up the `1`s.

**W1** (R3 on `digits n = if n < 10 then 0 else 1 + digits (n / 10)`): `simp [digits]` unfolds
345 → 34 → 3 and closes the goal.

| Before | After `simp [digits]` |
|---|---|
| `⊢ digits 345 = 2` | no goals |

---

## Traps

- `rfl` and `decide` do not compute a well-founded function: `rfl` fails with `The left-hand side
  … is not definitionally equal to the right-hand side`. Use `simp [f]` (numerals) or `rw [f]` (one step).
- `simp [f]` on a variable argument loops: it unfolds `f n`, cannot decide the `if`, unfolds the new
  `f (n / 2)`, and so on, ending in `maximum recursion depth has been reached`. Use `rw [f]`.
- Leaving out `termination_by` usually still compiles (Lean guesses the measure `n`), so a missing clause
  is not an error here; write it anyway. When the guess fails you get `failed to prove termination`.
- `termination_by` goes on its own line **after** the whole body, at the indentation of `def`, not inside the
  `if`.
- The measure must drop on the branch where the call happens. With `if n = 0 then … else f (n / 2)` Lean must
  prove `n / 2 < n` from `¬n = 0`, which holds; with `n / 2` and no condition at all it would be false at `0`.
- After the last `rw` makes both sides identical, the goal is already closed: an extra `rfl` fails with
  `no goals` (E009).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| recursion on `n / 2`, `n - 1`, … | body, then `termination_by n` on the next line | R1 |
| the obligation `e < n` | Lean proves it; else `decreasing_by omega` | R1, R2 |
| `f a = v` with numerals | `simp [f]` (not `rfl`, not `decide`) | R3 |
| unfold `f n` once, `n` a variable | `rw [f]` | R4 |
| take the `else` branch | `rw [if_neg hc]` | R5 |
| take the `then` branch | `rw [if_pos hc]` | R5 |
| the branch condition from a hypothesis | `rw [if_neg (by omega)]` | R6 |
| see the state | infoview | |
