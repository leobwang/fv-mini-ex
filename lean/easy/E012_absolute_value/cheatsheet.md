# E012 · Absolute value: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** E001 (`def`, `decide`, `#eval`), E002 (a `def` body is a term), E003 (tactic mode, `exact`),
E005 (`∧`, `∨`, `t <;> u`), E008 (`absurd`, used in W4), E011 (`omega`, `Int`).
**New here:** the term `if c then a else b`, the tactic `unfold`, and the tactic `split`, which turns one
goal containing an `if` into one goal per branch, each with the branch condition as a hypothesis. This is
the standard way to prove facts about a function defined by cases on a condition.

## How to read an entry

Each entry is one term or one tactic. It says what changes (**goal**, **context**, or **goal list**), lists
the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses (the **context**) `Γ`, **goal** `G`. A cell shows only the
  hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- `c : Prop` is a condition; `[Decidable c]` is the requirement that Lean can compute whether `c` holds. It
  is met by `<`, `≤`, `=` on `Int` and `Nat`, and by `∧`, `∨`, `¬` of such conditions.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `if c then a else b` | `a` when `c` holds, `b` otherwise; `a` and `b` have the same type |
| `x : Int` | an integer, negatives included |
| `-x` | integer negation (`-(-3) = 3`); linear, so `omega` handles it |
| `¬x < 0` | "not `x < 0`", i.e. `0 ≤ x`; `omega` reads it that way |
| `h✝ : c` | a hypothesis with an inaccessible name (made by `split`): tactics use it, you cannot type `h✝` |
| `inst✝ : Decidable c` | the `[Decidable c]` placeholder, an unnamed instance |
| `case isTrue`, `case isFalse` | the goal for the `then` branch (`c` holds) and for the `else` branch |
| `(0 ≤ if c then a else b) ∧ …`, `(if c then a else b) = x` | `else b` extends as far right as it can, so Lean adds parentheses whenever something follows the `if`; they group, nothing more |
| `-1 * -1` | `(-1) * (-1)`: unary minus binds tighter than `*` |

---

## Part 1 · `myAbs` (definition body)

Statement: `myAbs : Int → Int`. You write its body. The theorem in Part 2 forces the value: it must be
`≥ 0` and equal to `x` or `-x`, so it is `-x` when `x < 0` and `x` otherwise. A case split on a condition
is an `if` (R1). Check the values with `#eval` before proving anything (W1).

**R1 · `if c then a else b`** **closes** a `⊢ α` goal: it is a term of type `α`. Placeholders:
`(c : Prop) [Decidable c] {α : Type} (a b : α)`. In a `def` write it directly after `:=`; the guide feeds
it to `exact` only to show the goal it fills (as E002 does).

| Before | After |
|---|---|
| `a b : α ⊢ α` | no goals |

## Part 2 · `myAbs_spec`

Statement: for every `x : Int`, `0 ≤ myAbs x ∧ (myAbs x = x ∨ myAbs x = -x)`. `omega` cannot see inside
`myAbs`: to it `myAbs x` is an unknown integer. So first expose the body (R2), then split on its `if` (R3),
then each branch is linear arithmetic with the branch condition in the context (R4).

**R2 · `unfold f`** changes the **goal**: every `f x` becomes the body of `f` with `x` substituted. Placeholders:
`(x : Int) (P : Int → Prop)`, and `sgn` from the guide, `sgn x = if x < 0 then -1 else 1`.

| Before | After |
|---|---|
| `⊢ P (sgn x)` | `⊢ P (if x < 0 then -1 else 1)` |

**R3 · `split`** changes the **goal list and the context**: a goal containing `if c then a else b` becomes
two goals. In the first (`isTrue`) the `if` is replaced by `a` and the context gains `h✝ : c`; in the second
(`isFalse`) by `b`, with `h✝ : ¬c`. All copies of the same `if` are replaced together (W2). Placeholders:
`(c : Prop) [Decidable c] {α : Type} (a b : α) (P : α → Prop)`.

| Before | After |
|---|---|
| `⊢ P (if c then a else b)` | `h✝ : c ⊢ P a`, `h✝ : ¬c ⊢ P b` |

**R4 · `omega` after `split`** **closes** a branch goal. The branch hypothesis `h✝ : x < 0` or `h✝ : ¬x < 0` is
linear (`¬x < y` reads as `y ≤ x`), `-x` is linear on `Int`, and `∧`/`∨` of linear facts need no
`constructor`, `left` or `right` first (E011 R4). `omega` uses `h✝` though you cannot name it.
Placeholders: `(x y : Int) (h : ¬x < y)`.

| Before | After |
|---|---|
| `h : ¬x < y ⊢ y ≤ x ∧ (x - y = 0 ∨ -(x - y) < 0)` | no goals |

`split <;> omega` runs `omega` on both goals `split` makes (`<;>`, E005; TACTIC_STATES "Structure").

### Worked combinations (W1–W4, on `sgn` and `relu`, not the exercise's function)

**W1 · run it first.** `#eval sgn (-3)` prints `-1`; `decide` proves `sgn (-3) = -1 ∧ sgn 0 = 1`.

**W2 · one `split`, every copy.** After `unfold sgn`, `sgn x * sgn x = 1` has two copies of one `if`:

```lean-goal
⊢ sgn x * sgn x = 1
⊢ ((if x < 0 then -1 else 1) * if x < 0 then -1 else 1) = 1
```

`split` replaces both copies in each branch, giving `-1 * -1 = 1` and `1 * 1 = 1` (closed by `decide`), never
a mixed `-1 * 1`.

**W3 · the full chain R1 → R2 → R3 → R4** on `relu x = if x < 0 then 0 else x`, goal
`0 ≤ relu x ∧ x ≤ relu x`. `unfold relu` gives

```lean-goal
⊢ (0 ≤ if x < 0 then 0 else x) ∧ x ≤ if x < 0 then 0 else x
```

and `split <;> omega` closes both branches.

**W4 · naming the branch hypothesis.** `next h => tac` works on the next goal and names its `h✝` as `h`, for a
branch closed by a term that mentions it. For `relu x = x` with `hx : 0 ≤ x`, after `unfold relu`:

```lean-goal
⊢ (if x < 0 then 0 else x) = x
```

`split` then gives `h✝ : x < 0 ⊢ 0 = x` (contradicts `hx`: `next h => exact absurd hx (Int.not_le.mpr h)`,
where core's `Int.not_le : ¬a ≤ b ↔ b < a`) and `h✝ : ¬x < 0 ⊢ x = x` (`next => rfl`).

---

## Traps

- `split` before `unfold`: the goal mentions `myAbs x`, not an `if`, so `split` fails. Unfold first (R2).
- The `if` must be on a **decidable** condition. `x < 0` on `Int` is; for an arbitrary `Prop` with no
  `Decidable` instance Lean rejects the `def` with `failed to synthesize Decidable`.
- `t ; u` runs `u` on the first goal only. After `split` there are two goals: use `split <;> omega`, or
  handle each with its own line (R3, W4).
- `h✝` cannot be typed. `omega`, `simp` and `‹c›` use it anyway; to refer to it by name use `next h => …` (W4).
- The order of the branches is the order in the `if`: with `if x < 0 then … else …` the first goal is the
  `x < 0` case. Writing `if 0 ≤ x then x else -x` is equally valid; only the branch order changes.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| define by cases on a condition | `if c then a else b` (`c` decidable) | R1 |
| check a definition's values | `#eval f (-3)`, `decide` | W1 |
| expose a definition's body in the goal | `unfold f` | R2 |
| one goal per branch of an `if` | `split` (adds `h✝ : c` / `h✝ : ¬c`) | R3 |
| close linear branches, `∧`/`∨`/`-x` included | `omega` | R4 |
| both branches at once | `split <;> omega` | R3, R4, W3 |
| name the branch hypothesis | `next h => …` | W4 |
| see the state | infoview (cursor after a tactic) | |
