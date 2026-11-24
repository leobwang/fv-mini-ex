# E037 · positivity: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular tactic mode, `apply`/`exact` (E003) and `rw`
(E009).
**New here:** Mathlib. `import Mathlib` loads the number types `ℕ ℝ`, the absolute value `|x|`, the real
exponential `Real.exp`, and the tactic `positivity`. `positivity` proves a goal of exactly one of the forms
`0 < e`, `0 ≤ e`, `e ≠ 0` (also written `e > 0`, `e ≥ 0`). It reads `e` as a tree and proves a sign for each
node from the signs of its children, bottom up. It either closes the goal or fails; it never leaves a goal.

| Node of `e` | Sign `positivity` derives |
|---|---|
| numeral `3` | `> 0` (`0` gives only `≥ 0`) |
| variable `a` in `ℝ` | what a hypothesis says: `0 < a`, `0 ≤ a`, `1 < a`, …; none: fails |
| variable `n` in `ℕ` | `≥ 0` always |
| `a + b` | `> 0` if one side `> 0` and the other `≥ 0`; `≥ 0` if both `≥ 0` |
| `a * b`, `a / b` | `> 0` if both `> 0`; `≥ 0` if both `≥ 0` |
| `a ^ n` | `≥ 0` if `n` is an even numeral (any `a`); `> 0` if `a > 0` (any `n`) |
| `\|a\|` | `≥ 0` (`> 0` only if `a ≠ 0` is known) |
| `Real.exp a` | `> 0` (any `a`) |

## How to read an entry

Each entry is one call of `positivity` on one shape of `e`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses (the **context**) `Γ`, **goal** `G`. A cell shows only the
  hypotheses that matter. "no goals" means the tactic closed the goal.
- Placeholders are written as Lean binders: `(y : ℝ)` is any real number, `(n : ℕ)` any natural number,
  `(ha : 0 < a)` a hypothesis.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means | Type it as |
|---|---|---|
| `ℝ` | the real numbers (Mathlib's `Real`) | `\R` |
| `ℕ` | `Nat`: `0, 1, 2, …`; every element is `≥ 0` | `\N` |
| `0`, `1` in a goal about `x : ℝ` | the numerals of type `ℝ` (the type comes from the other side of `<`) | |
| `x ^ 2` | `x * x`; the exponent is a natural number | `^` |
| `\|x\|` | `abs x`, the absolute value: `x` if `x ≥ 0`, else `-x` | `\|x\|` |
| `Real.exp x` | `eˣ`, the real exponential function | |
| `e > 0`, `e ≥ 0` | notation for `0 < e`, `0 ≤ e`; `positivity` accepts both | `>`, `\ge` |
| `e ≠ 0` | `¬ (e = 0)` | `\ne` |
| `2 ^ n` with `n : ℕ` | a natural-number power whose exponent is a variable | |

---

## Part 1 · `sq_add_one_pos`

Statement: for `x : ℝ`, `0 < x ^ 2 + 1`. A square is `≥ 0`, `1` is `> 0`, so the sum is `> 0` (R1).

**R1 · `positivity` on a sum of even powers and a positive numeral** **closes** the goal. Placeholders:
`(y : ℝ)`. `y ^ 4`, `y ^ 2` are even powers (`≥ 0` for every `y`), `2 * y ^ 2` is `> 0` times `≥ 0`, `1 > 0`.

| Before | After |
|---|---|
| `y : ℝ ⊢ 0 < y ^ 4 + 2 * y ^ 2 + 1` | no goals |

## Part 2 · `prod_pos`

Statement: for `a b : ℝ` with `ha : 0 < a` and `hb : 0 ≤ b`, `0 < a * (b + 1)`. A product of two factors
`> 0`: `a` by `ha`, and `b + 1` because `b ≥ 0` by `hb` and `1 > 0` (R2).

**R2 · `positivity` with variables bounded by hypotheses** **closes** the goal. Placeholders:
`(a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)`. A real variable is a leaf whose sign must come from the context:
without `ha`, `positivity` fails here.

| Before | After |
|---|---|
| `ha : 0 < a, hb : 0 ≤ b ⊢ 0 < (b + 2) * a` | no goals |

## Part 3 · `exp_abs_pos`

Statement: for `x : ℝ`, `0 < Real.exp x + |x|`. `Real.exp x > 0` for every `x` (R3) and `|x| ≥ 0` (R4); a
sum of a `> 0` and a `≥ 0` term is `> 0`. No hypothesis is needed.

**R3 · `positivity` on `Real.exp`** **closes** the goal. Placeholders: `(x : ℝ)`. `Real.exp x > 0` holds for
every `x`, so `positivity` needs nothing about `x`.

| Before | After |
|---|---|
| `x : ℝ ⊢ 0 < 3 * Real.exp x` | no goals |

**R4 · `positivity` on `|x|`** **closes** the goal. Placeholders: `(x y : ℝ) (hy : 0 < y)`. `|x|` is only
`≥ 0` (it is `0` at `x = 0`), so a strict goal needs a summand that is `> 0`, here `y` by `hy`.

Before (the absolute-value bars would break a table, so the state is shown as a block); after: no goals.

```lean-goal
⊢ 0 < |x| + y
```

## Part 4 · `nat_pow_pos`

Statement: for `n : ℕ`, `0 < 2 ^ n + n`. In `ℕ`, `2 ^ n > 0` (positive base, any exponent) and `n ≥ 0` with
no hypothesis, so the sum is `> 0` (R5).

**R5 · `positivity` in `ℕ`** **closes** the goal. Placeholders: `(n : ℕ)`. Every natural number is `≥ 0`, and a
power of a positive base is `> 0` whatever the exponent.

| Before | After |
|---|---|
| `n : ℕ ⊢ 0 < 3 ^ n * (n + 1)` | no goals |

### Worked combinations (W1–W4, on statements that are not the exercise's)

**W1 · a non-strict goal.** For `0 ≤ e` every leaf only needs `≥ 0`, so `|x|` and `x ^ 2` suffice.

Before; after: no goals.

```lean-goal
⊢ 0 ≤ x ^ 2 + |x|
```

**W2 · a goal `e ≠ 0`.** `positivity` proves `0 < e`, which gives `e ≠ 0`.

| Before | After |
|---|---|
| `x : ℝ ⊢ Real.exp x + x ^ 2 ≠ 0` | no goals |

**W3 · division.** `a / (a + 1)` is `> 0` over `> 0`; `ha` gives both.

| Before | After |
|---|---|
| `ha : 0 < a ⊢ 0 < a / (a + 1)` | no goals |

**W4 · what `positivity` does, by hand.** `apply add_pos_of_pos_of_nonneg` (the lemma
`0 < a → 0 ≤ b → 0 < a + b`) splits a sum into one goal per summand (cases `ha`, `hb`). Then
`exact Real.exp_pos y` (`0 < Real.exp y`) and `exact sq_nonneg y` (`0 ≤ y ^ 2`) close them. `positivity`
finds this chain itself; you never need to name these lemmas in this exercise.

| Before | After `apply add_pos_of_pos_of_nonneg` |
|---|---|
| `y : ℝ ⊢ 0 < Real.exp y + y ^ 2` | `⊢ 0 < Real.exp y`, `⊢ 0 ≤ y ^ 2` |

---

## Traps

- Only `0 < e`, `0 ≤ e`, `e ≠ 0` (or `e > 0`, `e ≥ 0`). On `1 < x ^ 2 + 2` it fails with "not a positivity
  goal": the left side must be `0`. Move terms across first, or use `nlinarith`/`norm_num`.
- `positivity` does no arithmetic on signs that cancel: `0 < x - 1` with nothing known about `x` fails, and so
  does `0 ≤ y ^ 3` (an odd power can be negative).
- A strict goal needs one strictly positive piece: `0 < |x|` and `0 < x ^ 2` fail with "failed to prove strict
  positivity, but it would be possible to prove nonnegativity". Both are false at `x = 0`.
- A real variable with no hypothesis is unknown, not `≥ 0`. Only `ℕ` variables are `≥ 0` for free.
- `positivity` proves a sign; it does not prove an order between two non-zero sides. For `y < x` from
  `0 < x - y`, use `linarith` (E035) or `sub_pos`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `0 < (even powers) + (positive numeral)` | `positivity` | R1 |
| sign of a variable | a hypothesis `0 < a` / `0 ≤ a` in the context, then `positivity` | R2 |
| `Real.exp _ > 0` | `positivity` | R3 |
| `\|x\| ≥ 0`, strict only with a `> 0` partner | `positivity` | R4 |
| `ℕ`: `0 < b ^ n + …` with `b > 0` | `positivity` | R5 |
| `0 ≤ e` / `e ≠ 0` | `positivity` | W1, W2 |
| quotient of positives | `positivity` | W3 |
| by hand | `add_pos_of_pos_of_nonneg`, `mul_pos`, `Real.exp_pos`, `sq_nonneg`, `abs_nonneg` | W4 |
| goal not of the form `0 < e` | rearrange first, or `linarith` (E035) | |
| see the state | infoview (cursor after a tactic) | |
