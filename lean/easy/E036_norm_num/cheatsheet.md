# E036 · norm_num: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular tactic mode, `decide` (E001), `rw [h]` (E009)
and `simp` (E010).
**New here:** Mathlib. `import Mathlib` loads the number types `ℤ ℚ ℝ` and Mathlib's tactics, among them
`norm_num`. `norm_num` ("normalize numerals") is `simp` plus exact arithmetic on numerals: it evaluates `+ - *
^ ⁻¹ / %` on literals in any of these types, reduces fractions, and decides `=`, `≠`, `<`, `≤` between the
results. It closes a goal that is a true numeric fact, and otherwise leaves the goal with its numeric parts
evaluated (R6).

## How to read an entry

Each entry is one tactic call. It says what changes (**goal**, **context**, or **goal list**), lists the
placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses (the **context**) `Γ`, **goal** `G`. A cell shows only the hypotheses
  that change. "no goals" means the tactic closed the goal.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`.
- Placeholders are written as Lean binders: `(x : ℝ)` is a real number, `(h : …)` a hypothesis.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means | Type it as |
|---|---|---|
| `ℤ` | `Int`, the integers | `\Z` |
| `ℚ` | the rationals: exact fractions `p / q` | `\Q` |
| `ℝ` | the real numbers. Equality on `ℝ` is not decidable, so `decide` and `rfl` fail there; `norm_num` works | `\R` |
| `(3 : ℝ)` in the source, `3` in the infoview | the numeral `3` of type `ℝ`. The infoview drops the ascription; hover over the `3` to see its type | `(3 : ℝ)` |
| `a ^ n` | `a` to the natural-number power `n` | `^` |
| `a⁻¹` | the inverse `1 / a` (in `ℚ`, `ℝ`; Mathlib sets `0⁻¹ = 0`) | `\inv` or `\-1` |
| `a / b` | in `ℚ`, `ℝ`: the exact quotient. In `ℕ`, `ℤ`: the integer quotient | `/` |
| `a % b` | the remainder of integer division (`ℕ`, `ℤ`); `0 ≤ a % b < b` when `b > 0` | `%` |
| `a > b` | notation for `b < a` (and `a ≥ b` for `b ≤ a`) | `>` |
| `a ≠ b` | `a = b → False` | `\ne` |

---

## Part 1 · `pow_ten`

Statement: `(2 : ℝ) ^ 10 = 1024`. Only numerals, in `ℝ`: one `norm_num` (R1). `decide` would fail, because
`ℝ` has no decidable equality.

**R1 · `norm_num` on `+ - * ^` in `ℝ`** **closes** the goal. It evaluates both sides exactly (no floating
point) and compares. Placeholders: none, the goal is closed (`(3 : ℝ) ^ 4 - 1 = 80` in the guide).

| Before | After |
|---|---|
| `⊢ 3 ^ 4 - 1 = 80` | no goals |

**W1 · `rw [h]`, then `norm_num`.** With `h : x = 3`, the goal `x ^ 2 + 1 = 10` is not closed by `norm_num`
(it has a variable). Substitute first:

| Before | After `rw [h]` | After `norm_num` |
|---|---|---|
| `h : x = 3 ⊢ x ^ 2 + 1 = 10` | `h : x = 3 ⊢ 3 ^ 2 + 1 = 10` | no goals |

**W2.** `norm_num` also proves that two numerals differ:

| Before | After |
|---|---|
| `⊢ 2 ^ 3 ≠ 9` | no goals |

## Part 2 · `frac_gt`

Statement: `(7 : ℚ) / 2 > 3`, i.e. `3 < 7 / 2` in the rationals. The ascription `(7 : ℚ)` makes the whole
expression rational, so `7 / 2` is the fraction `7/2`, not `3` (R5). One `norm_num` (R2).

**R2 · `norm_num` on an order between fractions in `ℚ`** **closes** the goal. It handles `<`, `≤`, `>`, `≥`,
`=`, `≠`: each side becomes a reduced fraction, then the two are compared. Placeholders: none.

| Before | After |
|---|---|
| `⊢ 5 / 3 > 3 / 2` | no goals |

**R5 · the ascription decides the type** (`(7 : ℕ)` versus `(7 : ℚ)`). `norm_num` **closes** the goal in each
type, but the facts differ. A numeral with no ascription and no other type information is a natural number
(`ℕ`), where `/` rounds down and `-` stops at `0`. One ascription anywhere fixes the type of the whole
expression.

| Before | After |
|---|---|
| `⊢ 7 / 2 = 3 ∧ 2 - 5 = 0` (in `ℕ`) | no goals |
| `⊢ 7 / 2 ≠ 3` (in `ℚ`) | no goals |

Both rows print `7 / 2`; only hovering shows whether it is `ℕ` or `ℚ`.

## Part 3 · `big_mod`

Statement: `(12345 : ℤ) % 7 = 4`. The remainder of `12345` divided by `7`, in the integers. One `norm_num`
(R3). (`decide` also works here, since `ℤ` has decidable equality, but `norm_num` is the general tool.)

**R3 · `norm_num` on `%` and `/` in `ℤ`** **closes** the goal. For `b > 0`, `a / b` and `a % b` satisfy
`a = b * (a / b) + a % b` with `0 ≤ a % b < b`, also for negative `a`. Placeholders: none.

| Before | After |
|---|---|
| `⊢ 1000 % 9 = 1` | no goals |
| `⊢ -7 % 3 = 2 ∧ -7 / 3 = -3` | no goals |

The second row: `-7 = 3 * (-3) + 2`. A `∧` of numeric facts is fine; `norm_num` proves both sides.

## Part 4 · `inv_sum`

Statement: `(3 : ℝ)⁻¹ + 6⁻¹ = 1 / 2`. Inverses and a fraction in `ℝ`; only numerals. One `norm_num` (R4).

**R4 · `norm_num` on `⁻¹` and `/` in `ℝ`** **closes** the goal. It computes with exact fractions:
`2⁻¹ + 4⁻¹ = 1/2 + 1/4 = 3/4`. Placeholders: none.

| Before | After |
|---|---|
| `⊢ 2⁻¹ + 4⁻¹ = 3 / 4` | no goals |

**W3.** R2 and R4 together, in `ℚ`: an inverse inside a comparison.

| Before | After |
|---|---|
| `⊢ 4⁻¹ < 1 / 3` | no goals |

---

## When the goal is not purely numeric

None of the four holes needs this, but it is what you see when `norm_num` does not finish.

**R6 · `norm_num` that cannot close the goal** changes the **goal**: like `simp` (E010), it evaluates the
numeric parts and leaves the rest. Unlike `simp`, it does not fail when it changes nothing: the goal stays
as it was and Lean only warns "'norm_num' tactic does nothing". Placeholders:
`(x : ℝ) (P : ℝ → Prop) (h : P (x + 6))`.

| Before | After |
|---|---|
| `h : P (x + 6) ⊢ P (x + 2 * 3)` | `h : P (x + 6) ⊢ P (x + 6)` |

---

## Traps

- On a **false** numeric statement such as `(2 : ℝ) + 2 = 5`, `norm_num` reduces the goal to `False` and
  reports an error (unsolved goal `False`). That is a sign the statement, or its type, is not what you meant.
- A missing ascription changes the problem: `7 / 2 > 3` with no type is a statement about `ℕ`, where
  `7 / 2 = 3`, and it is false (R5). The infoview prints `7 / 2` in both cases; hover to see the type.
- `decide` and `rfl` do not work on `ℝ` (equality there is not decidable). Use `norm_num`.
- `norm_num` does not use hypotheses unless you pass them (`norm_num [h]`) or rewrite first (`rw [h]`, W1).
- `/` and `%` in `ℤ` round so that the remainder is non-negative for a positive divisor: `-7 / 3 = -3`, not
  `-2` (R3).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `+ - * ^` of numerals, any type | `norm_num` | R1 |
| `<`, `≤`, `>`, `≠` between fractions | `norm_num` | R2 |
| `%`, `/` of integers | `norm_num` | R3 |
| `⁻¹`, `/` in `ℚ` or `ℝ` | `norm_num` | R4 |
| make a numeral rational / real | `(7 : ℚ)`, `(3 : ℝ)` | R5 |
| evaluate numerals inside a bigger goal | `norm_num` (leaves the rest) | R6 |
| a variable with a known value | `rw [h]`, then `norm_num` | W1 |
| see the state | infoview (cursor after a tactic) | |
