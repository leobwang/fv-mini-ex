# M057 · Solving x² = 4: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): tactic mode, `have`, `exact`, `·` bullets, `∨` and `↔`
(`.mp` is the left-to-right direction of an `↔`, E005).
**New here:** Mathlib (`import Mathlib`), the real numbers `ℝ`, the tactics `ring_nf` and `linarith`, the
lemma `mul_eq_zero`, `rcases` on a disjunction, and `left` / `right`.

The method is the school one. To solve $p(x) = 0$ for a quadratic $p$ with roots $r, s$: prove the factored
form $(x - r)(x - s) = 0$ from the hypothesis, conclude $x - r = 0$ or $x - s = 0$ (a product of reals is
$0$ only if a factor is), and solve each linear equation.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**), lists
the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses (the **context**) `Γ`, **goal** `G`. A cell shows only the
  hypotheses that change. "no goals" means the step closed the goal.
- `G : Prop` is a goal the step does not touch; `g`, `ga`, `gb` are hypotheses that only finish the example.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[CommRing α]` is a
  requirement on `α` (a *type class*); Lean shows it in the context as `inst✝ : CommRing α`. Each entry says
  which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ`, `ℚ` | Mathlib's real and rational numbers (type `\R`, `\Q`). Both are ordered fields |
| `4`, `-2` in `x = -2` | numerals of type `ℝ` (the type comes from `x`); `-2` is `-(2)`, negation applied to `2` |
| `x ^ 2` | `x * x`; the exponent `2` is a natural number |
| `-4 + x ^ 2`, `6 - x * 5 + x ^ 2` | what `ring_nf` prints: constant first, then increasing powers, numeral coefficients written after the variable (`x * 5` is $5x$) |
| `A ∨ B` | "A or B"; a proof is a proof of one side |
| `h : a = 0 ∨ b = 0` | a hypothesis saying one of the two factors is zero (you do not know which) |
| `case inl`, `case inr` | the two goals after `rcases` on `∨`: the left side holds, the right side holds |
| `inst✝ : CommRing α` | the instance from a bracket `[CommRing α]` |

---

## Part 1 · `sq_eq_four`

Statement: for a real `x` with `h : x ^ 2 = 4`, `x = 2 ∨ x = -2`. Plan: $x^2 - 4 = (x - 2)(x + 2)$, so
$(x - 2)(x + 2) = 0$, so $x - 2 = 0$ or $x + 2 = 0$.

### Proving the factored form

Write `have h' : (x - 2) * (x + 2) = 0 := by …` (`have`: TACTIC_STATES, "Adding facts"). The proof of `h'`
is R1 then R2.

**R1 · `ring_nf`** changes the **goal**: it rewrites it into ring normal form, multiplying out every product
and collecting like terms. On an equation it normalizes both sides. Placeholders:
`{α : Type} [CommRing α] (a b : α)`; `[CommRing α]`: `α` has `0 1 + - *` with the usual laws and commutative
`*` (`ℤ`, `ℚ`, `ℝ`, `ℂ` qualify).

| Before | After |
|---|---|
| `⊢ (a - b) * (a + b) = 0` | `⊢ a ^ 2 - b ^ 2 = 0` |
| `⊢ (x - 1) * (x - 4) = 0` | `⊢ 4 - x * 5 + x ^ 2 = 0` |

The second row (`x : ℚ`) shows the layout with numerals: `4 - x * 5 + x ^ 2` is $x^2 - 5x + 4$.

**R2 · `linarith`** **closes** a goal `t = s`, `t ≤ s`, `t < s` (or `False`) that follows from the
hypotheses by adding them with constant coefficients. Any term that is not linear, such as `x ^ 2`, is
treated as a fresh unknown: from `h : x ^ 2 = c` the goal `-c + x ^ 2 = 0` is "unknown `x ^ 2` minus `c`
is `0`", a linear consequence. It also solves the linear equations at the end of each branch. It does not
know `x ^ 2 ≥ 0` or multiply hypotheses (that is `nlinarith`). Placeholders:
`{α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (x c : α)`, i.e. an ordered field (`ℚ`, `ℝ`;
not `ℂ`, which has no order).

| Before | After |
|---|---|
| `h : x ^ 2 = c ⊢ -c + x ^ 2 = 0` | no goals |
| `h : x - c = 0 ⊢ x = c` | no goals |

### Splitting the product

**R3 · `mul_eq_zero`** changes the **context** (with `have h := mul_eq_zero.mp hab`). The lemma is
`mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0`, and `.mp` turns a proof of `a * b = 0` into a proof of
`a = 0 ∨ b = 0`. Placeholders: `{M₀ : Type} [MulZeroClass M₀] [NoZeroDivisors M₀] (a b : M₀)`.
`[MulZeroClass M₀]`: `M₀` has `*` and `0` with `0 * a = a * 0 = 0`. `[NoZeroDivisors M₀]`: `a * b = 0` forces
`a = 0` or `b = 0`. `ℤ`, `ℚ`, `ℝ`, `ℂ` qualify; `ZMod 4` does not ($2 \cdot 2 = 0$).

| Before | After |
|---|---|
| `hab : a * b = 0 ⊢ G` | `h : a = 0 ∨ b = 0 ⊢ G` |

**R4 · `rcases h with h1 | h1`** changes the **goal list and the context**: a hypothesis `h : A ∨ B` is
replaced by two goals, one with `h1 : A`, one with `h1 : B` (`|` separates the two patterns). It accepts a
term, so `rcases mul_eq_zero.mp h' with h1 | h1` does R3 and R4 in one step (and then `h'` stays in the
context). Handle the two goals with `·` bullets. Placeholders: `(A B G : Prop)`.

| Before | After |
|---|---|
| `h : A ∨ B ⊢ G` | `h1 : A ⊢ G`, `h1 : B ⊢ G` |

### Choosing a side of the goal

**R5 · `left`** changes the **goal**: to prove `A ∨ B`, commit to proving `A`. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∨ B` | `⊢ A` |

**R6 · `right`** changes the **goal**: commit to proving `B`. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∨ B` | `⊢ B` |

In each branch the side to pick is the one your `h1` gives: `h1 : x - 2 = 0` goes with `x = 2` (R5, then
R2), `h1 : x + 2 = 0` with `x = -2` (R6, then R2).

### Worked combinations (W1, W2, on other equations)

**W1: a factored form.** `y : ℚ`, `h : y ^ 2 = 9`. R1, then R2 closes the normal form:

```lean-goal
⊢ (y - 3) * (y + 3) = 0
⊢ -9 + y ^ 2 = 0
```

**W2: from the product to the roots.** `h : (y - 1) * (y + 5) = 0`.
`rcases mul_eq_zero.mp h with h1 | h1` (R3 + R4), then in each bullet `left` / `right` (R5, R6) and
`linarith` (R2):

| Before | After |
|---|---|
| `⊢ y = 1 ∨ y = -5` | `h1 : y - 1 = 0 ⊢ y = 1 ∨ y = -5`, `h1 : y + 5 = 0 ⊢ y = 1 ∨ y = -5` |

---

## Part 2 · `quadratic`

Statement: for a real `x` with `h : x ^ 2 - 5 * x + 6 = 0`, `x = 2 ∨ x = 3`. Same plan as Part 1: find the
roots $r, s$ with $r + s = 5$, $rs = 6$, so that $x^2 - 5x + 6 = (x - r)(x - s)$; prove
`h' : (x - r) * (x - s) = 0` by R1 then R2 (after R1 the goal is `6 - x * 5 + x ^ 2 = 0`, and `h` is the
same equation, so R2 closes it); split with R3 + R4; finish each branch with R5 or R6 and R2. No new entries.

---

## Traps

- `ring` cannot prove `h'`: `(x - 2) * (x + 2) = 0` is not an identity (it is false for `x = 0`); it needs
  `h`, and `ring` never reads hypotheses. Use `ring_nf` to expand, then `linarith` to use `h`.
- `linarith` does not use `x ^ 2 ≥ 0` or products of hypotheses. It can close `h'` only because, after
  expanding, `h'` and `h` are the same linear equation in the unknowns `x` and `x ^ 2`.
- Do not `left` / `right` before splitting the product: you do not yet know which root `x` is, and the goal
  you commit to may be false.
- Match sides: `h1 : x + 2 = 0` cannot prove `x = 2`; `linarith` then fails with "linarith failed".
- The order of the factors in `h'` decides which branch is `inl` and which is `inr`.
- `t1; t2` is plain sequencing (the same as `t2` on the next line), and `left`, `right`, `linarith` act on
  the first goal only. After `rcases`, use one `·` bullet per goal, so each branch gets its own side.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| state the factored form | `have h' : (x - r) * (x - s) = 0 := by …` | TACTIC_STATES |
| expand products in the goal | `ring_nf` | R1 |
| close a linear consequence of hypotheses | `linarith` | R2 |
| product is zero → a factor is zero | `mul_eq_zero.mp h'` | R3 |
| split `h : A ∨ B` | `rcases h with h1 \| h1` (or `rcases mul_eq_zero.mp h' with h1 \| h1`) | R4, R3 |
| prove `A ∨ B` by `A` / by `B` | `left` / `right` | R5, R6 |
| see the state | infoview | |
