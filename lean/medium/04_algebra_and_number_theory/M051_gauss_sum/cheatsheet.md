# M051 · Gauss sum: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `induction` on `Nat` (E014). **New here:**
Mathlib's finite sums `∑ i ∈ s, f i` over `Finset.range n`, the lemmas that peel terms off them, and the
`ring` tactic.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddCommMonoid M]`
  is a requirement on `M` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℕ` | `Nat`, the natural numbers `0, 1, 2, …` |
| `range n` | `Finset.range n`, the finite set `{0, 1, …, n - 1}` (`n` elements; `range 0` is empty). It prints without `Finset.` because the file has `open Finset` |
| `∑ i ∈ range n, f i` | `Finset.sum (range n) (fun i => f i)`: `f 0 + f 1 + … + f (n - 1)`. `i` is a bound variable |
| `2 * ∑ i ∈ range (n + 1), i` | `2 * (0 + 1 + … + n)`: the whole `∑ …` is the right factor of `*` |
| `∑ i ∈ range n, (2 * i + 1)` | the body of `∑` (after the comma) takes in `*` and `^` but stops at `+`: `∑ i ∈ s, f i * c` is `∑ i ∈ s, (f i * c)`, while `∑ i ∈ s, f i + c` is `(∑ i ∈ s, f i) + c`. So a body containing `+` needs parentheses |
| `∑ x ∈ range n, f x + f n` | `(∑ x ∈ range n, f x) + f n` (the body stops at `+`, row above): after R5 the last term sits outside the sum. Lean renamed the bound variable `i` to `x`; the name does not matter, `rw [ih]` still matches |
| `n + 1 + 1` | `(n + 1) + 1`: the `succ` case of an induction substitutes `n + 1` for `n`, so `range (n + 1)` becomes `range (n + 1 + 1)` |
| `case zero`, `case succ` | the two goals made by `induction` (R1) |
| `inst✝ : AddCommMonoid M` | an unnamed type-class instance from a placeholder bracket |

---

## Part 1 · `gauss`

Statement: `2 * ∑ i ∈ range (n + 1), i = n * (n + 1)`, i.e. $2\,(0 + 1 + \dots + n) = n(n + 1)$ for every
$n \in \mathbb{N}$. Stated with the factor `2` so that no division appears.

### Splitting `n` into `0` and `k + 1`

**R1 · `induction n with | zero => ?_ | succ k ih => ?_`** changes the **goal list and the context**: one goal
becomes the `zero` goal and the `succ` goal. In the `succ` goal, `n` is gone and the context gains `k : ℕ` and
`ih : P k`. In the exercise write the tactics directly after each `=>`:
`induction n with | zero => tac₀ | succ n ih => tac₁` (reusing the name `n` is fine). Placeholders:
`(P : ℕ → Prop) (n : ℕ)`.

| Before | After |
|---|---|
| `n : ℕ ⊢ P n` | `⊢ P 0`, `k : ℕ, ih : P k ⊢ P (k + 1)` |

### The `zero` case

**R2 · `Finset.sum_range_zero`** changes the **goal**: the empty sum is `0`. The lemma is
`∑ i ∈ range 0, f i = 0`. Placeholders: `{M : Type} [AddCommMonoid M] (f : ℕ → M)`. `AddCommMonoid M` means
`M` has a commutative, associative `+` with a `0`, which is all a finite sum needs; `ℕ`, `ℤ`, `ℝ` qualify.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ range 0, f i)` | `⊢ P 0` |

**R3 · `Finset.sum_range_one`** changes the **goal**: a sum over `range 1 = {0}` is its single term. The lemma
is `∑ i ∈ range 1, f i = f 0`. Placeholders: as in R2.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ range 1, f i)` | `⊢ P (f 0)` |

**R4 · `simp`** **closes** the `zero` case. It does by itself what R2/R3 do by hand, through its own simp
lemmas `Finset.range_zero : range 0 = ∅`, `Finset.sum_empty` (a sum over `∅` is `0`), `Finset.range_one :
range 1 = {0}` and `Finset.sum_singleton` (a sum over `{a}` is `f a`), plus `0 + 1 = 1`, `0 * a = 0`,
`a * 0 = 0`, `a * 1 = a` and `0 ^ 2 = 0`; you need not name any of them. In `gauss` the `zero` goal is
`⊢ 2 * ∑ i ∈ range (0 + 1), i = 0 * (0 + 1)`; in `sum_odd` it is `⊢ ∑ i ∈ range 0, (2 * i + 1) = 0 ^ 2`.

### The `succ` case

**R5 · `rw [Finset.sum_range_succ]`** changes the **goal**: the sum up to `n + 1` becomes the sum up to `n`
plus the last term. The lemma is `∑ x ∈ range (n + 1), f x = ∑ x ∈ range n, f x + f n`. Placeholders:
`{M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ)`. In the exercise `n` is `k + 1` (or `n + 1`), so the sum
over `range (k + 1 + 1)` becomes one over `range (k + 1)`, the range `ih` talks about. (`Finset.sum_range_succ'`
with a `'` peels off the *first* term instead; not what you want here.)

| Before | After |
|---|---|
| `⊢ P (∑ x ∈ range (n + 1), f x)` | `⊢ P (∑ x ∈ range n, f x + f n)` |

**R6 · `rw [mul_add]`** changes the **goal**: it distributes a factor over a sum. The lemma is
`mul_add : a * (b + c) = a * b + a * c`. Placeholders: `{α : Type} [Semiring α] (a b c : α)` (α has `+`, `*`,
`0`, `1` with the distributive law; `ℕ`, `ℤ`, `ℝ` qualify). In `gauss`, after R5 the goal is
`2 * (∑ … + (k + 1)) = …`, and `ih`'s left side `2 * ∑ …` is not there yet. R6 makes it appear.

| Before | After |
|---|---|
| `⊢ P (a * (b + c))` | `⊢ P (a * b + a * c)` |

**R7 · `rw [ih]`** changes the **goal**: it replaces the left side of the induction hypothesis by its right
side. `rw` needs that left side to appear literally (up to the name of the bound variable). Placeholders:
`(c s t u : ℕ) (ih : c * s = t)`.

| Before | After |
|---|---|
| `ih : c * s = t ⊢ P (c * s + c * u)` | `ih : c * s = t ⊢ P (t + c * u)` |

**R8 · `ring`** **closes** an equation that holds in every commutative (semi)ring, `ℕ` included: it expands
`+`, `*`, `^` by a numeral, and compares. It treats a remaining `∑` as an unknown and does not use hypotheses,
so it works only after R7 has removed the sum. Example: `(a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2`.

### Worked combination (W1, on a sum that is not the exercise's)

**W1: sum of cubes**, `4 * ∑ i ∈ range (n + 1), i ^ 3 = (n * (n + 1)) ^ 2`. R1, then `simp` (R4) on `zero`. On
`succ`, R5, R6, R7, R8:

```lean-goal
⊢ 4 * ∑ i ∈ range (k + 1 + 1), i ^ 3 = ((k + 1) * (k + 1 + 1)) ^ 2
⊢ 4 * (∑ x ∈ range (k + 1), x ^ 3 + (k + 1) ^ 3) = ((k + 1) * (k + 1 + 1)) ^ 2
⊢ 4 * ∑ x ∈ range (k + 1), x ^ 3 + 4 * (k + 1) ^ 3 = ((k + 1) * (k + 1 + 1)) ^ 2
⊢ (k * (k + 1)) ^ 2 + 4 * (k + 1) ^ 3 = ((k + 1) * (k + 1 + 1)) ^ 2
```

---

## Part 2 · `sum_odd`

Statement: `∑ i ∈ range n, (2 * i + 1) = n ^ 2`, i.e. $1 + 3 + \dots + (2n - 1) = n^2$: the first $n$ odd
numbers sum to $n^2$. Same plan as Part 1 with R1, R4, R5, R7, R8. There is no factor in front of the sum, so
R6 is not needed: after R5 the IH's left side `∑ i ∈ range k, (2 * i + 1)` is already in the goal. The
`zero` goal is the empty sum `∑ i ∈ range 0, … = 0 ^ 2` (R2 inside R4).

**W2: `∑ i ∈ range n, (3 * i ^ 2 + 3 * i + 1) = n ^ 3`.** Same shape; on `succ`, R5, R7, R8:

```lean-goal
⊢ ∑ i ∈ range (k + 1), (3 * i ^ 2 + 3 * i + 1) = (k + 1) ^ 3
⊢ ∑ x ∈ range k, (3 * x ^ 2 + 3 * x + 1) + (3 * k ^ 2 + 3 * k + 1) = (k + 1) ^ 3
⊢ k ^ 3 + (3 * k ^ 2 + 3 * k + 1) = (k + 1) ^ 3
```

---

## Traps

- `rw [ih]` fails in `gauss` right after R5: the goal has `2 * (∑ … + (k + 1))`, not `2 * ∑ …`. Distribute
  first (R6).
- `ring` cannot see inside `∑`. Call it only after `rw [ih]` has replaced the sum by a polynomial.
- `gauss` sums over `range (n + 1)` (terms `0 … n`), `sum_odd` over `range n` (terms `0 … n - 1`). That is why
  their `zero` goals differ: a one-term sum and an empty sum. `simp` handles both.
- Mathlib has the closed form of `0 + 1 + … + n` as a lemma; it is on the `BANNED:` line, so prove it.
- Avoid stating the closed form with `/ 2` in `ℕ`: `ℕ` division rounds down, which is why the spec multiplies
  by `2` instead.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| prove `∀ n` by adding one term at a time | `induction n with \| zero => … \| succ n ih => …` | R1 |
| empty / one-term sum | `Finset.sum_range_zero` / `Finset.sum_range_one` | R2, R3 |
| close the `zero` case | `simp` | R4 |
| peel off the last term | `rw [Finset.sum_range_succ]` | R5 |
| `a * (b + c) → a * b + a * c` | `rw [mul_add]` | R6 |
| replace the IH's left side | `rw [ih]` | R7 |
| polynomial identity in `ℕ` | `ring` | R8 |
| see the state | infoview | |
