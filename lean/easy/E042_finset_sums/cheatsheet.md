# E042 · Finset sums: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `rw [...]` and `rw [← ...]`, `simp [...]`, `decide`, `exact`.
**New here:** Mathlib's finite sets `Finset ι`, `Finset.range n`, the big-sum notation `∑ i ∈ s, f i`, and four
lemmas: peel the last term off a sum over `range` (`sum_range_succ`), the empty sum (`sum_range_zero`), and
linearity (`sum_add_distrib`, `mul_sum`).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change (here none
  do: every entry changes the goal).
- `P` is "the rest of your goal" (`P : M → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{M : Type}` is any type. A bracket such as `[AddCommMonoid M]` is
  a requirement on `M` (a *type class*); each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

**What a finite sum is in Mathlib.** `Finset ι` is the type of finite sets of elements of `ι` (a list with
duplicates and order forgotten). `Finset.range n : Finset ℕ` is `{0, 1, …, n - 1}`; `range 0` is empty. For
`s : Finset ι` and `f : ι → M`, `∑ i ∈ s, f i` is `Finset.sum s f`, the sum of `f i` over `i ∈ s`; it needs a
commutative `+` with a `0` on `M` (`[AddCommMonoid M]`), because a finite set has no order to add in. So

$$\sum_{i \in \mathrm{range}\,n} f\,i \;=\; f\,0 + f\,1 + \dots + f\,(n-1), \qquad \sum_{i \in \mathrm{range}\,0} f\,i = 0.$$

The file says `open Finset`, so `range`, `sum_range_succ` etc. can be written without the `Finset.` prefix.

## Reading the goals

| You see | It means |
|---|---|
| `Finset ℕ` | finite sets of natural numbers |
| `range n` | `Finset.range n = {0, 1, …, n - 1}` |
| `∑ i ∈ s, f i` | the sum of `f i` over all `i ∈ s` (`\sum`, `\in`); the name `i` is a bound variable |
| `∑ x ∈ range n, f x` | the same sum: after a `rw`, Lean renames the bound variable to the lemma's (`x`, `k`) |
| `∑ i ∈ s, (f i + g i)` | the sum of `f i + g i`; the parentheses mark where the summand ends |
| `∑ x ∈ s, f x + ∑ x ∈ s, g x` | `(∑ f) + (∑ g)`: a summand stops before `+`, but not before `*` |
| `a * ∑ i ∈ s, f i` | `a` times the whole sum |
| `inst✝ : AddCommMonoid M` | the unnamed type-class argument, shown in the context |

---

## Part 1 · `sum_squares_five`

Statement: `0² + 1² + 2² + 3² + 4² = 30`, written as a sum over `range 5`. Unroll the sum into its five terms
(R4, built from R1–R3) and let `simp` do the arithmetic.

**R1 · `rw [Finset.sum_range_succ]`** changes the **goal**: the last term comes out of the sum. Lemma:
`Finset.sum_range_succ (f : ℕ → M) (n : ℕ) : ∑ x ∈ range (n + 1), f x = ∑ x ∈ range n, f x + f n`.
Placeholders: `{M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ)`; `ℕ`, `ℤ`, `ℝ` meet `[AddCommMonoid M]`.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ range (n + 1), f i)` | `⊢ P (∑ x ∈ range n, f x + f n)` |

**R2 · R1 on `range (n + 2)` and on a numeral `range 3`** changes the **goal** the same way. `rw` matches
`n + 2` against the lemma's `?m + 1` with `?m := n + 1`, and the numeral `3` with `?m := 2`; no preliminary
rewrite is needed. Placeholders: as in R1.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ range (n + 2), f i)` | `⊢ P (∑ x ∈ range (n + 1), f x + f (n + 1))` |
| `⊢ P (∑ i ∈ range 3, f i)` | `⊢ P (∑ x ∈ range 2, f x + f 2)` |

**R3 · `rw [Finset.sum_range_zero]`** changes the **goal**: the empty sum is `0`. Lemma:
`Finset.sum_range_zero (f : ℕ → M) : ∑ k ∈ range 0, f k = 0`. It is a `simp` lemma, so `simp` uses it without
being told. Placeholders: `{M : Type} [AddCommMonoid M] (f : ℕ → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ k ∈ range 0, f k)` | `⊢ P 0` |

**R4 · `simp [Finset.sum_range_succ]`** changes the **goal**: it applies R2 until it reaches `range 0`, then R3
and `0 + a = a`, leaving the terms in order. When the terms are numerals, `simp` also evaluates them, so a
numeric goal closes. Placeholders: `{M : Type} [AddCommMonoid M] (f : ℕ → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ range 3, f i)` | `⊢ P (f 0 + f 1 + f 2)` |

**W1.** On numerals, R4 closes the goal outright:

```lean-goal
⊢ ∑ i ∈ range 4, (2 * i + 1) = 16
```

`decide` also closes such small closed goals: `range 5` and the sum are computable (TACTIC_STATES, "Closing").

## Part 2 · `peel_two`

Statement: a sum over `range (n + 2)` equals the sum over `range n` plus its last two terms `f n` and
`f (n + 1)`. Peel off the last term twice: R2 (for `n + 2`), then R1 (for `n + 1`).

After the second rewrite both sides are the same expression, and `rw` closes a goal of the form `a = a` with
`rfl` by itself: no tactic is left to write.

**W2.** The same move three times on `range (m + 3)`; after the third `rw` the goal is closed:

```lean-goal
⊢ ∑ i ∈ range (m + 3), g i = ∑ i ∈ range m, g i + g m + g (m + 1) + g (m + 2)
⊢ ∑ x ∈ range (m + 2), g x + g (m + 2) = ∑ i ∈ range m, g i + g m + g (m + 1) + g (m + 2)
⊢ ∑ x ∈ range (m + 1), g x + g (m + 1) + g (m + 2) = ∑ i ∈ range m, g i + g m + g (m + 1) + g (m + 2)
```

## Part 3 · `sum_linear`

Statement: `∑ (f i + 2 · g i) = ∑ f i + 2 · ∑ g i` over `range n`. Split the sum of a `+` (R5), then match the
constant `2` with the sum it multiplies (R6).

**R5 · `rw [Finset.sum_add_distrib]`** changes the **goal**: a sum of `+` becomes a `+` of sums. Lemma:
`Finset.sum_add_distrib : ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑ x ∈ s, g x` (`s`, `f`, `g` implicit: `rw`
finds them in the goal). Placeholders: `{ι M : Type} [AddCommMonoid M] (s : Finset ι) (f g : ι → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ s, (f i + g i))` | `⊢ P (∑ x ∈ s, f x + ∑ x ∈ s, g x)` |

**R6 · `rw [Finset.mul_sum]`** changes the **goal**: a constant times a sum becomes the sum of constant times
each term; `rw [← Finset.mul_sum]` goes the other way. Lemma:
`Finset.mul_sum (s : Finset ι) (f : ι → R) (a : R) : a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`.
Placeholders: `{ι R : Type} [Semiring R] (s : Finset ι) (f : ι → R) (a : R)`; `[Semiring R]` (`+`, `*`, `0`, `1`
with distributivity) is met by `ℕ`, `ℤ`, `ℝ` (the lemma itself asks only for `[NonUnitalNonAssocSemiring R]`: `+`, `*`, `0` and distributivity, no `1`).

| Before | After `rw [Finset.mul_sum]` |
|---|---|
| `⊢ P (a * ∑ i ∈ s, f i)` | `⊢ P (∑ i ∈ s, a * f i)` |

| Before | After `rw [← Finset.mul_sum]` |
|---|---|
| `⊢ P (∑ i ∈ s, a * f i)` | `⊢ P (a * ∑ i ∈ s, f i)` |

Either direction works when one side of the goal has `a * ∑ …` and the other `∑ …, a * …`: rewrite one into
the other, and `rw` closes the remaining `a = a` with `rfl`.

**W3.** Three summands: R5 twice (`+` groups to the left, so the first R5 splits off `5 * k i`), then R6 closes
the goal:

```lean-goal
⊢ ∑ i ∈ s, (f i + g i + 5 * k i) = ∑ i ∈ s, f i + ∑ i ∈ s, g i + 5 * ∑ i ∈ s, k i
⊢ ∑ x ∈ s, (f x + g x) + ∑ x ∈ s, 5 * k x = ∑ i ∈ s, f i + ∑ i ∈ s, g i + 5 * ∑ i ∈ s, k i
⊢ ∑ x ∈ s, f x + ∑ x ∈ s, g x + ∑ x ∈ s, 5 * k x = ∑ i ∈ s, f i + ∑ i ∈ s, g i + 5 * ∑ i ∈ s, k i
```

---

## Traps

- `rw` rewrites the **first** match and every identical copy of it. In `peel_two` the left side is the only
  sum over `range (n + 2)`, so each `rw [sum_range_succ]` peels the left side; on a goal with several different
  `range (_ + 1)` sums, pass the arguments: `rw [sum_range_succ f n]`.
- `rw [sum_range_succ]` does not rewrite `range n` for a variable `n`: `n` is not of the form `?m + 1`. Only
  `n + 1`, `n + 2`, … and numerals `≥ 1` match.
- The summand of `∑` stops before a `+` (or `-`) but not before a `*`: `∑ i ∈ s, f i + c` is
  `(∑ i ∈ s, f i) + c`, while `∑ i ∈ s, 2 * g i` is `∑ i ∈ s, (2 * g i)`. A sum of `f i + g i` must be written
  `∑ i ∈ s, (f i + g i)`, and that is how Lean prints it.
- `Finset.mul_sum` is for a constant on the left (`2 * ∑ …`). For `(∑ …) * 2` the lemma is `Finset.sum_mul`.
- After `rw` closes the goal with `rfl`, a following tactic fails with "no goals". Stop when the goal is gone.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| peel the last term off `∑ over range (n + 1)` | `rw [sum_range_succ]` | R1 |
| peel off `range (n + 2)` or `range 3` | `rw [sum_range_succ]` (no rewrite of `n + 2` first) | R2 |
| the empty sum | `rw [sum_range_zero]` (`simp` does it by itself) | R3 |
| evaluate a sum over `range 5` | `simp [sum_range_succ]` (or `decide`) | R4 |
| peel two terms | `rw [sum_range_succ, sum_range_succ]` | R2, R1 |
| `∑ (f + g)` → `∑ f + ∑ g` | `rw [sum_add_distrib]` | R5 |
| `a * ∑ f` ↔ `∑ a * f` | `rw [mul_sum]` / `rw [← mul_sum]` | R6 |
| see the state | infoview | |
