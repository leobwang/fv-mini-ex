# M052 · Geometric sum: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `induction` on `ℕ` (E014) and `omega`
(E011). **New here:** Mathlib's finite sums `∑ i ∈ range n, f i`, the real numbers `ℝ`, and the
algebra lemmas `pow_succ`, `mul_add` and the tactic `ring`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Monoid M]`
  is a requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `range n` | `Finset.range n`, the finite set `{0, 1, …, n - 1}` (empty for `n = 0`). A `Finset α` is Mathlib's type of finite sets of elements of `α`; `open Finset` lets you drop the prefix |
| `∑ i ∈ range n, f i` | $\sum_{i=0}^{n-1} f(i)$; `i` is a bound variable, so Lean may rename it (`∑ x ∈ …` after a `rw`) |
| `∑ i ∈ range n, 2 ^ i + 1` | `(∑ i ∈ range n, 2 ^ i) + 1`: the summand stops before a `+`. A `+` inside the summand is printed with brackets: `∑ i ∈ range n, (2 * i + 1)`. `*` and `^` bind tighter, so they stay inside: `∑ i ∈ range n, 2 * 3 ^ i + 1` is `(∑ i ∈ range n, 2 * 3 ^ i) + 1` |
| `3 * ∑ i ∈ range n, f i + c` | `(3 * ∑ …) + c` |
| `ℝ` | Mathlib's real numbers. Unlike `ℕ`, `-` is true subtraction there |
| `r ^ i` | `r` to the natural-number power `i : ℕ` (`Monoid.npow`), for `r : ℝ` or `r : ℕ` |
| `case zero`, `case succ` | the two goals `induction` produced |
| `ih : …` | the induction hypothesis: the statement for `n`, in the `succ` goal for `n + 1` |

---

## Part 1 · `geom_two`

Statement: $\left(\sum_{i=0}^{n-1} 2^i\right) + 1 = 2^n$ in `ℕ`. (Written with `+ 1` on the left, not
`- 1` on the right, because `ℕ` subtraction truncates at 0.)

### Induction

**R1 · `induction n with | zero => ?_ | succ n ih => ?_`** changes the **goal list and the context**: the goal
`P n` becomes `P 0` and `P (n + 1)`, and the second goal gets `ih : P n`. Writing `?_` in each case leaves
the case open as an ordinary goal, so the cases can be handled one after another (`· simp` for the first).
You can also write each case's tactics directly after its `=>`, as in E014. Placeholders: `(P : ℕ → Prop) (n : ℕ)`.

| Before | After |
|---|---|
| `n : ℕ ⊢ P n` | `⊢ P 0`, `n : ℕ, ih : P n ⊢ P (n + 1)` |

### The base case

`simp` closes both base cases by itself: it uses R2 and R3 (R2 in the form `range 0 = ∅`, sum over `∅` is
`0`), plus `0 + a = a`, `a * 0 = 0` and `a - a = 0`.

**R2 · `rw [Finset.sum_range_zero]`** changes the **goal**. The lemma is `∑ k ∈ range 0, f k = 0`.
Placeholders: `{β : Type} [AddCommMonoid β] (f : ℕ → β)`; `[AddCommMonoid β]` says β has a commutative `+`
with `0`, as `ℕ` and `ℝ` do.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ range 0, f i)` | `⊢ P 0` |

**R3 · `rw [pow_zero]`** changes the **goal**. The lemma is `a ^ 0 = 1`. Placeholders:
`{M : Type} [Monoid M] (a : M)`; `[Monoid M]` says M has an associative `*` with `1` (`ℕ`, `ℝ` qualify).

| Before | After |
|---|---|
| `⊢ P (a ^ 0)` | `⊢ P 1` |

### The step case

**R4 · `rw [Finset.sum_range_succ]`** changes the **goal**: the sum up to `n + 1` becomes the sum up to `n`
plus the last term. The lemma is `∑ x ∈ range (n + 1), f x = ∑ x ∈ range n, f x + f n`. Placeholders:
`{β : Type} [AddCommMonoid β] (f : ℕ → β) (n : ℕ)`. It finds `f` by itself: in `∑ i ∈ range (n + 1), 2 ^ i`,
`f` is `fun i => 2 ^ i`.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ range (n + 1), f i)` | `⊢ P (∑ x ∈ range n, f x + f n)` |

**R5 · `rw [pow_succ]`** changes the **goal**. The lemma is `pow_succ : a ^ (n + 1) = a ^ n * a` (the factor
comes out on the right; `pow_succ'` puts it on the left). Placeholders: `{M : Type} [Monoid M] (a : M) (n : ℕ)`.
`rw` rewrites the first match and every other copy of it, so pick the form your goal needs.

| Before | After |
|---|---|
| `⊢ P (a ^ (n + 1))` | `⊢ P (a ^ n * a)` |

**R6 · `omega`** **closes** a goal of linear arithmetic over `ℕ` or `ℤ` (`+`, `-`, `*` by a numeral, `≤`, `=`),
using the hypotheses in the context. Any other subterm (a sum, `2 ^ n`, `g n`) is treated as an opaque
number, an *atom*; the same text is the same atom. So it proves `s + g n + 1 = g n * 2` from `s + 1 = g n`.
It fails if the atoms differ between goal and hypothesis (`2 ^ (n + 1)` vs `2 ^ n`): that is why R5 comes
first. Placeholders: `(s : ℕ) (g : ℕ → ℕ) (n : ℕ)`.

| Before | After |
|---|---|
| `h : s + 1 = g n ⊢ s + g n + 1 = g n * 2` | ∅ |

**W3: R4, R5, R6 on base 3.** `∑ i ∈ range n, 2 * 3 ^ i + 1 = 3 ^ n`, in the `succ` case:

```lean-goal
⊢ ∑ i ∈ range (n + 1), 2 * 3 ^ i + 1 = 3 ^ (n + 1)
⊢ ∑ x ∈ range n, 2 * 3 ^ x + 2 * 3 ^ n + 1 = 3 ^ n * 3
```

with `ih : ∑ i ∈ range n, 2 * 3 ^ i + 1 = 3 ^ n`. The atoms are `∑ x ∈ range n, 2 * 3 ^ x` (the same as
`ih`'s up to the bound variable's name) and `3 ^ n`; `omega` closes it.

---

## Part 2 · `geom_real`

Statement: $(r - 1)\sum_{i=0}^{n-1} r^i = r^n - 1$ for `r : ℝ`. Same induction (R1, base case by `simp`,
R4), but the sum sits under a factor `(r - 1)`, and over `ℝ` you finish with `ring` instead of `omega`.

**R7 · `rw [mul_add]`** changes the **goal**: it distributes a factor over a sum. The lemma is
`mul_add : a * (b + c) = a * b + a * c`. Placeholders: `{R : Type} [CommRing R] (a b c : R)`; `[CommRing R]`
says R has `+`, `-`, `*` with the usual laws and commutative `*` (`ℝ`, `ℤ`, `ℂ` qualify; `ℕ` meets the weaker
requirement `mul_add` really needs). After R4 the goal has `(r - 1) * (∑ … + r ^ n)`; R7 turns it into
`(r - 1) * ∑ … + (r - 1) * r ^ n`, whose first summand is exactly the left side of `ih`, so `rw [ih]` applies.

| Before | After |
|---|---|
| `⊢ P (a * (b + c))` | `⊢ P (a * b + a * c)` |

**R8 · `ring`** **closes** an equation that holds in every commutative ring (or semiring such as `ℕ`). It
handles powers with a symbolic exponent: it knows `a ^ (n + 1) = a ^ n * a`. It does not use hypotheses, so
substitute `ih` first. Placeholders: `{R : Type} [CommRing R] (a b : R) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ (a - b) * a ^ n = a ^ (n + 1) - b * a ^ n` | ∅ |

### Worked combinations (W1–W2, odd numbers instead of powers)

**W1: R4, `rw [ih]`, R8.** $\sum_{i<n}(2i + 1) = n^2$, in the `succ` case:

```lean-goal
⊢ ∑ i ∈ range (n + 1), (2 * i + 1) = (n + 1) ^ 2
⊢ ∑ x ∈ range n, (2 * x + 1) + (2 * n + 1) = (n + 1) ^ 2
⊢ n ^ 2 + (2 * n + 1) = (n + 1) ^ 2
```

**W2: a factor in front, so R7 comes before `rw [ih]`.** $3\sum_{i<n}(2i + 1) = 3n^2$, with
`ih : 3 * ∑ i ∈ range n, (2 * i + 1) = 3 * n ^ 2`:

```lean-goal
⊢ 3 * ∑ i ∈ range (n + 1), (2 * i + 1) = 3 * (n + 1) ^ 2
⊢ 3 * (∑ x ∈ range n, (2 * x + 1) + (2 * n + 1)) = 3 * (n + 1) ^ 2
⊢ 3 * ∑ x ∈ range n, (2 * x + 1) + 3 * (2 * n + 1) = 3 * (n + 1) ^ 2
⊢ 3 * n ^ 2 + 3 * (2 * n + 1) = 3 * (n + 1) ^ 2
```

`ring` closes the last line.

---

## Traps

- `ℕ` subtraction truncates at 0 (`1 - 2 = 0`), and `ring` cannot reason about it. That is why `geom_two` is
  stated as `… + 1 = 2 ^ n` and not as `… = 2 ^ n - 1`: the goal stays free of `-`.
- `rw [ih]` needs the left side of `ih` literally. In Part 2, right after R4 it sits inside
  `(r - 1) * (… + …)`: distribute with R7 first.
- `ring` ignores hypotheses: it cannot use `ih`. Over `ℕ` with `ih` needed, use `omega` (linear in atoms), or
  `rw [ih]` first and then `ring`.
- `omega` matches atoms by their text: `2 ^ (n + 1)` and `2 ^ n` are unrelated to it. Rewrite with R5 first.
- `pow_succ` is `a ^ n * a`, `pow_succ'` is `a * a ^ n`.
- `∑ i ∈ range n, f i + 1` is `(∑ …) + 1`, not `∑ (f i + 1)`.
- The library's geometric-sum lemmas (`geom_sum_eq`, `geom_sum_mul`, `mul_geom_sum`, `Nat.geomSum_eq`,
  `geom_sum_mul_neg`) are banned: they are the statements themselves.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction with both cases open | `induction n with \| zero => ?_ \| succ n ih => ?_` | R1 |
| base case (empty sum, `a ^ 0`) | `simp` | R2, R3 |
| peel the last term | `rw [sum_range_succ]` | R4 |
| `a ^ (n + 1) → a ^ n * a` | `rw [pow_succ]` | R5 |
| linear goal over `ℕ` with atoms, uses `ih` | `omega` | R6 |
| `a * (b + c) → a * b + a * c` | `rw [mul_add]` | R7 |
| substitute the induction hypothesis | `rw [ih]` | TACTIC_STATES |
| ring identity, symbolic exponents | `ring` | R8 |
| see the state | infoview | |
