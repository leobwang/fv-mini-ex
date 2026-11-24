# E071 · gcongr under sums: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `exact`, `have`, applying a `∀` hypothesis to an argument,
`↔` and its directions. No Mathlib is assumed: sums, products and `range` are explained below.
**New here:** Mathlib's finite sums and products over a `Finset`, the tactic `gcongr` ("generalized
congruence") that compares two sides of the same shape piece by piece, `nlinarith` for polynomial
inequalities over `ℝ`, and `Finset.mem_range`.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**), lists
the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`); `Q : Prop` is an arbitrary goal.
- Placeholders are written as Lean binders. `{ι : Type}` is any type (here: the type of indices).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Finset ι` | a finite set of elements of type `ι` (Mathlib's `Finset`) |
| `range n` | `Finset.range n`, the finset `{0, 1, …, n - 1}` of naturals (`open Finset` drops the prefix) |
| `∑ i ∈ s, f i` | `f i` summed over every `i ∈ s` (`Finset.sum s f`); `0` when `s` is empty |
| `∏ i ∈ s, f i` | `f i` multiplied over every `i ∈ s` (`Finset.prod s f`); `1` when `s` is empty |
| `i ∈ s` | membership of `i` in the finset `s` |
| `∀ i ∈ s, P i` | `∀ i, i ∈ s → P i`: two arguments, an index and a membership proof |
| `∀ i < n, P i` | `∀ i, i < n → P i` |
| `∀ (i : ι), P i` | the same as `∀ i, P i`; Lean prints the binder with its type |
| `a✝ : i ∈ s` | a hypothesis with no usable name (you did not name it in `gcongr with`) |
| `x ^ 2` | `x` squared (`^` with a natural-number exponent) |
| `f i ^ 2` | `(f i) ^ 2`: function application binds tighter than `^` |
| `this : 1 ≤ f i` | the fact added by an unnamed `have := …`; Lean calls it `this` |
| `mem_range` | `Finset.mem_range`; `open Finset` lets you drop the prefix (R5) |
| `case h`, `case h1` | the name gcongr gives the term goal; ignore it |

---

## Part 1 · `sum_mono`

Statement: for `f g : ℕ → ℝ` with `f i ≤ g i` for **every** `i`, `∑ i ∈ range n, f i ≤ ∑ i ∈ range n, g i`.
Both sides sum over the same index set; only the term differs.

**R1 · `gcongr with i hi`** on a sum changes the **goal and the context**. `gcongr` matches the two sides of
`≤` against each other, finds the parts where they differ, and replaces the goal by "differing part on the
left `≤` differing part on the right", using the monotonicity of `∑`. Under a binder it introduces a fresh
index; `with i hi` names it `i` and its membership proof `hi : i ∈ s`. Placeholders:
`{ι : Type} (s : Finset ι) (f g : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i` | `i : ι, hi : i ∈ s ⊢ f i ≤ g i` |

**R2 · `h a` / `h a ha`** closes the goal or adds to the **context**. A hypothesis `h : ∀ i, P i` applied to
`a` is a proof of `P a`, so `exact h a` closes `⊢ P a`. A bounded `h : ∀ i ∈ s, P i` needs the membership proof
too: `h a ha`. With `have hP := h a ha` the instance enters the context. Placeholders:
`{ι : Type} (s : Finset ι) (P : ι → Prop) (Q : Prop) (a : ι) (ha : a ∈ s)`.

| Before | After |
|---|---|
| `⊢ P a` | no goals (`exact h a`) |
| `⊢ Q` | `hP : P a ⊢ Q` (`have hP := h a ha`) |

**W1: gcongr peels several layers.** On `∑ i ∈ s, 2 * f i ≤ ∑ i ∈ s, 2 * g i` the common factor `2 *` is
peeled too (multiplying by `2 ≥ 0` is monotone, and gcongr proves `0 ≤ 2` itself):

| Before | After `gcongr with i hi` |
|---|---|
| `⊢ ∑ i ∈ s, 2 * f i ≤ ∑ i ∈ s, 2 * g i` | `hi : i ∈ s ⊢ f i ≤ g i` |

---

## Part 2 · `sum_le_sq`

Statement: for `f : ℕ → ℝ` with `1 ≤ f i` for every `i ∈ range n`, `∑ f i ≤ ∑ f i ^ 2`. The two terms have
different shapes, so R1 leaves the whole term inequality `f i ≤ f i ^ 2`; it is true because `f i ≥ 1`.

**R3 · `nlinarith`** **closes** a polynomial (in)equality over an ordered field such as `ℝ` that follows from
the hypotheses in the context. It adds products of pairs of hypotheses and squares to the list, then runs
`linarith` (which handles only linear combinations). It does not look inside `∀` hypotheses: instantiate
first with R2. Placeholders: `(x : ℝ) (hx : 2 ≤ x)`.

| Before | After |
|---|---|
| `hx : 2 ≤ x ⊢ 2 * x ≤ x ^ 2` | no goals |

**W3: R1 → R2 → R3** on `∑ i ∈ s, 2 * f i ≤ ∑ i ∈ s, f i ^ 2` with `h : ∀ i ∈ s, 2 ≤ f i`:

| Step | State |
|---|---|
| start | `⊢ ∑ i ∈ s, 2 * f i ≤ ∑ i ∈ s, f i ^ 2` |
| `gcongr with i hi` | `hi : i ∈ s ⊢ 2 * f i ≤ f i ^ 2` |
| `have h2 := h i hi` | `h2 : 2 ≤ f i ⊢ 2 * f i ≤ f i ^ 2` |
| `nlinarith` | no goals |

---

## Part 3 · `prod_mono`

Statement: for `f g : ℕ → ℕ` with `f i ≤ g i` for every `i < n`, `∏ i ∈ range n, f i ≤ ∏ i ∈ range n, g i`.
The hypothesis is phrased with `i < n`, but gcongr hands you `hi : i ∈ range n`; translate with R5.

**R4 · `gcongr with i hi`** on a product changes the **goal and the context**, as R1. A product is monotone
only in **nonnegative** factors, so gcongr also needs `0 ≤ f i`. It tries to prove such side goals itself
(with `positivity`); in `ℕ` that always succeeds, so only the term goal is left. Placeholders:
`{ι : Type} (s : Finset ι) (f g : ι → ℕ)`.

| Before | After |
|---|---|
| `⊢ ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i` | `i : ι, hi : i ∈ s ⊢ f i ≤ g i` |

**R5 · `Finset.mem_range`** changes the **context** (used as `.mp`). The lemma is
`Finset.mem_range : m ∈ range n ↔ m < n`; `.mp` is its left-to-right direction, so
`Finset.mem_range.mp hm : m < n` for `hm : m ∈ range n`. Use it inline as an argument (`h i (… .mp hi)`) or
name it with `have`. Placeholders: `(m n : ℕ) (hm : m ∈ range n)`.

| Before | After `have h' : m < n := Finset.mem_range.mp hm` |
|---|---|
| `hm : m ∈ range n ⊢ Q` | `h' : m < n ⊢ Q` |

**W2: products over `ℝ` keep the side goal.** In `ℝ`, `0 ≤ f i` is not automatic, so `gcongr with i hi` on
`∏ i ∈ s, f i ≤ ∏ i ∈ s, g i` leaves two goals, the side goal first (not yet introduced):

```lean-goal
⊢ ∀ i ∈ s, 0 ≤ f i
⊢ f i ≤ g i
```

**W4: R4 → R2 fed by R5** on `∏ k ∈ range m, (a k + 1) ≤ ∏ k ∈ range m, (b k + 1)` with
`h : ∀ k < m, a k ≤ b k`: gcongr peels the product and the `+ 1`, then `exact h k (Finset.mem_range.mp hk)`.

| Before | After `gcongr with k hk` |
|---|---|
| `⊢ ∏ k ∈ range m, (a k + 1) ≤ ∏ k ∈ range m, (b k + 1)` | `hk : k ∈ range m ⊢ a k ≤ b k` |

---

## Traps

- The obvious library lemmas for term-wise comparison of sums and products are banned; `gcongr` is the point.
- `gcongr` without `with` still introduces the index and membership, but under inaccessible names such as
  `a✝ : i ∈ s`. Name them: `gcongr with i hi`.
- `h : ∀ i ∈ s, P i` takes **two** arguments (`h i hi`); `h : ∀ i, P i` takes one (`h i`). Passing `hi` to the
  latter is an error.
- `h : ∀ i < n, …` wants `i < n`, not `i ∈ range n`: convert with `Finset.mem_range.mp` (R5).
- `linarith` fails on `x ≤ x ^ 2`-type goals (they are not linear); use `nlinarith` (R3), and first bring the
  instantiated hypothesis into the context (R2): neither tactic reads a `∀`.
- Over `ℝ`, gcongr on a product leaves side goals `0 ≤ f i` (W2); over `ℕ` it does not (R4).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `∑ i ∈ s, f i ≤ ∑ i ∈ s, g i` → one term | `gcongr with i hi` | R1 |
| use `h : ∀ i, P i` / `h : ∀ i ∈ s, P i` at `i` | `exact h i` / `have hP := h i hi` | R2 |
| polynomial inequality over `ℝ` from context | `nlinarith` | R3 |
| `∏ i ∈ s, f i ≤ ∏ i ∈ s, g i` → one factor (ℕ) | `gcongr with i hi` | R4 |
| `i ∈ range n` → `i < n` | `Finset.mem_range.mp hi` | R5 |
| common factor or `+ c` around the term | `gcongr` peels it too | W1, W4 |
| product over `ℝ` | prove the side goal `∀ i ∈ s, 0 ≤ f i` first | W2 |
| see the state | infoview | |
