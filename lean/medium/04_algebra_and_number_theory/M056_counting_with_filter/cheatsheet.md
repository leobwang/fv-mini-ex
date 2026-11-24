# M056 · Counting with Finset.filter: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `induction` on `Nat` (E014). **New here:**
Mathlib's finite sets `Finset`, `Finset.range`, `Finset.filter`, the cardinality `#s`, the predicate `Even`,
and `if … then … else` inside a goal.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[DecidableEq α]`
  is a requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℕ` | `Nat`, the natural numbers `0, 1, 2, …` |
| `Finset α` | a finite set of elements of `α` (Mathlib). Membership `a ∈ s`, `a ∉ s` means `¬ (a ∈ s)` |
| `range n` | `Finset.range n`, the finite set `{0, 1, …, n - 1}` (`n` elements; `range 0 = ∅`). It prints without `Finset.` because the file has `open Finset` |
| `insert a s` | the finite set `{a} ∪ s` |
| `filter p s` | `Finset.filter p s`, the elements `x ∈ s` with `p x`; `p : α → Prop`. The spec's `(range (2 * n)).filter Even` is the same term in dot notation (`s.filter p` = `filter p s`); Lean prints it as `filter Even (range (2 * n))` |
| `{m ∈ range n \| q m}` | how Lean prints `filter (fun m => q m) (range n)` when the test is a `fun` (W1). `filter Even s` stays as written |
| `#s` | `Finset.card s`, the number of elements of `s`. You may type `s.card` or `(filter p s).card`; Lean prints `#s` |
| `Even n` | `∃ r, n = r + r` (Mathlib). On `ℕ` it is decidable, so it can be used as a `filter` test |
| `a ∣ b` | `a` divides `b`: `∃ c, b = a * c`. The symbol `∣` is typed `\mid`; it is not the keyboard bar |
| `if c then x else y` | `ite c x y`: the value `x` when `c` holds, `y` otherwise. `c : Prop` needs a `Decidable c` instance |
| `inst✝ : DecidablePred p` | an unnamed instance: `p x` can be decided for every `x`. `filter` needs it to run the test |
| `inst✝ : DecidableEq α` | equality on `α` is decidable. `insert` needs it to check for duplicates; `ℕ` has it |
| `case zero`, `case succ` | the two goals made by `induction` (R1) |

---

## Part 1 · `even_count`

Statement: `#(filter Even (range (2 * n))) = n`: exactly $n$ of the numbers $0, 1, \dots, 2n - 1$ are even.
Plan: induct on `n`. Going from `2 * n` to `2 * (n + 1) = 2 * n + 2` adds the two numbers `2 * n` (even, so
counted) and `2 * n + 1` (odd, so not counted). Expose them as `insert`s (R3, R4), push the filter through
(R5), decide the two parity tests (R6–R9), count the one new element (R10, R13), and use `ih`.

### Splitting `n` into `0` and `k + 1`

**R1 · `induction n with | zero => ?_ | succ k ih => ?_`** changes the **goal list and the context**: one goal
becomes the `zero` goal and the `succ` goal. In the `succ` goal, `n` is gone and the context gains `k : ℕ` and
`ih : P k`. In the exercise write the tactics directly after each `=>`:
`induction n with | zero => tac₀ | succ n ih => tac₁` (reusing the name `n` is fine). Placeholders:
`(P : ℕ → Prop) (n : ℕ)`.

| Before | After |
|---|---|
| `n : ℕ ⊢ P n` | `⊢ P 0`, `k : ℕ, ih : P k ⊢ P (k + 1)` |

**R2 · `simp`** **closes** the `zero` case. `2 * 0 = 0`, `range 0 = ∅`, `filter p ∅ = ∅` and `#∅ = 0` are all
simp lemmas. Placeholders: `(p : ℕ → Prop) [DecidablePred p] (c : ℕ)`.

| Before | After |
|---|---|
| `⊢ #(filter p (range (c * 0))) = 0` | closed |

### Exposing the new elements of the range

**R3 · `rw [show a = b by ring]`** changes the **goal**. `show a = b by ring` is a proof term for `a = b`
built on the spot, and `rw` rewrites with it. Use it to bring the goal into the literal shape a lemma needs:
R4 only matches `range (m + 1)`, and `range (2 * (n + 1))` is not of that form. Placeholders: `(n : ℕ)`,
`(P : ℕ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (3 * (n + 1))` | `⊢ P (3 * n + 2 + 1)` |

**R4 · `rw [Finset.range_add_one]`** changes the **goal**: the range up to `n + 1` becomes the range up to `n`
with the top element `n` inserted. The lemma is `range (n + 1) = insert n (range n)`. Placeholders: `(n : ℕ)`.
Used twice in a row: the first `rw` matches the outer `range (m + 1 + 1)`, the second the `range (m + 1)` it
leaves behind.

| Before | After |
|---|---|
| `⊢ P (range (n + 1))` | `⊢ P (insert n (range n))` |

### Pushing the filter through `insert`

**R5 · `rw [Finset.filter_insert]`** changes the **goal**: the filter of an `insert` becomes an `if` on the
test of the inserted element. The lemma is
`filter p (insert a s) = if p a then insert a (filter p s) else filter p s`. Placeholders:
`{α : Type} [DecidableEq α] (p : α → Prop) [DecidablePred p] (a : α) (s : Finset α)` (for `α = ℕ`,
`p = Even` both brackets are met). After two inserts, use it twice: the first `rw` handles the outer
`insert`; the second rewrites the inner `filter p (insert …)`, which now occurs in both branches of the `if`,
and `rw` rewrites every copy.

| Before | After |
|---|---|
| `⊢ P (filter p (insert a s))` | `⊢ P (if p a then insert a (filter p s) else filter p s)` |

### Deciding the parity tests

**R6 · `have h : Even (2 * a) := even_two_mul a`** changes the **context**. The lemma is
`even_two_mul a : Even (2 * a)`. Placeholders: `{α : Type} [Semiring α] (a : α)` (α has `+`, `*`, `0`, `1`
with the usual laws; `ℕ`, `ℤ`, `ℝ` qualify).

| Before | After |
|---|---|
| `⊢ G` | `h : Even (2 * a) ⊢ G` |

**R7 · `have h : ¬ Even (2 * m + 1) := by simp`** changes the **context**. `simp` proves it with the simp lemma
`Nat.not_even_bit1 : ¬ Even (2 * n + 1)`. Placeholders: `(m : ℕ)`.

| Before | After |
|---|---|
| `⊢ G` | `h : ¬Even (2 * m + 1) ⊢ G` |

**R8 · `simp only [hc, if_true]`** with `hc : c` changes the **goal**: the `if` picks its `then` branch. `hc`
rewrites `c` to `True`, then `if_true : (if True then t else e) = t`. Placeholders:
`{α : Type} (c : Prop) [Decidable c] (x y : α)`.

| Before | After |
|---|---|
| `hc : c ⊢ P (if c then x else y)` | `hc : c ⊢ P x` |

**R9 · `simp only [hc, if_false]`** with `hc : ¬ c` changes the **goal**: the `if` picks its `else` branch.
`hc` rewrites `c` to `False`, then `if_false : (if False then t else e) = e`. Placeholders: as in R8.

| Before | After |
|---|---|
| `hc : ¬c ⊢ P (if c then x else y)` | `hc : ¬c ⊢ P y` |

R8 and R9 combine: `simp only [h1, h2, if_true, if_false]` resolves every `if` whose condition is `h1`'s or
`h2`'s statement, nested ones included.

### Counting the inserted element

**R10 · `rw [Finset.card_insert_of_notMem]`** changes the **goal list**. The lemma is
`a ∉ s → #(insert a s) = #s + 1`, so the goal is rewritten and a side goal `a ∉ s` is added after it. Write
`rw [Finset.card_insert_of_notMem (by simp)]` to close the side goal on the spot (R13). Placeholders:
`{α : Type} [DecidableEq α] (a : α) (s : Finset α)`.

| Before | After |
|---|---|
| `⊢ P #(insert a s)` | `⊢ P (#s + 1)`, `⊢ a ∉ s` |

**R11 · `rw [Finset.mem_filter]`** changes the **goal**: membership in a filter is membership in `s` plus the
test. The lemma is `a ∈ filter p s ↔ a ∈ s ∧ p a`. Placeholders:
`{α : Type} (p : α → Prop) [DecidablePred p] (a : α) (s : Finset α)`.

| Before | After |
|---|---|
| `⊢ a ∉ filter p s` | `⊢ ¬(a ∈ s ∧ p a)` |

**R12 · `rw [Finset.mem_range]`** changes the **goal**: `m ∈ range n` becomes `m < n`. The lemma is
`m ∈ range n ↔ m < n`. Placeholders: `(m n : ℕ) (P : Prop → Prop)`.

| Before | After |
|---|---|
| `⊢ P (m ∈ range n)` | `⊢ P (m < n)` |

**R13 · `simp`** **closes** `a ∉ filter p (range a)`: it applies R11 and R12, then `a < a` is false
(`lt_self_iff_false`). This is the side goal of R10 in the exercise: the new element `2 * n` is not already in
`range (2 * n)`. Placeholders: `(p : ℕ → Prop) [DecidablePred p] (a : ℕ)`.

| Before | After |
|---|---|
| `⊢ a ∉ filter p (range a)` | closed |

After R10 the goal is `#(filter Even (range (2 * n))) + 1 = n + 1`. `rw [ih]` turns it into `n + 1 = n + 1`,
and `rw` closes that by `rfl` itself (TACTIC_STATES, "Rewriting").

### Worked combination (W1, on a count that is not the exercise's)

**W1: multiples of 3**, `#({m ∈ range (3 * n) | 3 ∣ m}) = n`. R1, then `simp` (R2) on `zero`. On `succ`: R3
with `3 * (k + 1) = 3 * k + 1 + 1 + 1`, R4 three times, R5 three times, three facts by `omega` (in place of
R6, R7), R8 and R9 together, R10 with R13, `rw [ih]`. The states before R3, after R3, after the three R4,
after R8/R9, after R10:

```lean-goal
⊢ #({m ∈ range (3 * (k + 1)) | 3 ∣ m}) = k + 1
⊢ #({m ∈ range (3 * k + 1 + 1 + 1) | 3 ∣ m}) = k + 1
⊢ #({m ∈ insert (3 * k + 2) (insert (3 * k + 1) (insert (3 * k) (range (3 * k)))) | 3 ∣ m}) = k + 1
⊢ #(insert (3 * k) ({m ∈ range (3 * k) | 3 ∣ m})) = k + 1
⊢ #({m ∈ range (3 * k) | 3 ∣ m}) + 1 = k + 1
```

Lean prints the top element `3 * k + 1 + 1` as `3 * k + 2`, so the fact about it is stated with `+ 2`.

---

## Traps

- `rw [Finset.range_add_one]` on `range (2 * (n + 1))` fails: the argument must literally be `_ + 1`. Rewrite
  `2 * (n + 1)` to `2 * n + 1 + 1` first (R3).
- After two R5 rewrites the goal is a nested `if`. Do not try to `rw` with `ih` yet: `filter Even (range (2 * n))`
  sits inside the branches. Resolve the `if`s first (R8, R9).
- `simp only [h]` resolves an `if` only when `h`'s statement matches the condition as printed
  (`Even (2 * n)`, `Even (2 * n + 1)`); prove the facts with exactly those expressions.
- `Finset.card_insert_of_notMem` leaves the side goal `2 * n ∉ filter Even (range (2 * n))` after the main
  goal. Close it inline with `(by simp)` (R13), or prove it as the next goal.
- In `ℕ`, `2 * n - 1` is truncated subtraction (`0 - 1 = 0`); the spec avoids it by using `range (2 * n)`,
  which already means "the numbers below `2 * n`".

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| prove `∀ n` one step at a time | `induction n with \| zero => … \| succ n ih => …` | R1 |
| close the `zero` case | `simp` | R2 |
| reshape `2 * (n + 1)` | `rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]` | R3 |
| `range (m + 1) → insert m (range m)` | `rw [Finset.range_add_one]` | R4 |
| `filter p (insert a s) → if p a then … else …` | `rw [Finset.filter_insert]` | R5 |
| `Even (2 * n)` | `even_two_mul n` | R6 |
| `¬ Even (2 * n + 1)` | `by simp` | R7 |
| resolve `if`s with known conditions | `simp only [h1, h2, if_true, if_false]` | R8, R9 |
| `#(insert a s) → #s + 1` | `rw [Finset.card_insert_of_notMem (by simp)]` | R10, R13 |
| unfold `∈ filter` / `∈ range` | `Finset.mem_filter` / `Finset.mem_range` | R11, R12 |
| replace the IH's left side | `rw [ih]` | TACTIC_STATES |
| see the state | infoview | |
