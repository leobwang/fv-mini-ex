# M001 · take and drop: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `List`, `def` by pattern matching, `induction`, `cases`,
`simp`, `rfl`, `omega`. **New here:** induction whose hypothesis is re-quantified over the list
(`generalizing`), functions that recurse on a number and a list at the same time, and the core `Nat`
lemmas for truncated subtraction and `min` that `simp` uses. Core Lean only, no Mathlib.

## The objects

- **`take n xs`**: the first `n` elements of `xs` (all of `xs` if it is shorter).
  **`drop n xs`**: `xs` without its first `n` elements (`[]` if it is shorter). Both are given (spec);
  each line `| pattern => body` of their definitions is one equation `simp [take]` / `simp [drop]` can use.
- **Holes:** four theorems: `take n xs ++ drop n xs = xs`, `(drop n xs).length = xs.length - n`,
  `(take n xs).length = min n xs.length`, `drop m (drop n xs) = drop (n + m) xs`.
- The guide teaches on a toy function `insertAt a n xs` (put `a` at position `n`), which recurses the
  same way. It is **not** one of the exercise's functions.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change. `∅`
  means the goal is closed.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders: `{α : Type}` is any element type; `(n m : Nat)`, `(xs : List α)`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `[]`, `x :: xs` | the empty list; the list with head `x` and tail `xs` |
| `l₁ ++ l₂` | append. `x :: xs ++ ys` means `(x :: xs) ++ ys`: `::` binds tighter |
| `xs.length` | `List.length xs` |
| `a - b` on `Nat` | truncated subtraction: `0` when `b ≥ a`, so `0 - n = 0` |
| `min a b` | the smaller of `a` and `b` |
| `n + 1 + m` | `(n + 1) + m`: `+` groups to the left, so this is **not** of the form `_ + 1` |
| `ih : ∀ (xs : List α), …` | the induction hypothesis, valid for every list (after `generalizing xs`) |
| `n✝`, `a✝`, `head✝`, `tail✝` | inaccessible names made by `induction`/`cases`; name them with `with` |
| `‹_›` (in `guide.lean`) | the hypothesis in context whose type fits; used to refer to an unnamed `a✝` |
| `case succ.cons` | the goal for `n + 1` and a non-empty list |

---

## Part 1 · `take_append_drop`

Statement: `take n xs ++ drop n xs = xs` for every `n` and `xs`. Both functions peel one element off the
number and the list together, so induct on `n` with the list free, then split the list.

**R1 · `induction n generalizing xs`** changes the **goal list and the context**: goals `zero` and `succ`. In
`succ` the hypothesis `a✝ : ∀ (xs : List α), P n✝ xs` holds for every list, because `generalizing xs` removed
`xs` from the context before inducting. That is what lets you apply it to the tail later.
With `induction n generalizing xs with | zero => … | succ n ih => …` the names are `n` and `ih`.
Placeholders: `{α : Type} (P : Nat → List α → Prop) (n : Nat) (xs : List α)`.

| Before | After (case `zero`) | After (case `succ`) |
|---|---|---|
| `n : Nat, xs : List α ⊢ P n xs` | `xs : List α ⊢ P 0 xs` | `n✝ : Nat, xs : List α ⊢ P (n✝ + 1) xs` |

Without `generalizing` (second example of R1), `xs` stays fixed and the hypothesis is `a✝ : P n✝ xs`: only
about the original list, useless for its tail.

| Before `induction n` | After (case `succ`) |
|---|---|
| `n : Nat ⊢ P n xs` | `n✝ : Nat, a✝ : P n✝ xs ⊢ P (n✝ + 1) xs` |

**R2 · `cases xs`** changes the **goal list and the context**: one goal for `[]`, one for `head :: tail`.
With `cases xs with | nil => … | cons x xs => …` the names are `x` and `xs`. Placeholders:
`{α : Type} (P : List α → Prop) (xs : List α)`.

| Before | After (case `nil`) | After (case `cons`) |
|---|---|---|
| `xs : List α ⊢ P xs` | `⊢ P []` | `head✝ : α, tail✝ : List α ⊢ P (head✝ :: tail✝)` |

**R3 · `simp only [f]`** changes the **goal**: it rewrites `f` applied to arguments that literally match one
of its patterns (`0`, `n + 1`, `[]`, `x :: xs`) into that line's body. In the exercise: `simp [take, drop]`.
Placeholders: `{α : Type} (a x : α) (n : Nat) (xs : List α)`.

| Before | After |
|---|---|
| `⊢ P (insertAt a (n + 1) (x :: xs))` | `⊢ P (x :: insertAt a n xs)` |
| `⊢ P (insertAt a 0 xs)` | `⊢ P (a :: xs)` |

R4–R6 are core list lemmas that `simp` applies by itself after R3. Placeholders:
`{α : Type} (a : α) (l as bs : List α)`.

**R4 · `List.nil_append`** changes the **goal**. Statement: `[] ++ l = l` (case `zero`: `take 0 xs` is `[]`).

| Before | After |
|---|---|
| `⊢ P ([] ++ l)` | `⊢ P l` |

**R5 · `List.append_nil`** changes the **goal**. Statement: `l ++ [] = l` (case `succ.nil`).

| Before | After |
|---|---|
| `⊢ P (l ++ [])` | `⊢ P l` |

**R6 · `List.cons_append`** changes the **goal**. Statement: `a :: as ++ bs = a :: (as ++ bs)`: it brings the
head out so the IH can see `take n xs ++ drop n xs` (case `succ.cons`).

| Before | After |
|---|---|
| `⊢ P (a :: as ++ bs)` | `⊢ P (a :: (as ++ bs))` |

**R7 · `simp [ih]`** with `ih : ∀ xs, f xs = g xs` **closes** the goal: `simp` instantiates the `∀` at the list
it finds (the tail `t`), rewrites left to right, and both sides agree. A helper lemma `simp [my_lemma]` works the
same way. Placeholders: `{α : Type} (f g : List α → List α) (x : α) (t : List α)`.

| Before | After |
|---|---|
| `⊢ x :: f t = x :: g t` | `∅` |

In the exercise one call per case does R3–R7: `simp [take, drop]` for `zero` and `succ.nil`,
`simp [take, drop, ih]` for `succ.cons`.

## Part 2 · `length_drop`

Statement: `(drop n xs).length = xs.length - n`. Same structure as Part 1 (R1, R2); `simp [drop]` (R3), plus
the length lemmas R8 and the subtraction lemmas R9–R11, which `simp` applies by itself.

**R8 · `List.length_nil`, `List.length_cons`** change the **goal**. Statements: `[].length = 0` and
`(a :: l).length = l.length + 1`. Placeholders: `{α : Type} (a : α) (l : List α)`.

| Before | After |
|---|---|
| `⊢ P [].length` | `⊢ P 0` |
| `⊢ P (a :: l).length` | `⊢ P (l.length + 1)` |

**R9 · `Nat.sub_zero`** changes the **goal**. Statement: `n - 0 = n` (case `zero`). Placeholders: `(n : Nat)`.

| Before | After |
|---|---|
| `⊢ P (n - 0)` | `⊢ P n` |

**R10 · `Nat.zero_sub`** changes the **goal**. Statement: `0 - n = 0`; `-` on `Nat` never goes below `0`
(case `succ.nil`: `[].length - (n + 1)`). `simp` gets it from `Nat.sub_eq_zero_of_le : n ≤ m → n - m = 0`.
Placeholders: `(n : Nat)`.

| Before | After |
|---|---|
| `⊢ P (0 - n)` | `⊢ P 0` |

**R11 · `Nat.add_sub_add_right`** changes the **goal**. Statement: `n + k - (m + k) = n - m` (case `succ.cons`:
`(x :: xs).length - (n + 1)` becomes `xs.length + 1 - (n + 1)`, then `xs.length - n`, which is the IH's right
side). `simp` does this step with its built-in procedure `Nat.reduceSubDiff`. Placeholders: `(n m : Nat)`.

| Before | After |
|---|---|
| `⊢ P (n + 1 - (m + 1))` | `⊢ P (n - m)` |

## Part 3 · `length_take`

Statement: `(take n xs).length = min n xs.length`. Same structure again; `simp [take]` and `simp [take, ih]`,
with R8 and the `min` lemmas R12–R13.

**R12 · `Nat.zero_min`, `Nat.min_zero`** change the **goal**. Statements: `min 0 a = 0` (case `zero`) and
`min a 0 = 0` (case `succ.nil`). Placeholders: `(a : Nat)`.

| Before | After |
|---|---|
| `⊢ P (min 0 a)` | `⊢ P 0` |
| `⊢ P (min a 0)` | `⊢ P 0` |

**R13 · `Nat.add_min_add_right`** changes the **goal**. Statement: `min (a + c) (b + c) = min a b + c` (case
`succ.cons`: `min (n + 1) (xs.length + 1)` becomes `min n xs.length + 1`). Placeholders: `(a b : Nat)`.

| Before | After |
|---|---|
| `⊢ P (min (a + 1) (b + 1))` | `⊢ P (min a b + 1)` |

**R17 · `omega`** **closes** linear arithmetic over `Nat` and `Int`: `+`, truncated `-`, `min`, `max`,
multiplication by numerals, `=`, `≤`, `<`, using the hypotheses in context. If `simp` leaves an arithmetic goal
in Parts 2–3, `omega` finishes it. Placeholders: `(a b c : Nat) (h : a ≤ b)`.

| Before | After |
|---|---|
| `h : a ≤ b ⊢ min (a + c) (b + c) - c = a` | `∅` |

## Part 4 · `drop_drop`

Statement: `drop m (drop n xs) = drop (n + m) xs`. Induct on `n` generalizing `xs`, split `xs` (R1, R2). Two
cases need more than R3:

- `succ.nil`: the goal is `drop m (drop (n + 1) []) = drop (n + 1 + m) []`. `drop m []` does not unfold for an
  unknown `m`. Prove a **milestone** `drop m [] = []` first, as its own theorem outside the spec regions (R15),
  and give it to `simp` (R7).
- `succ.cons`: the right side is `drop (n + 1 + m) (x :: xs)`, and `n + 1 + m` is not of the form `_ + 1`, so
  `simp [drop]` cannot unfold it. Rewrite the number first (R16), then `simp [drop, ih]`.

**R14 · `Nat.zero_add`** changes the **goal**. Statement: `0 + n = n` (case `zero`: `drop (0 + m) xs`). `n + 0`
reduces by computation, `0 + n` needs the lemma; `simp` applies it by itself. Placeholders: `(n : Nat)`.

| Before | After |
|---|---|
| `⊢ P (0 + n)` | `⊢ P n` |

**R15 · `cases m <;> rfl`** **closes** a fact about an unknown number by splitting it into `0` and `k + 1`, where
the definition reduces, then `rfl` in each case. Placeholders: `{α : Type} (a : α) (m : Nat)`.

| Before | After |
|---|---|
| `⊢ insertAt a m [] = [a]` | `∅` |

**R16 · `rw [show a = b by omega]`** changes the **goal**: `show a = b by omega` is a proof of `a = b` made on
the spot (R17), and `rw` uses it. Here it turns `n + 1 + m` into `n + m + 1`, which matches the pattern
`_ + 1`. Placeholders: `(n m : Nat)`.

| Before | After |
|---|---|
| `⊢ P (n + 1 + m)` | `⊢ P (n + m + 1)` |

**W2** in the guide runs it on `insertAt`: `rw [show n + 1 + m = n + m + 1 by omega]`, then `simp [insertAt]`:

```lean-goal
⊢ insertAt a (n + 1 + m) (x :: xs) = x :: insertAt a (n + m) xs
⊢ insertAt a (n + m + 1) (x :: xs) = x :: insertAt a (n + m) xs
```

Without the `rw`, `simp [insertAt]` fails with `simp made no progress`.

**W1** (`(insertAt a n xs).length = xs.length + 1`) runs the whole pattern of Parts 1–3: R1, R2, then
`simp [insertAt]` or `simp [insertAt, ih]` in each case.

---

## Traps

- Plain `induction n` (no `generalizing xs`) gives `ih` about the original list only. After `cases xs` it reads
  `ih : take n (x :: xs) ++ drop n (x :: xs) = x :: xs`, but the goal needs it for the tail `xs`, so
  `simp [take, drop, ih]` leaves the goal open (R1, second example).
- `take n xs` with an unknown `n` (or an unknown list) does not unfold: every case must have a literal number
  and a literal list before `simp [take]` can act. That is why the `succ` case needs `cases xs`.
- `simp [f]` unfolds only when the arguments literally match a pattern: `drop (n + 1 + m) (x :: xs)` is stuck
  (R16), and so is `drop m []` (R15).
- `-` on `Nat` is truncated: `xs.length - n` is `0` when `n > xs.length`. Do not reason as in `ℤ`; `omega`
  handles it correctly (R17).
- `simp [ih]` alone does not unfold `take`/`drop`; name them (`simp [take, drop, ih]`).
- In `drop_drop`'s `succ.cons`, unfolding before reshaping the number (R16) rewrites the left side but leaves
  `drop (n + m) xs = drop (n + 1 + m) (x :: xs)`, which no further `simp [drop, ih]` can close. Do R16 first.
- In `length_take`'s `zero` case the left side is `[].length` after unfolding: R8 turns it into `0` before R12
  applies.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| IH for every list | `induction n generalizing xs with \| zero => … \| succ n ih => …` | R1 |
| split the list | `cases xs with \| nil => … \| cons x xs => …` | R2 |
| unfold `take`/`drop` on constructors | `simp [take, drop]` | R3 |
| `[] ++ l`, `l ++ []`, `(a :: as) ++ bs` | applied by `simp` | R4–R6 |
| use the IH / a helper lemma | `simp [take, drop, ih]`, `simp [drop, drop_nil]` | R7 |
| `[].length`, `(a :: l).length` | applied by `simp` | R8 |
| `n - 0`, `0 - n`, `n + k - (m + k)` | applied by `simp` | R9–R11 |
| `min 0 a`, `min a 0`, `min (a + c) (b + c)` | applied by `simp` | R12, R13 |
| `0 + n` | applied by `simp` | R14 |
| a fact about `drop m []` for unknown `m` | `theorem … := by cases m <;> rfl` | R15 |
| expose `_ + 1` in `n + 1 + m` | `rw [show n + 1 + m = (n + m) + 1 by omega]` | R16 |
| leftover `Nat` arithmetic with `-`, `min` | `omega` | R17 |
| see the state | infoview | |
