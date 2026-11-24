# E024 · List library facts: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics up to E023: `rw [lemma]` (E009), `omega` (E011), `List α`, `[]`, `x :: xs`, `++`
(E015), `have` (E021), function composition `g ∘ f` (E022), implicit arguments `{…}` (E023). **New here:**
three functions of Lean's core list library, `List.map`, `List.filter`, `List.foldl`, and the library lemmas
about them. You do not prove anything by induction: each fact is already a named lemma, and the work is
finding the lemma and matching its shape to the goal. No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before and
after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Prop` or `P : List β → Prop`). The step changes only the part
  inside `P (…)`, wherever it sits in a larger goal.
- `{α β γ : Type}` are any types of elements (`Nat`, `Bool`, `List Nat`, …).
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## The three list functions

For `f : α → β`, `p : α → Bool` and `l = [x₁, …, xₙ] : List α`:

| Function | Value | Example |
|---|---|---|
| `List.map f l` | `[f x₁, …, f xₙ] : List β` | `[1, 2, 3].map (· * 2) = [2, 4, 6]` |
| `List.filter p l` | the `xᵢ` with `p xᵢ = true`, in order | `[1, 2, 3, 4].filter (· % 2 == 0) = [2, 4]` |
| `List.foldl g b l` (`g : β → α → β`, `b : β`) | `g (… (g (g b x₁) x₂) …) xₙ`: start at `b`, absorb elements left to right | `[1, 2, 3].foldl (· + ·) 0 = 6` (W1) |
| `List.length l` | `n` | |

`p` returns a `Bool` (`true`/`false`), not a `Prop`: `filter` must be able to compute the answer. In the
examples, `(· * 2)` is `fun x => x * 2`, and `x == y` is Boolean equality (a `Bool`, unlike the `Prop` `x = y`).

**Library names** follow the shape of the left side, outermost function first: `List.length_map` is "length
of a map", `List.length_append` "length of an append", `List.filter_map` "filter of a map",
`List.foldl_append` "foldl over an append". `#check List.length_map` prints a statement; `exact?` searches
for a lemma that closes the goal.

## Reading the goals

| You see | It means |
|---|---|
| `List.map f l` | `l.map f`; Lean prints the full name even if you wrote dot notation |
| `List.filter p l` | `l.filter p` |
| `List.foldl f b l` | `l.foldl f b`: fold `f` over `l` starting from `b` |
| `l.length` | the number of elements of `l` (`List.length l`) |
| `List.map f l ++ List.map g l'` | `(List.map f l) ++ (List.map g l')`: application binds tighter than `++` |
| `l₁ ++ l₂ ++ l₃` | `(l₁ ++ l₂) ++ l₃`: `++` groups to the left, so the outermost append is the last one (W4) |
| `p ∘ f` | `Function.comp p f`, the function `fun x => p (f x)` |
| `fun x1 x2 => x1 + x2` | how Lean prints the shorthand `(· + ·)` |

---

## Part 1 · `map_append_length`

Statement: `((xs ++ ys).map f).length = xs.length + ys.length`. Peel the two outer functions off the left side
from the outside in: first the `map` (R1), then the `++` (R2). After the second rewrite both sides are the same
and `rw` closes the goal with `rfl` by itself.

**R1 · `rw [List.length_map]`** changes the **goal**. The lemma is
`List.length_map (f : α → β) : (List.map f as).length = as.length`, with `as` implicit. Placeholders:
`{α β : Type} (f : α → β) (l : List α)`.

| Before | After |
|---|---|
| `⊢ P (List.map f l).length` | `⊢ P l.length` |

**R2 · `rw [List.length_append]`** changes the **goal**. The lemma is
`List.length_append : (as ++ bs).length = as.length + bs.length`, all arguments implicit. Placeholders:
`{α : Type} (l l' : List α)`.

| Before | After |
|---|---|
| `⊢ P (l ++ l').length` | `⊢ P (l.length + l'.length)` |

**W2 (two maps of different functions):** `(l.map f ++ l'.map g).length = l.length + l'.length`. R2 first, since
`++` is outermost; then R1 twice, because `rw` fixes `f` from the first match and rewrites only that map:

| Before | After `rw [List.length_append]` | After `rw [List.length_map]` |
|---|---|---|
| `⊢ (List.map f l ++ List.map g l').length = l.length + l'.length` | `⊢ (List.map f l).length + (List.map g l').length = l.length + l'.length` | `⊢ l.length + (List.map g l').length = l.length + l'.length` |

The third `rw [List.length_map]` makes both sides equal and closes the goal.

---

## Part 2 · `filter_le_append`

Statement: `(xs.filter p).length ≤ (xs ++ ys).length`. Filtering only removes elements, and appending only adds
them. The first fact is a library lemma with explicit arguments: add it to the context (R3). Expand the right
side (R2). The goal is then `a ≤ b + c` with `h : a ≤ b`, which is linear arithmetic (R4).

**R3 · `have h := List.length_filter_le p l`** changes the **context**: it adds `h`. The lemma is
`List.length_filter_le (p : α → Bool) (l : List α) : (List.filter p l).length ≤ l.length`; its arguments are
explicit, so you pass `p` and `l` (here `p xs`). Placeholders: `{α : Type} (p : α → Bool) (l : List α)`.

| Before | After |
|---|---|
| `⊢ G` | `h : (List.filter p l).length ≤ l.length ⊢ G` |

**R4 · `omega`** **closes** a linear `Nat` goal, using `=`/`≤`/`<` hypotheses from the context. Any term that is
not `+`, a literal, or a literal times something (`l.length`, `(List.filter p l).length`) is one unknown number,
and the same term is the same unknown everywhere. Placeholders: `{α : Type} (l l' : List α) (n : Nat)`.

| Before | After |
|---|---|
| `h : n ≤ l.length ⊢ n ≤ l.length + l'.length` | no goals |

**W3 (bound against a map):** `(l.filter p).length ≤ (l.map f).length + 1` by R3, R1, R4:

```lean-goal
⊢ (List.filter p l).length ≤ (List.map f l).length + 1
⊢ (List.filter p l).length ≤ l.length + 1
```

---

## Part 3 · `foldl_split`

Statement: `(xs ++ ys).foldl f a = ys.foldl f (xs.foldl f a)`: folding over `xs ++ ys` is folding over `xs`, then
continuing from that result over `ys`. This is a library lemma whose arguments are all implicit, so its bare name
is already a proof of the goal (R5). In term mode, write the name directly after `:=`; in tactic mode,
`exact` it.

**R5 · `exact List.foldl_append`** **closes** the goal. The lemma is
`List.foldl_append : List.foldl f b (l ++ l') = List.foldl f (List.foldl f b l) l'`, with `f b l l'` all
implicit: Lean unifies the lemma's left and right sides with the goal's and reads them off. Placeholders:
`{α β : Type} (f : β → α → β) (b : β) (l l' : List α)`.

| Before | After |
|---|---|
| `⊢ List.foldl f b (l ++ l') = List.foldl f (List.foldl f b l) l'` | no goals |

**W1 (how `foldl` computes):** `[1, 2, 3].foldl (· + ·) 0` is `((0 + 1) + 2) + 3 = 6`, and with
`fun acc x => 10 * acc + x` it is `((0·10 + 1)·10 + 2)·10 + 3 = 123`. Both close by `rfl`.

**W4 (three lists, `rw` instead of `exact`):** `rw [List.foldl_append]` rewrites the outermost append first:

```lean-goal
⊢ List.foldl f b (l₁ ++ l₂ ++ l₃) = List.foldl f (List.foldl f (List.foldl f b l₁) l₂) l₃
⊢ List.foldl f (List.foldl f b (l₁ ++ l₂)) l₃ = List.foldl f (List.foldl f (List.foldl f b l₁) l₂) l₃
```

and a second `rw [List.foldl_append]` makes the two sides equal.

---

## Part 4 · `filter_after_map`

Statement: `(xs.map f).filter p = (xs.filter (fun x => p (f x))).map f`: mapping then filtering by `p` keeps the
images of exactly those `x` with `p (f x) = true`. The library lemma moves the filter inside the map (R6), but it
writes the predicate as `p ∘ f`; the right side has `fun x => p (f x)`. These are the same function by unfolding
`Function.comp`, so `rfl` closes the rest (R7). `rw` alone does not, because its built-in `rfl` check only tries
cheap (reducible) unfolding.

**R6 · `rw [List.filter_map]`** changes the **goal**. The lemma is
`List.filter_map : List.filter p (List.map f l) = List.map f (List.filter (p ∘ f) l)`, all arguments implicit.
Placeholders: `{α β : Type} (f : α → β) (p : β → Bool) (l : List α)`.

| Before | After |
|---|---|
| `⊢ P (List.filter p (List.map f l))` | `⊢ P (List.map f (List.filter (p ∘ f) l))` |

**R7 · `rfl`** **closes** an equation whose sides differ only by `g ∘ f` versus `fun x => g (f x)`, wherever
that function sits inside a larger term: `Function.comp g f` is defined as `fun x => g (f x)`, and `rfl`
unfolds definitions. Placeholders: `{α β γ δ : Type} (f : α → β) (g : β → γ) (P : (α → γ) → δ)`; here `P` is
"the rest of each side" (after R6 it is `fun q => List.map f (List.filter q l)`). Lean prints `P (fun x => …)`
without the parentheses.

| Before | After |
|---|---|
| `⊢ P (g ∘ f) = P fun x => g (f x)` | no goals |

---

## Traps

- `rw [List.length_map]` rewrites one map, the first one found, with its `f` fixed; a goal with two different
  maps needs it twice (W2).
- `List.length_filter_le` takes `p` and `l` explicitly; `have h := List.length_filter_le` without them fails
  with `don't know how to synthesize implicit argument α` (Lean cannot tell which list type is meant). Write
  `have h := List.length_filter_le p xs`.
- `omega` uses hypotheses in the context but not lemmas: add the library bound with `have` first (R3).
- After `rw [List.filter_map]` the goal still shows `p ∘ f` on one side and `fun x => p (f x)` on the other:
  `rw` did not close it, `rfl` does (R7).
- `foldl` and `foldr` differ: `foldl` starts at the left with the initial value as first argument of `f`. The
  library lemma for `foldr` over `++` has a different shape (`List.foldr_append`).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| length of `List.map f l` | `rw [List.length_map]` | R1 |
| length of `l ++ l'` | `rw [List.length_append]` | R2 |
| `(List.filter p l).length ≤ l.length` as a fact | `have h := List.length_filter_le p l` | R3 |
| linear `Nat` goal from facts in context | `omega` | R4 |
| `foldl` over `l ++ l'` | `exact List.foldl_append` / `rw [List.foldl_append]` | R5 |
| move `filter` inside `map` | `rw [List.filter_map]` | R6 |
| `p ∘ f` vs `fun x => p (f x)` | `rfl` | R7 |
| find a lemma | `#check List.length_map`, `exact?` | |
| see the state | infoview | |
