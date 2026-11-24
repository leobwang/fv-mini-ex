# E082 · Arrays: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `rfl` and `decide` (E001), `rw` (E009),
`simp` (E010), `omega` (E011), `List` with `++`, `Option` (`some`, `none`), plain `if c then t else e`.
The indexing notation `xs[i]`, `xs[i]?` is explained in *Reading the goals*.
**New here:** core Lean's `Array α` (literal `#[..]`, `push`, `size`, `toList`), the lemmas
`Array.size_push`, `Array.toList_push`, `Array.getElem?_push`, `Array.getElem?_eq_getElem`, and `if_neg`.
No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Prop`, `P : List α → Prop`, `P : Option α → Prop`). The step
  changes only the part inside `P (…)`, wherever it sits in a larger goal.
- `{α : Type}` is any type (`Nat` in the exercise). `[Decidable c]` says Lean can compute whether `c` holds,
  which `if` needs; `i = n` on `Nat` is decidable.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

`Array α` is a finite sequence stored contiguously (constant-time indexing; compiled code updates it in
place when it is not shared). Logically it is a wrapper around a list: `xs.toList : List α` is that list,
and `xs.size = xs.toList.length`. `#[a, b, c]` is a literal. `xs.push v` is `xs` with `v` appended
(index `xs.size`); it returns a new value, nothing is mutated in the logic. Indices start at `0`.

| You see | It means |
|---|---|
| `#[a, b, c]` | the array literal with entries `a, b, c` |
| `xs.push v` | `Array.push xs v`: `xs` with `v` appended at index `xs.size` |
| `(a.push x).push x` | two pushes: first `x` at index `a.size`, then `x` at index `a.size + 1` |
| `xs.size` | `Array.size xs`, the number of entries |
| `xs.toList` | the entries of `xs` as a `List α`, in order |
| `l ++ [u, v]` | list append; `[u, v]` is the two-element list |
| `xs[i]` | entry `i` of `xs`; needs a proof of `i < xs.size`, found in the context and hidden in the display |
| `xs[i]?` | `Option α`: `some xs[i]` if `i < xs.size`, else `none`; no proof needed |
| `if i = xs.size then some v else xs[i]?` | a plain (non-dependent) `if`, the form `Array.getElem?_push` produces |
| `¬i = xs.size + 1` | `¬(i = xs.size + 1)`: `¬` is printed without a space and binds looser than `=` |
| `inst✝ : Decidable c` | the unnamed instance argument `[Decidable c]` |

---

## Part 1 · `pushTwice` (a definition)

Statement: `pushTwice (a : Array Nat) (x : Nat) : Array Nat` appends `x` to `a` twice. You write the body:
two `push`es, the second applied to the result of the first.

**R1 · `xs.push v`** appends one entry. On a literal array, `rfl` **closes** the equation by evaluation.
Placeholders: `{α : Type} (a b c : α)`.

| Before | After |
|---|---|
| `⊢ #[a, b].push c = #[a, b, c]` | no goals |

## Part 2 · `lit_size`

Statement: the literal array with entries `1, 2, 3` has size `3`. Lean counts the entries.

**R2 · `rfl` on `xs.size`** **closes** the goal for a literal array. `decide` also works when the entries are
concrete numbers (`#[1, 2, 3]`), but not on the placeholder example, whose entries `a b` are variables. Placeholders:
`{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `⊢ #[a, b].size = 2` | no goals |

## Part 3 · `pushTwice_size`

Statement: `(pushTwice a x).size = a.size + 2`. Unfold `pushTwice` and count: each push adds `1`, and
`a.size + 1 + 1 = a.size + 2` is arithmetic. `simp [pushTwice]` does all of it.

**R3 · `simp [f]`** changes the **goal**: it unfolds the definition `f`, then rewrites with every `@[simp]`
lemma that applies (here R4), and closes the goal if what is left is trivial (`rfl`, simple `Nat`
arithmetic). Placeholders: `pushZero (xs : Array Nat) : Array Nat := xs.push 0`, `(P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (pushZero xs).size` | `⊢ P (xs.size + 1)` |

**R4 · `Array.size_push`** changes the **goal**. The lemma is
`Array.size_push {xs : Array α} (v : α) : (xs.push v).size = xs.size + 1`; it is `@[simp]`, so `simp` uses it
by itself. Placeholders: `{α : Type} (xs : Array α) (v : α)`.

| Before | After |
|---|---|
| `⊢ P (xs.push v).size` | `⊢ P (xs.size + 1)` |

**W1.** `simp [pushZero]` closes `(pushZero xs).size = xs.size + 1` and
`(pushZero xs).toList = xs.toList ++ [0]` in one call each (R3 with R4, R5).

## Part 4 · `pushTwice_toList`

Statement: `(pushTwice a x).toList = a.toList ++ [x, x]`. Each push appends a singleton list to the list
view; then the two singletons merge into `[x, x]`. `simp [pushTwice]` again does all of it.

**R5 · `Array.toList_push`** changes the **goal**. The lemma is
`Array.toList_push {xs : Array α} {x : α} : (xs.push x).toList = xs.toList ++ [x]` (`@[simp]`).
Placeholders: `{α : Type} (xs : Array α) (v : α) (P : List α → Prop)`.

| Before | After |
|---|---|
| `⊢ P (xs.push v).toList` | `⊢ P (xs.toList ++ [v])` |

**R6 · `List.append_assoc`, `List.cons_append`, `List.nil_append`** change the **goal**: after two R5 steps
the list is `l ++ [u] ++ [v]`, which is `(l ++ [u]) ++ [v]` (`++` groups to the left). The lemmas are
`List.append_assoc : as ++ bs ++ cs = as ++ (bs ++ cs)`, `List.cons_append : a :: as ++ bs = a :: (as ++ bs)`,
`List.nil_append : [] ++ as = as`; together they turn `[u] ++ [v]` into `[u, v]`. All are `@[simp]`.
Placeholders: `{α : Type} (l : List α) (u v : α) (P : List α → Prop)`.

| Before | After |
|---|---|
| `⊢ P (l ++ [u] ++ [v])` | `⊢ P (l ++ [u, v])` |

## Part 5 · `pushTwice_old`

Statement: for `h : i < a.size`, `(pushTwice a x)[i]? = some a[i]`: an index that existed before still holds
its old entry. Unfold, then peel the two pushes from the outside in. Each `Array.getElem?_push` produces an
`if i = (current size) then … else …`, and since `i < a.size` the condition is false both times.

**R7 · `unfold f`** changes the **goal**: `f x y` is replaced by `f`'s body with `x, y` substituted.
Unlike `simp [f]` it does nothing else, so `rw` can work on exactly what you see. Placeholders: `pushZero` as
in R3, `(P : Array Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (pushZero xs)` | `⊢ P (xs.push 0)` |

**R8 · `Array.getElem?_push`** changes the **goal**. The lemma is
`Array.getElem?_push {i : Nat} {xs : Array α} {x : α} : (xs.push x)[i]? = if i = xs.size then some x else xs[i]?`.
`rw` rewrites the outermost `push` first (it matches the first occurrence of the pattern), so on two pushes
the condition is `i = (a.push x).size`. Placeholders:
`{α : Type} (xs : Array α) (v : α) (i : Nat) (P : Option α → Prop)`.

| Before | After |
|---|---|
| `⊢ P (xs.push v)[i]?` | `⊢ P (if i = xs.size then some v else xs[i]?)` |

**R9 · `if_neg`** changes the **goal**: the `if` becomes its `else` branch. The lemma is
`if_neg {c : Prop} [Decidable c] (hnc : ¬c) : (if c then t else e) = e`. Placeholders:
`{α : Type} (c : Prop) [Decidable c] (t e : α) (hnc : ¬c) (P : α → Prop)`. Its mirror `if_pos (hc : c)`
takes the `then` branch (W3).

| Before | After |
|---|---|
| `⊢ P (if c then t else e)` | `⊢ P e` |

**R10 · `simp` then `omega`** **closes** the condition of the outer `if`. `omega` treats `(xs.push v).size`
as an unknown number, so it cannot use `h` directly; `simp` first rewrites the size with R4. For the inner
`if` the condition is `¬i = a.size`, and `omega` alone suffices. Write both in place as `rw` arguments:
`if_neg (by simp; omega)` and `if_neg (by omega)`. Placeholders:
`{α : Type} (xs : Array α) (v : α) (i : Nat) (h : i < xs.size)`.

| Before | After `simp` | After `omega` |
|---|---|---|
| `h : i < xs.size ⊢ ¬i = (xs.push v).size` | `h : i < xs.size ⊢ ¬i = xs.size + 1` | no goals |

**R11 · `Array.getElem?_eq_getElem`** changes the **goal**, or closes it with `exact`. The lemma is
`Array.getElem?_eq_getElem {xs : Array α} {i : Nat} (h : i < xs.size) : xs[i]? = some xs[i]`. After both
pushes are peeled, the goal is exactly `xs[i]? = some xs[i]` with `xs := a`, so `exact … h` finishes.
Placeholders: `{α : Type} (xs : Array α) (i : Nat) (hi : i < xs.size) (P : Option α → Prop)`.

| Before | After |
|---|---|
| `⊢ P xs[i]?` | `⊢ P (some xs[i])` |

**W2: one push, R7 → R8 → R9 → R11.** With `h : i < xs.size`, `unfold pushZero`, `rw [Array.getElem?_push]`,
`rw [if_neg (by omega)]`, `exact Array.getElem?_eq_getElem h`:

```lean-goal
⊢ (pushZero xs)[i]? = some xs[i]
⊢ (xs.push 0)[i]? = some xs[i]
⊢ (if i = xs.size then some 0 else xs[i]?) = some xs[i]
⊢ xs[i]? = some xs[i]
```

With two pushes the same chain runs twice; only the first `if_neg` needs `(by simp; omega)` (R10).

**W3: the new index.** `rw [Array.getElem?_push]` on `(xs.push v)[xs.size]?` gives a true condition; `rw [if_pos rfl]`
then closes the goal:

```lean-goal
⊢ (xs.push v)[xs.size]? = some v
⊢ (if xs.size = xs.size then some v else xs[xs.size]?) = some v
```

---

## Traps

- `if_neg (by omega)` on the **outer** `if` fails: its condition is `¬i = (a.push x).size`, and `omega` sees
  `(a.push x).size` as an opaque number. Use `(by simp; omega)` there (R10).
- `rw [Array.getElem?_push]` rewrites one `push` at a time, outermost first. After the first `if_neg` the goal
  still has `(a.push x)[i]?`: rewrite again.
- `simp [pushTwice]` on the old-index goal only unfolds: `Array.getElem?_push` is not a `@[simp]` lemma, so
  `simp` stops at `((a.push x).push x)[i]? = some a[i]`. Name the lemma with `rw` (R8).
- `simp` without the name (`simp` instead of `simp [pushTwice]`) cannot see through `pushTwice` and makes no
  progress.
- `if_neg` is for a plain `if c then …` (`ite`); `dif_neg` is for a dependent `if h : c then …` (`dite`).
  `Array.getElem?_push` produces a plain `if`.
- `xs[i]` (no `?`) only type-checks with a bound proof in scope: in the statement it is `h : i < a.size`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| append one entry | `xs.push v` | R1 |
| size of a literal array | `rfl` (`decide` if entries are numerals) | R2 |
| unfold `f` and simplify | `simp [f]` | R3 |
| `(xs.push v).size` → `xs.size + 1` | `Array.size_push` (simp lemma) | R4 |
| `(xs.push v).toList` → `xs.toList ++ [v]` | `Array.toList_push` (simp lemma) | R5 |
| `l ++ [u] ++ [v]` → `l ++ [u, v]` | `simp` (`List.append_assoc`, `List.cons_append`, `List.nil_append`) | R6 |
| expose a definition's body only | `unfold f` | R7 |
| `(xs.push v)[i]?` → an `if` | `rw [Array.getElem?_push]` | R8 |
| take the `else` / `then` branch | `rw [if_neg hnc]` / `rw [if_pos hc]` | R9, W3 |
| `¬i = (xs.push v).size` from `i < xs.size` | `(by simp; omega)` | R10 |
| `xs[i]?` → `some xs[i]` | `exact Array.getElem?_eq_getElem h` | R11 |
| see the state | infoview | |
