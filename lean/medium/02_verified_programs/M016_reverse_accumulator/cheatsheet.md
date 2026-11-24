# M016 · Reverse with an accumulator: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): pattern-matching `def`, `List`, `::`, `++`, `induction`
on `List`, `rw`, `simp`, `rfl`, `omega`, `have`. **New here:** core Lean only (no Mathlib):
`induction … generalizing` for an argument that changes in the recursive call, rewriting with a
`∀`-hypothesis, the `List` lemmas `reverse_cons`, `append_assoc`, `cons_append`, `nil_append`,
`append_nil`, and the indexing operator `l[i]?` with `List.getElem?_reverse`.

The problem in one paragraph. `revAcc xs acc` walks `xs` and pushes each element onto the front of
`acc`, so it runs in linear time; `rev xs = revAcc xs []`. `rev_eq_reverse` says this equals the
library's `List.reverse`. Induction on `xs` cannot prove `revAcc xs [] = xs.reverse` directly: the
recursive call is `revAcc xs (x :: [])`, whose accumulator is not `[]`, so an IH about `[]` says
nothing about it. You first state and prove a MILESTONE for an arbitrary accumulator,
`revAcc_eq : revAcc xs acc = xs.reverse ++ acc`, by induction generalizing `acc`; then
`rev_eq_reverse` is the case `acc = []`, and `rev_getElem` follows from it and one library lemma.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : List α → Prop`, `P : Option α → Prop`). The step changes only the
  part inside `P (…)`, wherever it sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type; `l l₁ l₂ l₃ xs acc : List α` are
  lists, `a x : α` elements, `i : Nat` an index.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `x :: xs` | the list with head `x` and tail `xs` |
| `l₁ ++ l₂ ++ l₃` | `(l₁ ++ l₂) ++ l₃`: `++` groups to the left |
| `xs.reverse ++ x :: acc`, `a :: as ++ bs` | `::` binds tighter than `++`: `xs.reverse ++ (x :: acc)` and `(a :: as) ++ bs` |
| `revAcc [] acc`, `revAcc (x :: xs) acc` | `revAcc` applied to the list and the accumulator (plain function application, no parentheses) |
| `l.reverse`, `(a :: l).reverse` | `List.reverse l`, the list backwards |
| `[a]` | the one-element list `a :: []` |
| `l[i]?` | entry `i` of `l` (counted from 0) as an `Option α`: `some x`, or `none` when `i ≥ l.length` |
| `l.length - 1 - i` | `Nat` subtraction, cut off at 0 (`2 - 5 = 0`) |
| `∀ (acc : List α), …` in `ih` | the IH holds for every accumulator (after `generalizing acc`) |
| `case nil`, `case cons` | the goals for `[]` and `x :: xs` after `induction` |
| `List.flatMap f l` | apply `f` to each element, concatenate the results (guide only, W2) |

---

## Part 0 · MILESTONE `revAcc_eq` (your own theorem, above `rev_eq_reverse`)

Statement to write yourself, outside any spec region:
`theorem revAcc_eq {α : Type} (xs acc : List α) : revAcc xs acc = xs.reverse ++ acc`.
In words: reversing `xs` onto `acc` is `xs` reversed, followed by `acc`.

**R1 · `induction xs generalizing acc with | nil => … | cons x xs ih => …`** changes the **goal list and
the context**: one goal per constructor of `List`. Without `generalizing`, `acc` stays fixed and the IH is
`P xs acc` for that one `acc`. With it, the cons case gets `ih : ∀ (acc : List α), P xs acc`, usable at
`x :: acc`. Placeholders: `{α : Type} (P : List α → List α → Prop) (xs acc : List α)`.

| Before | After |
|---|---|
| `xs acc : List α ⊢ P xs acc` | `acc : List α ⊢ P [] acc`, `acc : List α ⊢ P (x :: xs) acc` |

In the second goal the context also has `x : α`, `xs : List α` and `ih : ∀ (acc : List α), P xs acc`.

**R2 · `rfl`** **closes** an equation whose two sides compute to the same value. The nil case
`revAcc [] acc = [].reverse ++ acc` is one: both sides compute to `acc`. Placeholders: `(acc : List β)`.

| Before | After |
|---|---|
| `⊢ dupAcc [] acc = [].reverse ++ acc` | no goal |

**R3 · `simp only [f]`** changes the **goal**: it unfolds the clause of `f` that matches the visible
shape of the list argument (`[]` or `_ :: _`). Also unfolds a non-recursive `def`, such as `rev` into
`revAcc xs []`. Placeholders: `(y : β) (ys acc : List β)`, the guide's `dupAcc`.

| Before | After |
|---|---|
| `⊢ P (dupAcc (y :: ys) acc)` | `⊢ P (dupAcc ys (y :: y :: acc))` |

**R4 · `rw [ih]`** with `ih : ∀ acc, f xs acc = g xs ++ acc` changes the **goal**. `rw` chooses the
instance of `∀ acc` itself, here `acc := x :: acc`. The same works with any theorem you proved
earlier, such as your milestone or a previous spec theorem: `rw [thm]`. Placeholders:
`(f : List α → List α → List α) (g : List α → List α) (x : α) (xs acc : List α)`.

| Before | After |
|---|---|
| `⊢ P (f xs (x :: acc))` | `⊢ P (g xs ++ x :: acc)` |

**R5 · `List.reverse_cons`** changes the **goal**. Statement: `(a :: as).reverse = as.reverse ++ [a]`.
Placeholders: `(a : α) (l : List α)`.

| Before | After |
|---|---|
| `⊢ P (a :: l).reverse` | `⊢ P (l.reverse ++ [a])` |

**R6 · `List.append_assoc`** changes the **goal**. Statement: `as ++ bs ++ cs = as ++ (bs ++ cs)`.
Placeholders: `(l₁ l₂ l₃ : List α)`.

| Before | After |
|---|---|
| `⊢ P (l₁ ++ l₂ ++ l₃)` | `⊢ P (l₁ ++ (l₂ ++ l₃))` |

**R7 · `List.cons_append`, then `List.nil_append`** change the **goal**: `[a] ++ l` becomes `a :: l`.
Statements: `a :: as ++ bs = a :: (as ++ bs)` and `[] ++ as = as`. `List.singleton_append :
[x] ++ l = x :: l` does both in one `rw`. Placeholders: `(a : α) (l : List α)`.

| Before | After `rw [List.cons_append]` | After `rw [List.nil_append]` |
|---|---|---|
| `⊢ P ([a] ++ l)` | `⊢ P (a :: ([] ++ l))` | `⊢ P (a :: l)` |

In the milestone's cons case, R3 → R4 → R5 → R6 → R7 turn both sides into `xs.reverse ++ x :: acc`.
`simp [revAcc, ih]` applies all of them at once and closes the goal (W1, W2 show the same call on
other functions).

**W1, W2: the same milestone for other accumulator functions.** `lenAcc xs n = xs.length + n`
(`simp [lenAcc, ih]; omega`) and `dupAcc xs acc = (xs.flatMap fun y => [y, y]).reverse ++ acc`
(`rfl` for nil, `simp [dupAcc, ih]` for cons). The state after `induction … generalizing` is R1's. The
goal before it:

```lean-goal
⊢ dupAcc xs acc = (List.flatMap (fun y => [y, y]) xs).reverse ++ acc
```

---

## Part 1 · `rev_eq_reverse`

Statement: `rev xs = xs.reverse`. Unfold `rev` (R3), rewrite with your milestone at `acc = []` (R4), and
remove the empty accumulator (R8). `simp [rev, revAcc_eq]` does all three.

**R8 · `List.append_nil`** changes the **goal**. Statement: `as ++ [] = as`. Placeholders: `(l : List α)`.

| Before | After |
|---|---|
| `⊢ P (l ++ [])` | `⊢ P l` |

**W3: an accumulator lemma at `acc = []`.** With `hd : ∀ acc, dupAcc xs acc = … ++ acc`, `rw [hd]` (R4)
and `rw [List.append_nil]` (R8):

```lean-goal
⊢ dupAcc xs [] = (List.flatMap (fun y => [y, y]) xs).reverse
⊢ (List.flatMap (fun y => [y, y]) xs).reverse ++ [] = (List.flatMap (fun y => [y, y]) xs).reverse
```

---

## Part 2 · `rev_getElem`

Statement: for `h : i < xs.length`, `(rev xs)[i]? = xs[xs.length - 1 - i]?`: position `i` of the
reversed list holds the element at position `n - 1 - i`, with `n = xs.length`. Rewrite `rev xs` into
`xs.reverse` with the theorem `rev_eq_reverse` you just proved (`rw [rev_eq_reverse]`, as in R4), then
apply R9.

**R9 · `rw [List.getElem?_reverse hi]`** changes the **goal**. Statement:
`i < l.length → l.reverse[i]? = l[l.length - 1 - i]?`. Passing `hi : i < l.length` as the argument
discharges the condition; without it, `rw` adds the side goal `i < l.length`. Placeholders:
`(l : List α) (i : Nat) (hi : i < l.length)`, `P : Option α → Prop`.

| Before | After |
|---|---|
| `hi : i < l.length ⊢ P l.reverse[i]?` | `hi : i < l.length ⊢ P l[l.length - 1 - i]?` |

---

## Traps

- `induction xs` without `generalizing acc`: the cons goal is about `revAcc xs (x :: acc)`, but the IH is
  about `revAcc xs acc`, so `rw [ih]` / `simp [ih]` finds nothing to rewrite.
- Do not try to prove `revAcc xs [] = xs.reverse` by induction directly: it is not the statement the
  recursion preserves. State the milestone for every `acc` (Part 0).
- `List.reverseAux_eq` and `List.reverse_eq_reverseAux` are **banned**: the library's own
  accumulator lemma would solve Part 0 for you. Using them anywhere outside the spec fails the check.
- `rw [List.getElem?_reverse]` without `h` leaves a side goal `i < xs.length`; pass `h` (R9).
- The milestone must come before `rev_eq_reverse` in the file, and `rev_eq_reverse` before
  `rev_getElem`: Lean only sees theorems declared above.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction with a changing accumulator | `induction xs generalizing acc with` | R1 |
| nil case that computes | `rfl` | R2 |
| unfold one clause / a wrapper `def` | `simp only [revAcc]`, `simp only [rev]` | R3 |
| use a `∀`-IH or earlier theorem | `rw [ih]`, `rw [rev_eq_reverse]` | R4 |
| `(a :: as).reverse → as.reverse ++ [a]` | `rw [List.reverse_cons]` | R5 |
| `as ++ bs ++ cs → as ++ (bs ++ cs)` | `rw [List.append_assoc]` | R6 |
| `[a] ++ l → a :: l` | `rw [List.singleton_append]` (simp: `cons_append`, `nil_append`) | R7 |
| whole cons case | `simp [revAcc, ih]` | R3–R7 |
| `l ++ [] → l` | `rw [List.append_nil]` | R8 |
| `l.reverse[i]? → l[l.length - 1 - i]?` | `rw [List.getElem?_reverse h]` | R9 |
| see the state | infoview | |
