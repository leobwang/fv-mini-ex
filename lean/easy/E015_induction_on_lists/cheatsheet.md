# E015 · Induction on lists: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics up to E014: `rfl`, `exact`, `simp [f]` (E010), `omega` (E011), definitions by
pattern matching, and `induction n with | zero => … | succ k ih => …` on `Nat` (E014). **New here:** the
type `List α` with its two constructors `[]` and `x :: xs`, induction on a list, and the two jobs `simp`
does in the `cons` case: unfolding a recursive definition one step and peeling off a common head
(`x :: a = x :: b` becomes `a = b`). No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : List α → Prop` or `P : Nat → Prop`). The step changes only the part
  inside `P (…)`, wherever it sits in a larger goal.
- `{α : Type}` is any type of elements (`Nat`, `Bool`, `List Nat`, …).
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `List α` | finite lists with elements of type `α` |
| `[]` | the empty list |
| `x :: xs` | the list with head `x` and tail `xs` |
| `xs ++ ys` | Lean's built-in append on lists (used only in W1; the exercise has its own `app`) |
| `x :: xs ++ ys` | `x :: (xs ++ ys)`: `::` and `++` group to the right (W1) |
| `case nil`, `case cons` | the two goals made by `induction xs` (R1) |
| `ih : P xs` | the induction hypothesis: the goal for the tail |
| `xs : List α` after R1 | a **new** `xs`, the tail; the original `xs` is gone from the context |
| `∀ (x : α) (xs : List α), …` | how Lean prints `∀ x xs, …` with the types filled in |
| `{α : Type}` in a signature | an *implicit* type argument: Lean infers `α` from the list you pass, so you write `len xs`, not `len α xs`; in the context it shows as `α : Type` |
| `\| _ :: xs => …` in a definition | a pattern: matches any cons; `_` is a head that is not named because the body does not use it |
| `\| x :: xs, ys => …` | a pattern for two arguments at once, separated by `,`: first list a cons, second anything (`ys`) |

## Lists and their induction principle

A value of `List α` is either `[]` (nil, the empty list) or `x :: xs` (cons: head `x : α` in front of the
tail `xs : List α`); `[a, b, c]` is notation for `a :: b :: c :: []`. Every list is built from finitely
many conses, so to prove `P xs` for all `xs` it suffices to prove

- `P []`, and
- `P (x :: xs)` for every `x`, `xs`, assuming `ih : P xs` (the induction hypothesis).

This is `Nat` induction with `0 ↦ []` and `k + 1 ↦ x :: xs`, plus a head `x` that comes along. A function
defined by recursion on its **first** list argument (`len`, `app`) computes only when that argument is `[]` or
`_ :: _`, so induct on that argument: then every occurrence of it in the goal becomes `[]` or `x :: xs`.

---

## Part 1 · `app_nil`

Statement: `app xs [] = xs`: appending the empty list changes nothing. `app` recurses on its first argument
(`app [] ys = ys`, `app (x :: xs) ys = x :: app xs ys`), so induct on `xs`. Case `nil`: `app [] []` computes to
`[]`. Case `cons`: `app (x :: xs) []` unfolds to `x :: app xs []`; peel the head `x`; what is left is `ih`.

**R1 · `induction xs with | nil => ?_ | cons x xs ih => ?_`** changes the **goal list and the context**: one
goal becomes the `nil` goal and the `cons` goal. In the `cons` goal the context gains the head `x`, the tail
`xs` and `ih`. In the exercise write the tactics directly after each `=>`, as in E014. Placeholders:
`{α : Type} (P : List α → Prop) (xs : List α)`.

| Before | After |
|---|---|
| `xs : List α ⊢ P xs` | `⊢ P []`, `x : α, xs : List α, ih : P xs ⊢ P (x :: xs)` |

**R2 · `rfl`** **closes** a goal whose two sides compute to the same term. `dbl []` computes to `[]` by the
first equation of `dbl`; in the exercise, `app [] ys` computes to `ys` in the same way.

| Before | After |
|---|---|
| `⊢ dbl [] = []` | no goals |

**R3 · `simp [f]`** changes the **goal**: every `f []` and `f (x :: xs)` is replaced by the right side of `f`'s
matching equation, repeatedly. Here `total [] = 0` and `total (x :: xs) = x + total xs`. Placeholders:
`(x : Nat) (xs : List Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (total (x :: xs))` | `⊢ P (x + total xs)` |

**R4 · `simp` with `List.cons.injEq`** changes the **goal**. The lemma is
`List.cons.injEq : (x :: a = y :: b) = (x = y ∧ a = b)`: conses are equal exactly when heads and tails are.
With equal heads `x = x` simplifies to `True`, so the goal becomes the equation of the tails. `simp` applies it
by itself; you never name it. Placeholders: `{α : Type} (x : α) (a b : List α)`.

| Before | After |
|---|---|
| `⊢ x :: a = x :: b` | `⊢ a = b` |

**R5 · `simp [f, ih]`** changes the **goal**: R3 for each name `f`, plus a rewrite with `ih` from left to
right wherever its left side appears after unfolding. `simp` keeps going until nothing applies (R4 included),
so one call often closes the `cons` case. Placeholders: `(x : Nat) (xs : List Nat) (P : Nat → Prop)`,
`ih : total (dbl xs) = 2 * total xs`.

| Before | After |
|---|---|
| `ih : total (dbl xs) = 2 * total xs ⊢ P (total (dbl (x :: xs)))` | `⊢ P (2 * x + 2 * total xs)` |

**W1 (on `dbl` and `++`):** `dbl (xs ++ ys) = dbl xs ++ dbl ys` by R1, R2 for `nil`, then R3 + R4 in one
`simp [dbl]`, which leaves exactly `ih`:

| Before `simp [dbl]` | After `simp [dbl]` |
|---|---|
| `ih : dbl (xs ++ ys) = dbl xs ++ dbl ys ⊢ dbl (x :: xs ++ ys) = dbl (x :: xs) ++ dbl ys` | `⊢ dbl (xs ++ ys) = dbl xs ++ dbl ys` |

Then `exact ih`, or put `ih` in the `simp` set (R5).

---

## Part 2 · `len_app`

Statement: `len (app xs ys) = len xs + len ys`, where `len [] = 0` and `len (x :: xs) = len xs + 1`. Induct
on `xs`. Case `nil`: the goal computes to `len ys = 0 + len ys`, which `rfl` does not close (R6). Case `cons`:
after unfolding and `ih` both sides are sums of the unknowns `len xs`, `len ys` and `1` in different orders,
which `simp` leaves to `omega` (R7).

**R6 · `simp [f]` where `rfl` fails** **closes** the goal. `0 + n` does not compute to `n` when `n` is unknown,
because `Nat.add` recurses on its **second** argument (`n + 0` does compute to `n`). `simp` knows the lemma
`Nat.zero_add : 0 + n = n`. Placeholders: `(ys : List Nat)`.

| Before | After |
|---|---|
| `⊢ total [] + total ys = total ys` | no goals |

**R7 · `omega`** **closes** a goal of linear arithmetic over `Nat` (`+`, `*` by a literal, `=`, `<`, `≤`).
Any other term, such as `f xs` or `len (app xs ys)`, counts as one unknown number. Placeholders:
`(f : List Nat → Nat) (xs ys : List Nat)`.

| Before | After |
|---|---|
| `⊢ 2 + f xs + f ys = f ys + (f xs + 2)` | no goals |

**W2 (on `total` and `dbl`):** `total (dbl xs) = 2 * total xs` by R1, R6 for `nil`, then R5 and R7. `simp`
leaves an equation of sums:

| Before `simp [dbl, total, ih]` | After |
|---|---|
| `⊢ total (dbl (x :: xs)) = 2 * total (x :: xs)` | `⊢ 2 * x + 2 * total xs = 2 * (x + total xs)` |

and `omega` closes it.

---

## Part 3 · `app_assoc`

Statement: `app (app xs ys) zs = app xs (app ys zs)`. Induct on `xs`, the first argument of the inner `app` on
the left and of the outer `app` on the right. Case `nil`: both sides compute to `app ys zs` (R2). Case `cons`:
`simp [app, ih]` (R5) unfolds twice on the left (`app (x :: xs) ys`, then `app (x :: _) zs`) and once on the
right, peels the common head `x` (R4), and closes the tails with `ih`.

---

## Traps

- Induct on the list the functions recurse on. `induction ys` leaves `app xs (y :: ys)`, which `simp [app]`
  cannot unfold because `xs` is neither `[]` nor `_ :: _`.
- `ih` is about the **tail** `xs`, not the original list: R1 reuses the name `xs` for the tail.
- `rfl` fails on `0 + n = n` for an unknown `n` (R6); use `simp`.
- Give `simp` the names to unfold: plain `simp` does not unfold your own `len` and `app`.
- `simp [len, ih]` may stop at a sum it cannot reorder (`a + b + 1 = a + 1 + b`); finish with `omega`. If
  `simp` already closed the goal, a following `omega` fails with "no goals".

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| prove `P xs` for every list | `induction xs with \| nil => … \| cons x xs ih => …` | R1 |
| `nil` case that computes | `rfl` | R2 |
| unfold `f (x :: xs)` / `f []` | `simp [f]` | R3 |
| `x :: a = x :: b` → `a = b` | `simp` (`List.cons.injEq`) | R4 |
| unfold and use the IH | `simp [f, g, ih]` | R5 |
| `0 + n` left over | `simp [f]` | R6 |
| sums in a different order | `omega` | R7 |
| see the state | infoview | |
