# M023 · Max of a non-empty list: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`exact`, `have`, `rw`, `·`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `List`, `def` by pattern matching, `induction`,
`intro`, `simp`, `omega`, `exact`. M001 (induction with `generalizing`) helps but is not needed.
**New here:** core Lean only (no Mathlib): a recursive function whose *other* argument is an
accumulator; induction `generalizing` that accumulator; `max` on `Int` and `omega`'s support for it;
membership `∈` in a list taken apart with `List.mem_cons` and `rcases … with rfl | rfl | hy`; the core
lemmas `List.mem_singleton`, `List.mem_cons_self`, `List.mem_cons_of_mem`; and `grind` for goals that
mix `∨`, `∈` and arithmetic.

**The objects.**

- **`maxList x xs : Int`** (you write it): the maximum of the non-empty list `x :: xs`. Non-emptiness is
  built into the signature: the list is always `x :: xs`, so there is no "maximum of `[]`" to invent.
  Recursion on `xs`, carrying the maximum so far in the first argument: on `[]` the answer is `x`; on
  `y :: ys` it is `maxList (max x y) ys`.
- **Holes:** the body of `maxList`, and two theorems:
  `maxList_ge`: every `y ∈ x :: xs` satisfies `y ≤ maxList x xs` (an upper bound);
  `maxList_mem`: `maxList x xs ∈ x :: xs` (it occurs in the list).
- In both proofs the recursive call is at a **different** first argument (`max x z`, not `x`), so the
  induction on `xs` must generalize `x` (R3), and the IH is then used at `max x z` (R8).
- The guide teaches on its own functions, **not** the exercise's: `lastOf x xs` (the last element of
  `x :: xs`) and `lenAcc n xs` (`n` plus the length of `xs`), both with the same accumulator shape (R1).

## How to read an entry

Each entry is one tactic, one lemma used with `simp`/`exact`, or one term construct. It says what
changes (**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows
the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
  "no goals" means the goal is closed.
- `P` is "the rest of your goal" (`P : α → Prop`, `P : α → List α → Prop`). The step changes only the
  part inside `P (…)`. `G : Prop` is an arbitrary goal, used when a step acts on a hypothesis.
- Placeholders are written as Lean binders: `{α : Type}` is any element type (`Int`, `Nat`, …);
  `(a b : Int)`, `(l : List α)`, `(f : Int → List Int → Int)`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `x :: xs` | the list with head `x` and tail `xs`; `x :: z :: zs` is `x :: (z :: zs)` |
| `[a]` | the one-element list `a :: []` |
| `y ∈ l` | `y` occurs in the list `l` (a `Prop`) |
| `∀ (y : Int), y ∈ x :: xs → …` | how Lean prints `∀ y ∈ x :: xs, …`: two binders, `y` and the membership proof |
| `max a b` | the larger of `a` and `b` (`if a ≤ b then b else a`) |
| `ih : ∀ (x y : Int), y ∈ x :: zs → y ≤ maxList x zs` | the IH of `maxList_ge` after `generalizing x`: for every accumulator `x` |
| `ih : ∀ (x : Int), maxList x zs ∈ x :: zs` | the IH of `maxList_mem` after `generalizing x` |
| `case cons.inl`, `cons.inr.inl`, `cons.inr.inr` | the three goals after `rcases` in the `cons` case of `y = x ∨ (y = z ∨ y ∈ zs)`: `inl` = left disjunct, `inr` = right; so `y = x`, `y = z`, `y ∈ zs` |

---

## Part 1 · `maxList`

Statement: the body of `def maxList (x : Int) (xs : List Int) : Int`. The theorems pin it down: an
upper bound of `x :: xs` that occurs in `x :: xs` is the maximum.

**R1 · `match xs with | [] => x | y :: ys => f (new x) ys`** is a **term**: recursion on the list with an
accumulator. Lean accepts the recursive call because the list argument `ys` is the tail of `xs`
(structural recursion); the first argument may change freely. Each arm is one equation that
`simp [f]` / `simp only [f]` uses (R6, R7). Placeholders: `{α : Type} (x : α) (xs : List α)`, `(n : Nat)`.

| Before | After |
|---|---|
| `lastOf 1 [2, 3]` | `3` (by `rfl`) |
| `lenAcc 10 [1, 2, 3]` | `13` (by `rfl`) |

**R2 · `max a b`** is a **term**: the larger of `a b : Int`, defined as `if a ≤ b then b else a`. You do
not unfold it: `omega` (R12) and `grind` (R14) know its two facts `a ≤ max a b`, `b ≤ max a b` and
`max a b = a ∨ max a b = b`.

| Before | After |
|---|---|
| `max (3 : Int) (-5)`, `max (-1 : Int) 4` | `3`, `4` (by `decide`) |

## Part 2 · `maxList_ge`

Statement: `∀ y ∈ x :: xs, y ≤ maxList x xs`. Induct on `xs` generalizing `x`. Case `nil`: `y ∈ [x]`
means `y = x`, and `maxList x [] = x`. Case `cons z zs`: unfold one step, so the goal is about
`maxList (max x z) zs`; get `max x z ≤ maxList (max x z) zs` from the IH (the head of
`max x z :: zs` is a member); then split `y ∈ x :: z :: zs` into `y = x`, `y = z`, `y ∈ zs`.

**R3 · `induction xs generalizing x with | nil => ?_ | cons z zs ih => ?_`** changes the **goal list and the
context**. `generalizing x` removes `x` from the context before inducting and re-introduces it in each
case, so the IH is `ih : ∀ (x : α), P x zs` (in the exercise:
`ih : ∀ (x y : Int), y ∈ x :: zs → y ≤ maxList x zs`), usable at the new accumulator `max x z`. In the
exercise, write the tactics directly after each `=>`. Placeholders:
`{α : Type} (P : α → List α → Prop) (x : α) (xs : List α)`.

| Before | After (case `nil`) | After (case `cons`, plus `ih`) |
|---|---|---|
| `x : α, xs : List α ⊢ P x xs` | `x : α ⊢ P x []` | `z : α, zs : List α, x : α ⊢ P x (z :: zs)` |

**R4 · `intro y hy`** changes the **goal and the context**: `∀ y ∈ l, Q y` is `∀ y, y ∈ l → Q y`, two
binders, so it takes two names. Placeholders: `{α : Type} (l : List α) (Q : α → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ (y : α), y ∈ l → Q y` | `y : α, hy : y ∈ l ⊢ Q y` |

**R5 · `simp at hy`** changes the **context**. It uses `List.mem_singleton : a ∈ [b] ↔ a = b`.
Placeholders: `{α : Type} (a y : α) (G : Prop)`.

| Before | After |
|---|---|
| `hy : y ∈ [a] ⊢ G` | `hy : y = a ⊢ G` |

**R6 · `simp [f, hy]`** **closes** the `nil` goal: it unfolds `f` at `[]` (R1's first arm), rewrites with
`hy`, and `a ≤ a` (or `a ∈ [a]`) simplifies to `True`. Placeholders: `(n m : Nat)`, `{α : Type} (a : α)`.
In the exercise: `simp [maxList, hy]` for `maxList_ge`, `simp [maxList]` for `maxList_mem`.

| Before | After |
|---|---|
| `hy : m = n ⊢ m ≤ lenAcc n []` | no goals |
| `⊢ lastOf a [] ∈ [a]` | no goals |

**R7 · `simp only [f]`** changes the **goal**: `f x (z :: zs)` becomes the right side of `f`'s `::` arm.
It fires only where the list argument is literally `[]` or `_ :: _`. In the exercise:
`maxList x (z :: zs)` becomes `maxList (max x z) zs`. Placeholders:
`{α : Type} (x z : α) (zs : List α) (P : α → Prop)`.

| Before | After |
|---|---|
| `⊢ P (lastOf x (z :: zs))` | `⊢ P (lastOf z zs)` |

**R8 · `have h := ih e`** changes the **context**: `ih : ∀ (x : α), Q x` is a function, and `ih e : Q e`.
Give one argument per `∀` and `→`: in `maxList_ge`, `ih (max x z) (max x z) List.mem_cons_self` (the
accumulator, the element `y`, the proof that `y ∈ max x z :: zs`, R9) has type
`max x z ≤ maxList (max x z) zs`. Placeholders: `{α : Type} (Q : α → Prop) (e : α) (G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `h : Q e ⊢ G` |

**R9 · `List.mem_cons_self`** is a **term**: `a ∈ a :: l`, the head is a member. In this Lean version its
arguments `a`, `l` are implicit, so you write just `List.mem_cons_self`. Placeholders:
`{α : Type} (a : α) (l : List α)`.

| Before | After |
|---|---|
| need `a ∈ a :: l` | `List.mem_cons_self` |

**R10 · `simp only [List.mem_cons] at hy`** changes the **context**; the form `at h ⊢` changes the
hypothesis `h` and the **goal**. The lemma is `List.mem_cons : a ∈ b :: l ↔ a = b ∨ a ∈ l`; on `b :: c :: l` it fires twice.
Placeholders: `{α : Type} (a b c : α) (l : List α) (G : Prop)`, `G` an arbitrary goal.

| Before | After |
|---|---|
| `hy : a ∈ b :: c :: l ⊢ G` | `hy : a = b ∨ a = c ∨ a ∈ l ⊢ G` |
| `h : a ∈ b :: l ⊢ a ∈ c :: b :: l` | `h : a = b ∨ a ∈ l ⊢ a = c ∨ a = b ∨ a ∈ l` |

The second row is the `at h ⊢` form (`maxList_mem`): one call rewrites both `h` and the goal.

**R11 · `rcases hy with rfl | rfl | hy`** changes the **goal list and the context**: one goal per
disjunct (`∨` nests to the right, `A ∨ (B ∨ C)`). The pattern `rfl` on `y = a` substitutes: the
variable `a` (the right side) is replaced by `y` everywhere and the equation disappears; `hy` keeps the last disjunct.
Placeholders: `{α : Type} (y a b : α) (l : List α) (P : α → Prop)`, with `ha : P a`, `hb : P b`.

| Before | After |
|---|---|
| `hy : y = a ∨ y = b ∨ y ∈ l ⊢ P y` | `ha : P y ⊢ P y`, `hb : P y ⊢ P y`, `hy : y ∈ l ⊢ P y` |

In the exercise the first branch replaces `x` by `y`: `hmax` becomes `max y z ≤ maxList (max y z) zs`,
which is why `hmax` is made **before** `rcases`.

**R12 · `omega`** **closes** a goal of linear arithmetic over `Int`/`Nat` (`+`, `-`, `*` by a literal,
`≤`, `<`, `=`), `max` and `min` included. Any other term, such as `f (max a b) l` or
`maxList (max y z) zs`, is one unknown number. Placeholders: `(a b : Int) (f : Int → List Int → Int)
(l : List Int)`.

| Before | After |
|---|---|
| `hmax : max a b ≤ f (max a b) l ⊢ a ≤ f (max a b) l` | no goals |

**R13 · `List.mem_cons_of_mem`** is a **term**: `a ∈ l → a ∈ b :: l`, with the new head `b` explicit
(`_` lets Lean infer it). In the third branch: `ih (max x z) y (List.mem_cons_of_mem _ hy)`.
Placeholders: `{α : Type} (a b : α) (l : List α)`.

| Before | After |
|---|---|
| `h : a ∈ l` | `List.mem_cons_of_mem b h : a ∈ b :: l` |

**W1 (on `lenAcc`):** `n ≤ lenAcc n xs` by R3, R6 for `nil`, then R7, R8 at the new counter `n + 1`,
and R12:

| Before | After `simp only [lenAcc]` | After `have h := ih (n + 1)` |
|---|---|---|
| `⊢ n ≤ lenAcc n (z :: zs)` | `⊢ n ≤ lenAcc (n + 1) zs` | `h : n + 1 ≤ lenAcc (n + 1) zs ⊢ n ≤ lenAcc (n + 1) zs` |

---

## Part 3 · `maxList_mem`

Statement: `maxList x xs ∈ x :: xs`. Induct on `xs` generalizing `x` (R3). Case `nil`: R6. Case
`cons z zs`: unfold one step (R7), take the IH at `max x z` (R8): `maxList (max x z) zs ∈ max x z :: zs`;
turn both it and the goal into disjunctions (R10); the result is either `max x z`, which is `x` or `z`,
or a member of `zs`; `grind` does this case analysis (R14).

**R14 · `grind`** **closes** the goal by combining the hypotheses, equalities, `∨` and arithmetic facts it
knows, here `max a b = a ∨ max a b = b`. `omega` fails on this goal: `m ∈ l` is not arithmetic.
Placeholders: `(a b m : Int) (l : List Int)`.

| Before | After |
|---|---|
| `h : m = max a b ∨ m ∈ l ⊢ m = a ∨ m = b ∨ m ∈ l` | no goals |

**W2 (on `lastOf`):** `lastOf x xs ∈ x :: xs` by R3, R6 for `nil`, then R7, R8 at `z`, R10 on `h` and
the goal, and R14:

| Step | State |
|---|---|
| start of `cons` | `⊢ lastOf x (z :: zs) ∈ x :: z :: zs` |
| `simp only [lastOf]` | `⊢ lastOf z zs ∈ x :: z :: zs` |
| `have h := ih z` | `h : lastOf z zs ∈ z :: zs ⊢ lastOf z zs ∈ x :: z :: zs` |
| R10 on `h` and on the goal | `h : lastOf z zs = z ∨ lastOf z zs ∈ zs ⊢ lastOf z zs = x ∨ lastOf z zs = z ∨ lastOf z zs ∈ zs` |
| `grind` | no goals |

---

## Traps

- Without `generalizing x`, the IH is about `maxList x zs` for the **original** `x`, but the unfolded goal
  is about `maxList (max x z) zs`: the IH never applies.
- `∀ y ∈ l, …` needs two names: `intro y hy`. `intro y` alone leaves `y ∈ l → …` as the goal.
- Make `hmax` before `rcases … rfl`: the substitution renames `x` (or `z`) inside it consistently, and
  you need it in the `y = x` and `y = z` branches.
- `omega` treats `y ∈ zs` as nothing it can use; use it only on goals of `≤`, `=`, `max`. For the
  membership disjunction use `grind` (R14).
- `List.mem_cons_self` takes no explicit arguments in this Lean version; `List.mem_cons_self a l` is an
  error.
- `simp only [maxList]` unfolds only where the list argument is a literal `[]` or `_ :: _`: do it after
  `induction`, not before.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| recursion with an accumulator | `match xs with \| [] => x \| y :: ys => f (max x y) ys` | R1, R2 |
| induct, IH for every accumulator | `induction xs generalizing x with \| nil => … \| cons z zs ih => …` | R3 |
| introduce `∀ y ∈ l` | `intro y hy` | R4 |
| `y ∈ [a]` → `y = a` | `simp at hy` | R5 |
| close the `nil` case | `simp [f, hy]` / `simp [f]` | R6 |
| unfold one recursive step | `simp only [f]` | R7 |
| IH at the new accumulator | `have h := ih (max x z) …` | R8 |
| `a ∈ a :: l` | `List.mem_cons_self` | R9 |
| `a ∈ b :: l` → `a = b ∨ a ∈ l` | `simp only [List.mem_cons] at h` (also the goal: see R10) | R10 |
| split the disjunction, substitute | `rcases hy with rfl \| rfl \| hy` | R11 |
| arithmetic with `max` | `omega` | R12 |
| `a ∈ l` → `a ∈ b :: l` | `List.mem_cons_of_mem _ h` | R13 |
| `∨`, `∈` and `max` together | `grind` | R14 |
| see the state | infoview | |
