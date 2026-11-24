# M030 · Merge sorted lists: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): pattern-matching `def`, `List`, `if … then … else`,
`intro`, `exact`, `apply`, `refine`, `have`, `rw … at h`, `simp`, `omega`, anonymous constructors.
**New here:** core Lean only (no Mathlib): a `match` on two lists at once whose termination Lean finds
by itself; `fun_induction` (induction that follows a function's own recursion); the permutation
relation `List.Perm` and its lemmas; the predicate `List.Pairwise` ("sorted" for `(· ≤ ·)`) and its
lemmas; the membership lemmas `List.mem_append`, `List.mem_cons`; `rcases` with `rfl`.

The problem in one paragraph. You write `merge xs ys`: repeatedly take the smaller of the two heads,
so two sorted lists give one sorted list. Then you prove two facts: `merge xs ys` is a permutation of
`xs ++ ys` (it only rearranges), and it is sorted when `xs` and `ys` are. Both proofs follow
`merge`'s own recursion. The sortedness proof needs the permutation fact, to know which elements
can sit behind the head, so prove `merge_perm` first.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`exact`/`refine`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
  `∅` means the goal is closed.
- `P` (or `Q`) is "the rest of your goal" (`P : List α → Prop`, `P : Prop`). The step changes only the
  part inside `P (…)`. A hypothesis `h`/`hp` in an example is there only to finish it.
- Placeholders are written as Lean binders. `{α : Type}` is any type (`Nat` in the exercise).
  `R : α → α → Prop` is any relation (`(· ≤ ·)` in the exercise).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
- The guide's recursive function is `inter l₁ l₂`, the common elements of two sorted lists: arms
  `[], _` and `_ :: _, []` give `[]`; on `a :: as, b :: bs` it drops `a` if `a < b`, drops `b` if
  `b < a`, and keeps `a` otherwise. Same two-list shape as `merge`, different function.

## Reading the goals

| You see | It means |
|---|---|
| `l₁.Perm l₂` | `List.Perm l₁ l₂`: `l₂` is a rearrangement of `l₁` (same elements, same multiplicities). Written `l₁ ~ l₂` below |
| `x :: xs ++ y :: ys` | `(x :: xs) ++ (y :: ys)`: `::` binds tighter than `++`. It computes to `x :: (xs ++ y :: ys)` (R5) |
| `[] ++ ys` vs `xs ++ []` | the first computes to `ys`, the second does not compute (`++` recurses on its left list) (R3, R4) |
| `xs.Pairwise (· ≤ ·)` | `List.Pairwise (· ≤ ·) xs`: every element is `≤` every later one, i.e. `xs` is sorted |
| `List.Pairwise R l` | `R x y` for every `x` that occurs before `y` in `l` |
| `fun x1 x2 => x1 ≤ x2` | how `(· ≤ ·)` is printed |
| `∀ (a' : Nat), a' ∈ l → x ≤ a'` | what `∀ a' ∈ l, x ≤ a'` is printed as (R10, R12) |
| `ih : P xs → P (y :: ys) → …` | an IH that first needs the hypotheses for the recursive call's arguments (R9) |
| `case case1`, …, `case case4` | goal tags made by `fun_induction`, one per branch of the function, in source order |
| `case inl`, `case inr.inl` | goal tags made by `rcases` on an `∨`: left, right-then-left, … |
| `this : …` | the fact added by `have := …` without a name |

---

## Part 1 · `merge` (a `def` with a hole)

Statement: `def merge (xs ys : List Nat) : List Nat`. Write the body. It should be the usual merge:
if one list is empty return the other; otherwise put the smaller head first and merge the rest.
The two theorems below pin down what "the usual merge" means.

**R1 · `def f (l₁ l₂ : List Nat) : List Nat := match l₁, l₂ with | … => …`** defines a function by
matching both lists at once: one arm per combination of shapes, tried top to bottom (`| [], ys => …`,
`| x :: xs, [] => …`, `| x :: xs, y :: ys => …`). Inside an arm you may call `f` again, and you may
reuse the names `xs ys` for the tails. When each recursive call shrinks one list and keeps the other,
neither argument alone always shrinks; Lean then proves termination itself with the pair of lists
ordered lexicographically (`(l₁, l₂)`: compare the first lists, on a tie the second), and you write
no `termination_by`. Such a definition is compiled by well-founded recursion, so it does **not**
compute inside proofs: `rfl` and `decide` fail on `f [1] [2] = …`. Test it with `simp [f]` (which
applies the defining equations) or `#eval f [1, 4] [2, 3]`. Placeholders: the guide's `inter`.

| Before | After `simp [inter]` |
|---|---|
| `⊢ inter [1, 2, 4] [2, 3, 4] = [2, 4]` | ∅ |

---

## Part 2 · `merge_perm`

Statement: `(merge xs ys).Perm (xs ++ ys)`: `merge` only rearranges its input. Prove it first: Part 3
uses it.

**R2 · `fun_induction f l₁ l₂ with | case1 … => … | …`** changes the **goal list**: one goal per
branch of `f`, i.e. per `match` arm, with each `if` inside an arm giving two branches. In each goal
the call `f l₁ l₂` is already replaced by that branch's right-hand side, and each recursive call
contributes an IH `ih` about that call. An arm names, in order, the arm's pattern variables, the `if`
conditions on the way, then the IHs. For your `merge` with three arms and one `if` there are four
goals, `case1` … `case4`; for `inter`, five. Placeholders: `(l₁ l₂ : List Nat) (P : List Nat → Prop)`.

| Before | After (last of five goals shown) |
|---|---|
| `⊢ P (inter l₁ l₂)` | `hnlt : ¬a < b, hngt : ¬b < a, ih : P (inter as bs) ⊢ P (a :: inter as bs)` |

The first two goals are `l : List Nat ⊢ P []` and `a : Nat, as : List Nat ⊢ P []`: the call is gone,
replaced by the arm's result.

**R3 · `exact .refl _`** **closes** `l.Perm l`. The lemma is `List.Perm.refl l : l.Perm l`; `.refl` is
short for `List.Perm.refl` (Lean takes the namespace from the goal's head `List.Perm`). `exact` checks
up to computation, so it also closes `l.Perm ([] ++ l)`. Placeholders: `{α : Type} (l : List α)`.

| Before | After |
|---|---|
| `⊢ l.Perm ([] ++ l)` | ∅ |

**R4 · `simp`** **closes** `l.Perm (l ++ [])`. `l ++ []` does not compute to `l`, so R3 fails; `simp`
uses `List.append_nil : l ++ [] = l`, then closes `l.Perm l` with `List.Perm.refl`. Placeholders:
`{α : Type} (a : α) (l : List α)`.

| Before | After |
|---|---|
| `⊢ (a :: l).Perm (a :: l ++ [])` | ∅ |

**R5 · `List.Perm.cons`** **closes** a goal with equal heads. The lemma is
`List.Perm.cons a : l₁.Perm l₂ → (a :: l₁).Perm (a :: l₂)`: a common head can be dropped. Dot notation:
`h.cons a` for `h : l₁.Perm l₂`. The right side `a :: as ++ bs` is `(a :: as) ++ bs`, which computes
to `a :: (as ++ bs)` (that equation is `List.cons_append`); `exact` sees through it, so no `rw` is
needed. Placeholders: `{α : Type} (a : α) (l₁ as bs : List α)`.

| Before | After `exact h.cons a` |
|---|---|
| `h : l₁.Perm (as ++ bs) ⊢ (a :: l₁).Perm (a :: as ++ bs)` | ∅ |

**R6 · `List.Perm.trans`** changes the **goal**. The lemma is
`l₁.Perm l₂ → l₂.Perm l₃ → l₁.Perm l₃`. `refine h.trans ?_` takes the first step of a chain from
`h`, and the goal is the remaining step; `h.trans h'` is the whole chain as one term. Placeholders:
`{α : Type} (l₁ l₂ l₃ : List α)`, `h : l₁.Perm l₂`.

| Before | After `refine h.trans ?_` |
|---|---|
| `h : l₁.Perm l₂ ⊢ l₁.Perm l₃` | `⊢ l₂.Perm l₃` |

**R7 · `List.Perm.symm`** changes the **goal**: `l₁.Perm l₂ → l₂.Perm l₁`. As a term: `h.symm`.
Placeholders: `{α : Type} (l₁ l₂ : List α)`.

| Before | After `apply List.Perm.symm` |
|---|---|
| `⊢ l₁.Perm l₂` | `⊢ l₂.Perm l₁` |

**R8 · `List.perm_middle`** **closes** the goal. The lemma is
`(l₁ ++ a :: l₂).Perm (a :: (l₁ ++ l₂))` (all arguments implicit): an element in the middle can move
to the front. `List.perm_middle.symm` (R7) is the reverse direction, `a :: (l₁ ++ l₂)` first. When
`merge` puts `y` first, the target `x :: xs ++ y :: ys` has `y` in the middle, with `l₁ = x :: xs`.
Placeholders: `{α : Type} (a : α) (l₁ l₂ : List α)`.

| Before | After |
|---|---|
| `⊢ (l₁ ++ a :: l₂).Perm (a :: (l₁ ++ l₂))` | ∅ |

**W1 (guide): a chain with R6, R5's lemma, R8.**

```lean-goal
⊢ (l₁ ++ b :: a :: l₂).Perm (b :: a :: (l₁ ++ l₂))
⊢ (b :: (l₁ ++ a :: l₂)).Perm (b :: a :: (l₁ ++ l₂))
⊢ (l₁ ++ a :: l₂).Perm (a :: (l₁ ++ l₂))
```

After `refine List.perm_middle.trans ?_` (R6 with R8 as the first step), then `apply List.Perm.cons`,
then `exact List.perm_middle` (R8). The branch of `merge` that puts `y` first is a two-step chain of
the same kind: `y :: merge … ~ y :: (x :: xs ++ ys) ~ x :: xs ++ y :: ys`.

---

## Part 3 · `merge_sorted`

Statement: `xs.Pairwise (· ≤ ·) → ys.Pairwise (· ≤ ·) → (merge xs ys).Pairwise (· ≤ ·)`. Uses
`merge_perm`.

**R9 · `fun_induction` with hypotheses about the arguments** changes the **goal list and the context**.
A hypothesis such as `hx : xs.Pairwise (· ≤ ·)` mentions the induction variables, so `fun_induction`
carries it into every case, about that case's arguments (`hx : List.Pairwise … (x :: xs)`), and each
IH asks for it about the recursive call's arguments
(`ih : List.Pairwise … xs → List.Pairwise … (y :: ys) → List.Pairwise … (merge xs (y :: ys))`).
You supply those, e.g. `ih hx.of_cons hy` (R11). Do not `revert` anything first. Placeholders:
`(Q P : List Nat → Prop)`, `hq : Q l₁`.

| Before | After (last of five goals shown) |
|---|---|
| `hq : Q l₁ ⊢ P (inter l₁ l₂)` | `ih : Q as → P (inter as bs), hq : Q (a :: as) ⊢ P (a :: inter as bs)` |

**R10 · `List.Pairwise.cons`** changes the **goal list**. The lemma is
`(∀ a' ∈ l, R a a') → List.Pairwise R l → List.Pairwise R (a :: l)`: a list with head `a` is pairwise
when `a` is related to every later element and the tail is pairwise. `refine List.Pairwise.cons ?_ ?_`
leaves both; you can fill the second at once (`refine List.Pairwise.cons ?_ (ih …)`).
Placeholders: `{α : Type} (R : α → α → Prop) (a : α) (l : List α)`.

| Before | After |
|---|---|
| `⊢ List.Pairwise R (a :: l)` | `⊢ ∀ (a' : α), a' ∈ l → R a a'`, `⊢ List.Pairwise R l` |

**R11 · `List.Pairwise.of_cons`** changes the **context**. The lemma is
`List.Pairwise R (a :: l) → List.Pairwise R l`. As a term: `h.of_cons`, typically directly as an
argument (`ih hx.of_cons hy`). Placeholders: as in R10, `h : List.Pairwise R (a :: l)`.

| Before | After `have h' := h.of_cons` |
|---|---|
| `h : List.Pairwise R (a :: l) ⊢ P` | `h' : List.Pairwise R l ⊢ P` |

**R12 · `intro z hz`** changes the **context**: `∀ a' ∈ l, R a a'` is `∀ (a' : α), a' ∈ l → R a a'`,
so it takes two names. Placeholders: as in R10.

| Before | After |
|---|---|
| `⊢ ∀ (a' : α), a' ∈ l → R a a'` | `z : α, hz : z ∈ l ⊢ R a z` |

**R13 · `List.Perm.mem_iff`** changes the **context**. The lemma is
`l₁.Perm l₂ → (a ∈ l₁ ↔ a ∈ l₂)`; `rw` uses the `↔` like an equation. In the exercise,
`(merge_perm _ _).mem_iff` turns `hz : z ∈ merge …` into membership in an append. Placeholders:
`{α : Type} (z : α) (l₁ l₂ : List α)`, `hp : l₁.Perm l₂`.

| Before | After `rw [hp.mem_iff] at hz` |
|---|---|
| `hz : z ∈ l₁ ⊢ P` | `hz : z ∈ l₂ ⊢ P` |

**R14 · `List.mem_append`** changes the **context**: `a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t`. Placeholders:
`{α : Type} (z : α) (s t : List α)`.

| Before | After `rw [List.mem_append] at hz` |
|---|---|
| `hz : z ∈ s ++ t ⊢ P` | `hz : z ∈ s ∨ z ∈ t ⊢ P` |

**R15 · `List.mem_cons`** changes the **context**: `a ∈ b :: l ↔ a = b ∨ a ∈ l`. Placeholders:
`{α : Type} (z b : α) (l : List α)`. R13, R14, R15 go in one `rw [… , … , …] at hz`.

| Before | After `rw [List.mem_cons] at hz` |
|---|---|
| `hz : z ∈ b :: l ⊢ P` | `hz : z = b ∨ z ∈ l ⊢ P` |

**R16 · `rcases hz with hz | rfl | hz`** changes the **goal list and the context**: one goal per side
of the `∨`. The pattern follows the `∨`'s shape: `A ∨ B ∨ C` is `A ∨ (B ∨ C)` and takes `p | q | r`;
`(A ∨ B) ∨ C` takes `(p | q) | r`. The pattern `rfl` on `z = b` substitutes the equation away: one of
the two variables disappears everywhere (here `b` becomes `z`). Placeholders:
`{α : Type} (z b : α) (s t : List α) (P : α → Prop)`.

| Before | After |
|---|---|
| `hz : z ∈ s ∨ z = b ∨ z ∈ t ⊢ P z` | `hz : z ∈ s ⊢ P z`, `h2 : P z ⊢ P z`, `hz : z ∈ t ⊢ P z` |
| `hz : (z = b ∨ z ∈ s) ∨ z ∈ t ⊢ P z` | `h2 : P z ⊢ P z`, `hz : z ∈ s ⊢ P z`, `hz : z ∈ t ⊢ P z` |

Where do the shapes come from? Rewriting `z ∈ xs ++ y :: ys` with R14, R15 gives
`z ∈ xs ∨ z = y ∨ z ∈ ys`; rewriting `z ∈ x :: xs ++ ys` gives `(z = x ∨ z ∈ xs) ∨ z ∈ ys`.

**R17 · `List.rel_of_pairwise_cons`** changes the **context** (or closes a goal `R a z` with `exact`).
The lemma is `List.Pairwise R (a :: l) → a' ∈ l → R a a'`: the head is related to every later element.
Placeholders: `{α : Type} (R : α → α → Prop) (a z : α) (l : List α)`.

| Before | After `have := List.rel_of_pairwise_cons h hz` |
|---|---|
| `h : List.Pairwise R (a :: l), hz : z ∈ l ⊢ P` | `this : R a z ⊢ P` |

**R18 · `Nat.le_trans`** **closes** `n ≤ k` from `n ≤ m` and `m ≤ k`: `Nat.le_trans h₁ h₂`.
Placeholders: `(n m k : Nat)`.

| Before | After `exact Nat.le_trans h₁ h₂` |
|---|---|
| `h₁ : n ≤ m, h₂ : m ≤ k ⊢ n ≤ k` | ∅ |

**R19 · `omega`** **closes** linear arithmetic over `Nat`/`Int` from the hypotheses; negations such as
`¬x ≤ y` count. When `merge` puts `y` first you know only `¬x ≤ y`, and you need `y ≤ x` (and, for
`z` behind `x`, `y ≤ z` from that and `this : x ≤ z`, R17). Placeholders: `(x y : Nat)`.

| Before | After |
|---|---|
| `h : ¬x ≤ y ⊢ y ≤ x` | ∅ |

**W2 (guide): a first lemma, `∀ z ∈ inter l₁ l₂, z ∈ l₁`.** R2 gives five goals; the `a`-kept one is

```lean-goal
⊢ ∀ (z : Nat), z ∈ a :: inter as bs → z ∈ a :: as
```

closed with R12, R15, R16 (`rfl | hz`), then `List.mem_cons_self : a ∈ a :: l` for the head and
`List.mem_cons_of_mem a : z ∈ l → z ∈ a :: l` with `ih` for the tail.

**W3 (guide): sorted in, sorted out, using W2 the way `merge_sorted` uses `merge_perm`.** With
`h : List.Pairwise (· ≤ ·) l₁` in context, R9 gives goals such as

```lean-goal
⊢ List.Pairwise (fun x1 x2 => x1 ≤ x2) (a :: inter as bs)
```

which R10 splits; the tail is `ih h.of_cons` (R11), the head bound is R12, then W2 to get `z ∈ as`,
then R17. The empty cases are `exact .nil` (`List.Pairwise.nil : List.Pairwise R []`).

---

## Traps

- `rfl`, `decide` and `#reduce` do not evaluate `merge`: Lean compiles it by well-founded recursion
  (R1). Check your definition with `example : merge [1, 4] [2, 3] = [1, 2, 3, 4] := by simp [merge]`.
- `fun_induction merge xs ys` produces **four** cases, not three: the `if` in the third arm splits it.
  The arms are `case1 … case4`, in source order, and their names are positional: in
  `| case3 x xs y ys h ih`, `h : x ≤ y` comes before `ih`. Write your `merge` with `x ≤ y` (not
  `y < x`) in the `if` so that the hints read the same.
- In `merge_sorted`, leave `hx` and `hy` in the context when you call `fun_induction`: it generalises
  them itself (R9), so `ih` takes them as arguments.
- `exact` sees through computation (`[] ++ ys` is `ys`, `x :: xs ++ l` is `x :: (xs ++ l)`), but
  `rw` and `simp` match syntax. `xs ++ []` does not compute at all: that case needs `simp` (R4).
- `rcases` patterns must follow how the `∨` is nested (R16); the two recursive cases give different
  nestings after the same `rw`.
- After `rcases … rfl`, a variable may disappear: if `hz : z = y` is substituted, `y` becomes `z`
  everywhere, so `hxy : x ≤ z`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| define by cases on two lists | `match xs, ys with \| [], ys => … \| x :: xs, [] => … \| x :: xs, y :: ys => …` | R1 |
| test a well-founded definition | `example : f [..] [..] = [..] := by simp [f]` | R1 |
| induction following `f`'s recursion | `fun_induction f xs ys with \| case1 … => … \| …` | R2, R9 |
| `l ~ l` (also `l ~ [] ++ l`) | `exact .refl _` | R3 |
| `l ~ l ++ []` | `simp` | R4 |
| drop a common head | `h.cons a` | R5 |
| chain two permutations | `refine h.trans ?_` / `h₁.trans h₂` | R6 |
| swap sides | `h.symm` | R7 |
| move a middle element to the front | `List.perm_middle` (`.symm` for the other way) | R8 |
| split `Pairwise R (a :: l)` | `refine List.Pairwise.cons ?_ ?_` | R10 |
| tail of a pairwise list | `h.of_cons` | R11 |
| `∀ a' ∈ l, …` | `intro z hz` | R12 |
| membership along a permutation | `rw [hp.mem_iff] at hz` | R13 |
| membership in `s ++ t` / `b :: l` | `rw [List.mem_append, List.mem_cons] at hz` | R14, R15 |
| case on `∨`, substitute `z = b` | `rcases hz with hz \| rfl \| hz` | R16 |
| head related to a later element | `List.rel_of_pairwise_cons h hz` | R17 |
| `n ≤ m → m ≤ k → n ≤ k` | `Nat.le_trans h₁ h₂` | R18 |
| arithmetic with `¬x ≤ y` | `omega` | R19 |
| see the state | infoview | |
