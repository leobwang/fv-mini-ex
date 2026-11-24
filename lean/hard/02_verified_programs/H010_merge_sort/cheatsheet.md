# H010 · Merge sort: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): pattern-matching `def`, `List`, `intro`, `exact`,
`apply`, `refine`, `have`, `rw … at h`, `simp`, `omega`, `induction`, anonymous constructors, `<;>`.
**New here:** core Lean only (no Mathlib): `fun_induction` (induction that follows a function's own
recursion, also for well-founded recursion with `if h :` and `let`); the permutation relation
`List.Perm` and its lemmas; the predicate `List.Pairwise` (which `Sorted` abbreviates) and its lemmas;
membership lemmas `List.mem_append`, `List.mem_cons`; `rcases` with `rfl`; a tactic `match` that
matches a list together with a hypothesis about its length; `List.take`, `List.drop`.

The problem in one paragraph. `merge xs ys` merges two lists by repeatedly taking the smaller head.
`msort xs` returns `xs` when `xs.length < 2`; otherwise it cuts `xs` at `half = xs.length / 2`
(`List.take half xs` is the first `half` elements, `List.drop half xs` the rest), sorts both parts and
merges them. Since `msort` calls itself on lists that are not sub-terms of `xs`, Lean accepts it only
with `termination_by xs.length` (well-founded recursion: the length strictly drops). You prove that
`msort xs` is a permutation of `xs` and is sorted. Both proofs go through two MILESTONES about
`merge`, each proved by following `merge`'s recursion.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`exact`/`refine`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` (or `Q`) is "the rest of your goal" (`P : List α → Prop`, `P : Prop`). The step changes only the
  part inside `P (…)`. A hypothesis `h`/`hp` in an example is there only to finish it.
- Placeholders are written as Lean binders. `{α : Type}` is any type (`Nat` in the exercise).
  `R : α → α → Prop` is any relation (`(· ≤ ·)` in the exercise).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
  `∅` means the goal is closed.
- The guide's recursive functions are `keepGE a l` (the elements of `l` that are `≥ a`; clauses `[]`
  and `b :: l` with `if a ≤ b`) and `halves l` (cut at `l.length / 2`, recurse on both parts, glue
  them back swapped; well-founded like `msort`).

## Reading the goals

| You see | It means |
|---|---|
| `l₁.Perm l₂` | `List.Perm l₁ l₂`: `l₂` is a rearrangement of `l₁` (same elements, same multiplicities). Written `l₁ ~ l₂` in the skeletons and hints |
| `x :: xs ++ y :: ys` | `(x :: xs) ++ (y :: ys)`: `::` binds tighter than `++`. It computes to `x :: (xs ++ y :: ys)` (R4) |
| `[] ++ ys` vs `xs ++ []` | the first computes to `ys`, the second does not compute (`++` recurses on its left list) (R2, R3) |
| `Sorted l` | the exercise's `abbrev` for `List.Pairwise (· ≤ ·) l`; every `List.Pairwise` lemma applies to it directly |
| `List.Pairwise R l` | `R x y` for every `x` that occurs before `y` in `l` |
| `(· ≤ ·)` | the relation `fun a b => a ≤ b`: each `·` is one argument. Printed `fun x1 x2 => x1 ≤ x2` when it shows unapplied |
| `abbrev Sorted …` | a definition Lean unfolds on its own when it matches terms, so `exact`, `apply` and `refine` treat `Sorted l` and `List.Pairwise (· ≤ ·) l` as the same; `rw` still sees the name `Sorted` |
| `if h : c then a else b` | an `if` that names the proof of `c` (`h : c` in `a`, `h : ¬c` in `b`); `msort` needs it to prove its calls terminate |
| `termination_by xs.length` | the measure that strictly decreases on every recursive call; it lets `msort` recurse on `take`/`drop`, which are not sub-terms of `xs` |
| `∀ (a' : α), a' ∈ l → R a a'` | what `∀ a' ∈ l, R a a'` is printed as (R10, R12) |
| `List.take n l`, `List.drop n l` | the first `n` elements of `l`, and the rest; `xs.take half` prints as `List.take half xs` |
| `half : Nat := xs.length / 2` | a `let` from the definition, kept as a local definition after `fun_induction` (R20) |
| `h : ¬xs.length < 2` | the `else` branch of `if h : xs.length < 2` |
| `ih : Sorted xs → Sorted (y :: ys) → …` | an IH that first needs the hypotheses for the recursive call (R9) |
| `x✝ : [].length < 2` | the length hypothesis, specialised to the arm of a `match`, with no name (R23) |
| `case case1`, …, `case case4` | goal tags made by `fun_induction`, one per branch of the function, in source order |
| `case inl`, `case inr.inl` | goal tags made by `rcases` on an `∨`: left, right-then-left, … |
| `this : …` | the fact added by `have := …` without a name |

---

## Part 1 · `merge_perm` (MILESTONE)

Statement: `(merge xs ys).Perm (xs ++ ys)`. `merge` only rearranges its input. Prove it FIRST: it is
used in Part 2 (to locate an element of `merge xs ys`) and in Part 3.

**R1 · `fun_induction f a l with | case1 … => … | …`** changes the **goal list**: one goal per branch
of `f`, i.e. per clause, with an `if` inside a clause giving two branches. In each goal the call
`f a l` is already replaced by that branch's right-hand side, and each recursive call contributes an
IH `ih`. Each arm names, in order, the clause's pattern variables, the `if` condition, then the IHs.
For `merge` there are four goals: `case1` (`[], ys`), `case2` (`x :: xs, []`), `case3`
(`x ≤ y`), `case4` (`¬x ≤ y`). Placeholders: `(a : Nat) (l : List Nat) (P : List Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (keepGE a l)` | `⊢ P []`, `hab : a ≤ b, ih : P (keepGE a l) ⊢ P (b :: keepGE a l)`, `hab : ¬a ≤ b, ih : P (keepGE a l) ⊢ P (keepGE a l)` |

**R2 · `exact .refl _`** **closes** `l.Perm l`. The lemma is `List.Perm.refl l : l.Perm l`; `.refl` is
short for `List.Perm.refl` (Lean takes the namespace from the goal's head `List.Perm`). `exact` checks
up to computation, so it also closes `l.Perm ([] ++ l)`. Placeholders: `{α : Type} (l : List α)`.

| Before | After |
|---|---|
| `⊢ l.Perm ([] ++ l)` | ∅ |

**R3 · `simp`** **closes** `l.Perm (l ++ [])`. `l ++ []` does not compute to `l`, so R2 fails; `simp`
uses `List.append_nil : l ++ [] = l`, then closes `l.Perm l` with `List.Perm.refl`. Placeholders:
`{α : Type} (a : α) (l : List α)`.

| Before | After |
|---|---|
| `⊢ (a :: l).Perm (a :: l ++ [])` | ∅ |

**R4 · `List.cons_append`** changes the **goal**. The lemma is `a :: as ++ bs = a :: (as ++ bs)`.
Both sides compute to the same list, so `exact` already treats them as equal (that is why
`ih.cons x` closes `case3` without a `rw`); `rw [List.cons_append]` makes it visible. Placeholders:
`{α : Type} (a : α) (as bs : List α)`.

| Before | After |
|---|---|
| `⊢ P (a :: as ++ bs)` | `⊢ P (a :: (as ++ bs))` |

**R5 · `List.Perm.cons`** changes the **goal**. The lemma is `l₁.Perm l₂ → (a :: l₁).Perm (a :: l₂)`:
a common head can be dropped. As a term, `h.cons a` for `h : l₁.Perm l₂` (dot notation: `h.cons` is
`List.Perm.cons a h`). Placeholders: `{α : Type} (a : α) (l₁ l₂ : List α)`.

| Before `apply List.Perm.cons` | After |
|---|---|
| `⊢ (a :: l₁).Perm (a :: l₂)` | `⊢ l₁.Perm l₂` |

**R6 · `List.Perm.trans`** changes the **goal**. The lemma is
`l₁.Perm l₂ → l₂.Perm l₃ → l₁.Perm l₃`. `refine h.trans ?_` takes the first step of a chain from
`h`, and the goal is the remaining step. Placeholders: `{α : Type} (l₁ l₂ l₃ : List α)`,
`h : l₁.Perm l₂`.

| Before | After `refine h.trans ?_` |
|---|---|
| `h : l₁.Perm l₂ ⊢ l₁.Perm l₃` | `⊢ l₂.Perm l₃` |

**R7 · `List.Perm.symm`** changes the **goal**: `l₁.Perm l₂ → l₂.Perm l₁`. As a term: `h.symm`.
Placeholders: `{α : Type} (l₁ l₂ : List α)`.

| Before `apply List.Perm.symm` | After |
|---|---|
| `⊢ l₁.Perm l₂` | `⊢ l₂.Perm l₁` |

**R8 · `List.perm_middle`** **closes** the goal. The lemma is
`(l₁ ++ a :: l₂).Perm (a :: (l₁ ++ l₂))` (all arguments implicit): an element in the middle can move
to the front. `List.perm_middle.symm` is the reverse direction, `a :: (l₁ ++ l₂)` first. In `case4`
of `merge_perm` the right side `x :: xs ++ y :: ys` has `y` in the middle with `l₁ = x :: xs`.
Placeholders: `{α : Type} (a : α) (l₁ l₂ : List α)`.

| Before | After |
|---|---|
| `⊢ (l₁ ++ a :: l₂).Perm (a :: (l₁ ++ l₂))` | ∅ |

**W1 (guide): a chain with R6, R5, R8.**

```lean-goal
⊢ (l₁ ++ b :: a :: l₂).Perm (b :: a :: (l₁ ++ l₂))
⊢ (b :: (l₁ ++ a :: l₂)).Perm (b :: a :: (l₁ ++ l₂))
⊢ (l₁ ++ a :: l₂).Perm (a :: (l₁ ++ l₂))
```

After `refine List.perm_middle.trans ?_` (R6 with R8 as the first step), then `apply List.Perm.cons`
(R5), then `exact List.perm_middle` (R8).

---

## Part 2 · `merge_sorted` (MILESTONE)

Statement: `Sorted xs → Sorted ys → Sorted (merge xs ys)`. Uses `merge_perm`. Used in Part 4.

**R9 · `fun_induction` with hypotheses about the arguments** changes the **goal list and the context**.
A hypothesis such as `hx : Sorted xs` mentions the induction variables, so `fun_induction` carries it
into every case, about that case's arguments (`hx : Sorted (x :: xs)`), and each IH asks for it about
the recursive call's arguments (`ih : Sorted xs → Sorted (y :: ys) → Sorted (merge xs (y :: ys))`).
You supply those, e.g. `ih hx.of_cons hy` (R11). Placeholders: `(Q P : List Nat → Prop)`, `hq : Q l`.

| Before | After (second of three goals shown) |
|---|---|
| `hq : Q l ⊢ P (keepGE a l)` | `hab : a ≤ b, ih : Q l → P (keepGE a l), hq : Q (b :: l) ⊢ P (b :: keepGE a l)` |

**R10 · `List.Pairwise.cons`** changes the **goal list**. The lemma is
`(∀ a' ∈ l, R a a') → List.Pairwise R l → List.Pairwise R (a :: l)`: a list with head `a` is pairwise
when `a` is related to every later element and the tail is pairwise. `refine List.Pairwise.cons ?_ ?_`
leaves both; the solution fills the second at once (`refine List.Pairwise.cons ?_ (ih …)`).
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
`l₁.Perm l₂ → (a ∈ l₁ ↔ a ∈ l₂)`; `rw` uses the `↔` like an equation. In the exercise
`(merge_perm _ _).mem_iff` turns `z ∈ merge xs (y :: ys)` into `z ∈ xs ++ y :: ys`. Placeholders:
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
the two variables disappears everywhere (here `b` becomes `z`; in `merge_sorted` case3, `y` becomes
`z`). Placeholders: `{α : Type} (z b : α) (s t : List α) (P : α → Prop)`.

| Before | After |
|---|---|
| `hz : z ∈ s ∨ z = b ∨ z ∈ t ⊢ P z` | `hz : z ∈ s ⊢ P z`, `h2 : P z ⊢ P z`, `hz : z ∈ t ⊢ P z` |
| `hz : (z = b ∨ z ∈ s) ∨ z ∈ t ⊢ P z` | `h2 : P z ⊢ P z`, `hz : z ∈ s ⊢ P z`, `hz : z ∈ t ⊢ P z` |

Where do the shapes come from? Rewriting `z ∈ xs ++ y :: ys` (case3) gives `z ∈ xs ∨ z = y ∨ z ∈ ys`;
rewriting `z ∈ x :: xs ++ ys` (case4) gives `(z = x ∨ z ∈ xs) ∨ z ∈ ys`.

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
`¬x ≤ y` count. In case4 of `merge_sorted` the head is `y` and you need `y ≤ z` from `¬x ≤ y` (and,
for `z ∈ xs`, from `this : x ≤ z`, R17). Placeholders: `(x y : Nat)`.

| Before | After |
|---|---|
| `h : ¬x ≤ y ⊢ y ≤ x` | ∅ |

**W2 (guide): every element of `keepGE a l` is `≥ a`.** R1 gives three goals:

```lean-goal
⊢ ∀ (z : Nat), z ∈ [] → a ≤ z
⊢ ∀ (z : Nat), z ∈ b :: keepGE a l → a ≤ z
⊢ ∀ (z : Nat), z ∈ keepGE a l → a ≤ z
```

The first is `simp`; the second is R12, R15, then R16 with `rfl | hz` (head: `hab`; tail: `ih`); the
third is `ih` itself.

---

## Part 3 · `msort_perm`

Statement: `(msort xs).Perm xs`. Uses `merge_perm`.

**R20 · `fun_induction` on a well-founded function with `if h :` and `let`** changes the **goal list**.
Two goals: the `then` branch with `h : cond`, and the `else` branch with `h : ¬cond`, the `let`
variable as a local definition (`k : Nat := l.length / 2`), and one IH per recursive call. Name them
in that order: `| case2 xs h half ih1 ih2 =>` for `msort`. The IHs mention `half`, not
`xs.length / 2`; leave it that way, the lemmas you need work with any `half`. Placeholders:
`(l : List Nat) (P : List Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (halves l)` | `h : l.length < 2 ⊢ P l`, `h : ¬l.length < 2, k : Nat := l.length / 2, ih1 : P (halves (List.drop k l)), ih2 : P (halves (List.take k l)) ⊢ P (halves (List.drop k l) ++ halves (List.take k l))` |

**R21 · `List.Perm.append`** changes the **context**. The lemma is
`l₁.Perm l₂ → l₃.Perm l₄ → (l₁ ++ l₃).Perm (l₂ ++ l₄)`: permute both parts. `have := h₁.append h₂`
names the result `this`. Placeholders: `{α : Type} (l₁ l₂ l₃ l₄ : List α)`.

| Before | After `have := h₁.append h₂` |
|---|---|
| `h₁ : l₁.Perm l₂, h₂ : l₃.Perm l₄ ⊢ P` | `this : (l₁ ++ l₃).Perm (l₂ ++ l₄) ⊢ P` |

**R22 · `List.take_append_drop`** changes the **context** (with `at`) or the goal. The lemma is
`List.take n l ++ List.drop n l = l` (cutting and regluing gives the list back), for any `n`.
Placeholders: `{α : Type} (n : Nat) (l l' : List α)`.

| Before | After `rw [List.take_append_drop] at this` |
|---|---|
| `this : l'.Perm (List.take n l ++ List.drop n l) ⊢ l'.Perm l` | `this : l'.Perm l ⊢ l'.Perm l` |

**W3 (guide): `halves l` is a permutation of `l`.** R20, then R2 for the base case; in the recursive
case R21 on `ih1 ih2`, R6 with `this`, R6 again with `List.perm_append_comm : (l₁ ++ l₂).Perm (l₂ ++ l₁)`
(needed because `halves` glues the parts back swapped; `msort` does not), then R22 on the goal:

```lean-goal
⊢ (halves l).Perm l
⊢ (halves (List.drop k l) ++ halves (List.take k l)).Perm l
```

The second line is the recursive goal. After the two `refine … .trans ?_` steps it is
`(List.take k l ++ List.drop k l).Perm l`, and `rw [List.take_append_drop]` closes it by itself:
after rewriting it is `l.Perm l`, and `rw` tries reflexivity.

---

## Part 4 · `msort_sorted`

Statement: `Sorted (msort xs)`. Uses `merge_sorted`. After R20 the recursive case is one `exact` with
the milestone and the two IHs. The base case has `h : xs.length < 2` and goal `Sorted xs`.

**R23 · `match l, h with | [], _ => … | [x], _ => …`** changes the **goal list**: one goal per list
shape you write. Matching `l` together with `h : l.length < 2` lets Lean see that the remaining shape
`a :: b :: r` would make `h` false, so the two arms are complete. In each arm, `_` is `h` specialised
to that shape, shown without a name (`x✝`). In the guide it is written `refine match l, h with … => ?_`
to show both goals; in your proof, use the tactic `match l, h with` with `exact …` after each `=>`.
Placeholders: `(l : List Nat) (h : l.length < 2) (P : List Nat → Prop)`.

| Before | After |
|---|---|
| `h : l.length < 2 ⊢ P l` | `x✝ : [].length < 2 ⊢ P []`, `x : Nat, x✝ : [x].length < 2 ⊢ P [x]` |

**R24 · `List.Pairwise.nil`** **closes** `List.Pairwise R []`: write `exact .nil` (namespace from the
goal, as in R2). `Sorted []` is such a goal. Placeholders: `{α : Type} (R : α → α → Prop)`.

| Before | After |
|---|---|
| `⊢ List.Pairwise R []` | ∅ |

**R25 · `List.pairwise_singleton`** **closes** `List.Pairwise R [a]`. The lemma is
`List.pairwise_singleton R a : List.Pairwise R [a]` (both arguments explicit; `_` lets Lean find `R`).
Placeholders: `{α : Type} (R : α → α → Prop) (a : α)`.

| Before | After |
|---|---|
| `⊢ List.Pairwise R [a]` | ∅ |

---

## Traps

- `fun_induction merge xs ys` produces **four** cases, not three: the `if` in `merge`'s third clause
  splits it. The arms are `case1 … case4`, in source order, and their names are positional: in
  `| case3 x xs y ys h ih`, `h : x ≤ y` comes before `ih`.
- In `merge_sorted`, leave `hx` and `hy` in the context when you call `fun_induction`: it generalises
  them itself (R9), so `ih` takes them as arguments and you never `revert` anything.
- `exact` sees through computation (`[] ++ ys` is `ys`, `x :: xs ++ l` is `x :: (xs ++ l)`), but
  `rw` and `simp` match syntax. `xs ++ []` does not compute at all: that case needs `simp` (R3).
- `rcases` patterns must follow how the `∨` is nested (R16); the two `merge` cases give different
  nestings after the same `rw`.
- After `rcases … rfl`, a variable may disappear: in case3 `y` becomes `z`, so `hxy : x ≤ z`; in case4
  `x` becomes `z`, so `hxy : ¬z ≤ y` and the goal is `y ≤ z`.
- `half` is a `let`: it shows as `half : Nat := xs.length / 2`. `List.take_append_drop` works for any
  `half`, so you never need to unfold it.
- The base case of `msort_sorted` is not closed by `simp` (it knows nothing about `xs`); case on `xs`
  with `h` (R23). A plain `match xs with` without `h` makes you handle `a :: b :: r` too.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction following `f`'s recursion | `fun_induction f a l with \| case1 … => … \| …` | R1, R9, R20 |
| `l ~ l` (also `l ~ [] ++ l`) | `exact .refl _` | R2 |
| `l ~ l ++ []` | `simp` | R3 |
| `a :: as ++ bs` → `a :: (as ++ bs)` | `rw [List.cons_append]` (or nothing: `exact` sees it) | R4 |
| drop a common head | `apply List.Perm.cons` / `h.cons a` | R5 |
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
| combine two permutations of parts | `have := h₁.append h₂` | R21 |
| `take n l ++ drop n l` → `l` | `rw [List.take_append_drop] at this` | R22 |
| list of length < 2 | `match l, h with \| [], _ => … \| [x], _ => …` | R23 |
| `Pairwise R []` / `Pairwise R [a]` | `exact .nil` / `exact List.pairwise_singleton _ a` | R24, R25 |
| see the state | infoview | |
