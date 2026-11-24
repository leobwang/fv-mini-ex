# E040 · Set extensionality: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `constructor`, `rintro` patterns,
anonymous constructors `⟨_, _⟩`, `Or.inl`/`Or.inr`, `↔`, `omega`, `simp only [...]`.
**New here:** Mathlib's sets `Set α` and their notation (`∈`, `∩`, `∪`, `⊆`, `{x | p x}`, `{a, b, c}`);
the `ext` tactic for sets; five membership lemmas that turn set statements into logic.

## How to read an entry

Each entry is one tactic or one lemma used with `simp only`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P : Prop → Prop` is "the rest of your goal": the step changes only the statement inside `P (…)`, wherever it
  sits. `G : Prop` is an arbitrary goal. A hypothesis `g` in an example only finishes it: it shows what the goal
  or context became.
- Placeholders are written as Lean binders: `{α : Type}` is any type (here: `ℕ`), `(s t u : Set α)` are sets of
  elements of `α`, `(x b : α)` elements, `(p : α → Prop)` a property of elements, `(A B : Prop)` statements.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

**What a set is in Mathlib.** `Set α` is defined as `α → Prop`: a set *is* its membership predicate, and
`x ∈ s` unfolds to `s x`. Every set operation is defined by what its members satisfy, so it unfolds to logic
*by definition* (Lean accepts the unfolded form without a rewrite, R8, R9, R11):

| Set statement | Unfolds to | Lemma that states it |
|---|---|---|
| `x ∈ s ∩ t` | `x ∈ s ∧ x ∈ t` | `Set.mem_inter_iff` (R2) |
| `x ∈ s ∪ t` | `x ∈ s ∨ x ∈ t` | `Set.mem_union` (R7) |
| `s ⊆ t` | `∀ ⦃a⦄, a ∈ s → a ∈ t` | (`Set.subset_def`; `intro` sees through it, R6) |
| `x ∈ {y \| p y}` | `p x` | `Set.mem_setOf_eq` (R12) |
| `x ∈ insert b s` | `x = b ∨ x ∈ s` | `Set.mem_insert_iff` (R13) |
| `x ∈ {b}` | `x = b` | `Set.mem_singleton_iff` (R14) |
| `s = t` | (not by definition) | `Set.ext`, via the tactic `ext x` (R1) |

`⦃a⦄` is a *strict-implicit* binder: `h : s ⊆ t` applied to `hs : x ∈ s` gives `h hs : x ∈ t`, with `x`
filled in from `hs` (R10).

## Reading the goals

| You see | It means |
|---|---|
| `Set ℕ` | sets of natural numbers (= predicates `ℕ → Prop`) |
| `x ∈ s` | `x` is a member of `s` (`\in`) |
| `s ∩ t`, `s ∪ t` | intersection (`\cap`), union (`\cup`) |
| `s ⊆ t` | `s` is a subset of `t` (`\sub`) |
| `{n \| n < 3}` | set-builder: all `n` with `n < 3`; Lean prints the bound variable's type only when it must |
| `{0, 1, 2}` | the finite set `insert 0 (insert 1 {2})` |
| `insert b s` | `{b} ∪ s`, written by Lean when `s` is not a literal list |
| `∀ y ∈ s, y ∈ t` | `∀ y, y ∈ s → y ∈ t` (Lean's printing of a bounded `∀`) |
| `case mp`, `case mpr` | the two directions of an `↔` after `constructor`: `→` and `←` |

---

## Part 1 · `inter_comm_set`

Statement: `A ∩ B = B ∩ A` for sets of naturals. Two sets are equal when they have the same members (R1); then
membership in `∩` is a conjunction (R2), and a conjunction can be swapped in both directions (R3–R5).

**R1 · `ext x`** changes the **goal and the context**. It applies `Set.ext : (∀ x, x ∈ s ↔ x ∈ t) → s = t` and
introduces the element. Placeholders: `{α : Type} (s t : Set α)`.

| Before | After |
|---|---|
| `⊢ s = t` | `x : α ⊢ x ∈ s ↔ x ∈ t` |

**R2 · `simp only [Set.mem_inter_iff]`** changes the **goal**. Lemma:
`Set.mem_inter_iff (a : α) (s t : Set α) : a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t`. `simp only` rewrites every occurrence,
on both sides of the `↔`. Placeholders: `{α : Type} (s t : Set α) (x : α) (P : Prop → Prop)`.

| Before | After |
|---|---|
| `⊢ P (x ∈ s ∩ t)` | `⊢ P (x ∈ s ∧ x ∈ t)` |

**R3 · `constructor`** on an `↔` changes the **goal list**: one goal per direction (`Iff.intro`).
Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B`, `⊢ B → A` |

**R4 · `rintro ⟨ha, hb⟩`** changes the **goal and the context**: it introduces the premise of an implication and
splits the `∧` into its two halves. Placeholders: `(A B G : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ B → G` | `ha : A, hb : B ⊢ G` |

**R5 · `exact ⟨hb, ha⟩`** **closes** a conjunction from its two halves, in the order the goal lists them.
Placeholders: `(A B : Prop) (ha : A) (hb : B)`.

| Before | After |
|---|---|
| `ha : A, hb : B ⊢ B ∧ A` | no goals |

The two directions after R3 have the same shape, so `constructor <;> rintro … <;> exact …` handles both.

**W1.** The same route on `∪`, ending with `Or.comm : a ∨ b ↔ b ∨ a`:

```lean-goal
⊢ s ∪ t = t ∪ s
⊢ x ∈ s ∪ t ↔ x ∈ t ∪ s
⊢ x ∈ s ∨ x ∈ t ↔ x ∈ t ∨ x ∈ s
```

## Part 2 · `subset_union_set`

Statement: `A ⊆ A ∪ B`. A subset goal is a `∀`: take an element of `A` (R6) and show it is in `A ∪ B`, which is
by definition the left side of an `∨` (R8). Since `⊆` unfolds, the whole proof can also be a `fun` term.

**R6 · `intro x hx`** on `s ⊆ t` changes the **goal and the context**. Placeholders: `{α : Type} (s t : Set α)`.

| Before | After |
|---|---|
| `⊢ s ⊆ t` | `x : α, hx : x ∈ s ⊢ x ∈ t` |

**R7 · `simp only [Set.mem_union]`** changes the **goal**. Lemma:
`Set.mem_union (a : α) (s t : Set α) : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t`. Optional: R8 works without it.
Placeholders: `{α : Type} (s t : Set α) (x : α) (P : Prop → Prop)`.

| Before | After |
|---|---|
| `⊢ P (x ∈ s ∪ t)` | `⊢ P (x ∈ s ∨ x ∈ t)` |

**R8 · `exact Or.inl hs` / `exact Or.inr ht`** **closes** `x ∈ s ∪ t` directly, because it is by definition
`x ∈ s ∨ x ∈ t`. Placeholders: `{α : Type} (s t : Set α) (x : α) (ht : x ∈ t)`.

| Before | After |
|---|---|
| `ht : x ∈ t ⊢ x ∈ s ∪ t` | no goals |

**W3** chains R6, R10, R8 on `s ⊆ u ∪ t` from `h : s ⊆ t`; after `intro x hx`:

| Before | After `intro x hx` |
|---|---|
| `h : s ⊆ t ⊢ s ⊆ u ∪ t` | `x : α, hx : x ∈ s ⊢ x ∈ u ∪ t` |

and `exact Or.inr (h hx)` closes it.

## Part 3 · `inter_mono`

Statement: from `h : A ⊆ B`, `A ∩ C ⊆ B ∩ C`. Take `x` with `x ∈ A` and `x ∈ C` (R9), move `x ∈ A` to `x ∈ B`
with `h` (R10), and pair the two memberships (R11).

**R9 · `rintro x ⟨hs, ht⟩`** on `s ∩ t ⊆ u` changes the **goal and the context**: R6 and R4 in one step, since
`x ∈ s ∩ t` is by definition a `∧`. Placeholders: `{α : Type} (s t u : Set α)`.

| Before | After |
|---|---|
| `⊢ s ∩ t ⊆ u` | `x : α, hs : x ∈ s, ht : x ∈ t ⊢ x ∈ u` |

**R10 · `h hs`** with `h : s ⊆ t` and `hs : x ∈ s` is a proof of `x ∈ t`: a subset hypothesis is a function from
membership proofs to membership proofs. The element is the strict-implicit `⦃a⦄`, so write `h hs`, not
`h x hs`. Shown with `have`, it changes the **context**. Placeholders:
`{α : Type} (s t : Set α) (x : α) (h : s ⊆ t) (hs : x ∈ s) (G : Prop)`.

| Before | After `have hx := h hs` |
|---|---|
| `hs : x ∈ s ⊢ G` | `hx : x ∈ t ⊢ G` |

**R11 · `exact ⟨hs, ht⟩`** **closes** `x ∈ s ∩ t`: the anonymous constructor of R5 works because the membership
is by definition `x ∈ s ∧ x ∈ t`. Placeholders: `{α : Type} (s t : Set α) (x : α) (hs : x ∈ s) (ht : x ∈ t)`.

| Before | After |
|---|---|
| `hs : x ∈ s, ht : x ∈ t ⊢ x ∈ s ∩ t` | no goals |

A component of `⟨_, _⟩` may itself be a term such as `h hs` (R10).

**W2** chains R9 and R8: on `s ∩ t ⊆ s ∪ t`, `rintro x ⟨hs, ht⟩` gives

| Before | After |
|---|---|
| `⊢ s ∩ t ⊆ s ∪ t` | `hs : x ∈ s, ht : x ∈ t ⊢ x ∈ s ∪ t` |

and `exact Or.inl hs` closes it.

## Part 4 · `set_builder`

Statement: `{n : ℕ | n < 3} = {0, 1, 2}`. Extensionality (R1), then rewrite both memberships into arithmetic
(R12–R14) and let `omega` decide the resulting statement about one natural number (R15).

**R12 · `simp only [Set.mem_setOf_eq]`** changes the **goal**. Lemma:
`Set.mem_setOf_eq : (a ∈ {x | p x}) = p a`. Placeholders: `{α : Type} (p : α → Prop) (x : α) (P : Prop → Prop)`.

Before, then after (a block, since `|` cannot sit inside a table cell):

```lean-goal
⊢ P (x ∈ {y | p y})
⊢ P (p x)
```

**R13 · `simp only [Set.mem_insert_iff]`** changes the **goal**. Lemma:
`Set.mem_insert_iff : a ∈ insert b s ↔ a = b ∨ a ∈ s`. `{a, b, c}` is `insert a (insert b {c})`, so `simp only`
peels off every listed element but the last. Placeholders: `{α : Type} (s : Set α) (x b : α) (P : Prop → Prop)`.

| Before | After |
|---|---|
| `⊢ P (x ∈ insert b s)` | `⊢ P (x = b ∨ x ∈ s)` |

**R14 · `simp only [Set.mem_singleton_iff]`** changes the **goal**: the last listed element. Lemma:
`Set.mem_singleton_iff : a ∈ {b} ↔ a = b`. Placeholders: `{α : Type} (x b : α) (P : Prop → Prop)`.

| Before | After |
|---|---|
| `⊢ P (x ∈ {b})` | `⊢ P (x = b)` |

**R15 · `omega`** **closes** a goal of linear arithmetic over `ℕ`/`ℤ`, including `↔`, `∨`, `∧`, `¬` of linear
facts. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ n < 2 ↔ n = 0 ∨ n = 1` | no goals |

**W4** is the whole route on `{n : ℕ | n < 2} = {0, 1}`: R1, then one `simp only` with R12–R14, then R15.

```lean-goal
⊢ {n | n < 2} = {0, 1}
⊢ n ∈ {n | n < 2} ↔ n ∈ {0, 1}
⊢ n < 2 ↔ n = 0 ∨ n = 1
```

---

## Traps

- `rw [Set.mem_inter_iff]` fixes the lemma's arguments at the first match (`x ∈ A ∩ B`) and rewrites only
  that instance: the other side `x ∈ B ∩ A` stays a set. `simp only [...]` rewrites every instance. Prefer
  `simp only` here.
- `omega` does not understand `∈`: rewrite every membership away first (R12–R14), or it fails with "omega could
  not prove the goal" even though the arithmetic is trivial.
- `ext x` applies only to equations; on `s ⊆ t` it fails, use `intro x hx` (R6).
- `h x hs` fails for `h : s ⊆ t`: the element is strict-implicit, write `h hs` (R10).
- The library lemmas `Set.inter_comm`, `Set.subset_union_left`, `Set.inter_subset_inter_left` are banned: they
  are the three theorems themselves.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `s = t` for sets → membership `↔` | `ext x` | R1 |
| `x ∈ s ∩ t` → `x ∈ s ∧ x ∈ t` | `simp only [Set.mem_inter_iff]` | R2 |
| split an `↔` | `constructor` | R3 |
| use a `∧` premise | `rintro ⟨ha, hb⟩` | R4 |
| prove `A ∧ B` or `x ∈ s ∩ t` | `exact ⟨ha, hb⟩` | R5, R11 |
| prove `s ⊆ t` | `intro x hx` | R6 |
| `x ∈ s ∪ t` → `x ∈ s ∨ x ∈ t` | `simp only [Set.mem_union]` | R7 |
| prove `x ∈ s ∪ t` | `exact Or.inl hs` / `Or.inr ht` | R8 |
| prove `s ∩ t ⊆ u` | `rintro x ⟨hs, ht⟩` | R9 |
| use `h : s ⊆ t` on `hs : x ∈ s` | `h hs` | R10 |
| `x ∈ {y \| p y}` → `p x` | `simp only [Set.mem_setOf_eq]` | R12 |
| `x ∈ {a, b, c}` → `x = a ∨ x = b ∨ x = c` | `simp only [Set.mem_insert_iff, Set.mem_singleton_iff]` | R13, R14 |
| finish linear `ℕ` logic | `omega` | R15 |
| see the state | infoview | |
