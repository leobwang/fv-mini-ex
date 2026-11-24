# M070 · Image and preimage: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `∧`, `∨`, `↔`, `∃`, anonymous constructors `⟨…⟩`, and
`rintro`/`obtain` patterns. **New here:** Mathlib's sets `Set α`, union, intersection, subset, image
`f '' s` and preimage `f ⁻¹' t`, and the fact that membership in each of them is a definition you can see
through.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : β → Prop` or `P : Prop`). The step changes only the part inside
  `P (…)`, wherever it sits in a larger goal.
- Placeholders are written as Lean binders. `{α β : Type}` are any types; `f : α → β` is any function.
  No type-class brackets occur in this problem.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Set α` | a set of elements of type `α`. In Mathlib a set *is* a predicate `α → Prop`, and `x ∈ s` is `s x` |
| `s ∪ t`, `s ∩ t` | union and intersection; `x ∈ s ∪ t` is by definition `x ∈ s ∨ x ∈ t`, `x ∈ s ∩ t` is `x ∈ s ∧ x ∈ t` |
| `s ⊆ t` | subset: by definition `∀ x, x ∈ s → x ∈ t`, so you prove it with `intro` |
| `f '' s` | `Set.image f s = {f x \| x ∈ s}`, typed as two apostrophes `''` (not `"`). `y ∈ f '' s` is by definition `∃ x, x ∈ s ∧ f x = y` |
| `f ⁻¹' t` | `Set.preimage f t = {x \| f x ∈ t}`, typed `\inv'`. `x ∈ f ⁻¹' t` is by definition `f x ∈ t` |
| `f '' f ⁻¹' B`, `f ⁻¹' f '' A` | `f '' (f ⁻¹' B)` and `f ⁻¹' (f '' A)`: the infoview drops these parentheses (both operators group to the right), and typing either form gives the same set |
| `sᶜ` | the complement of `s` (W4): `x ∈ sᶜ` is by definition `x ∉ s`, i.e. `¬ x ∈ s` |
| `∃ x ∈ s, Q x` | `∃ x, x ∈ s ∧ Q x` (a binder with a membership condition) |
| `∀ x ∈ s, Q x` | `∀ x, x ∈ s → Q x` |
| `s ∩ u ∪ t ∩ u` | `(s ∩ u) ∪ (t ∩ u)`: `∩` binds tighter than `∪`; `f '' A ∪ f '' B` is `(f '' A) ∪ (f '' B)` |
| `case mp`, `case mpr` | the `→` and `←` directions of an `↔` after `constructor` |
| `case inl`, `case inr` | the left and right sides of an `∨` after a `\|` pattern; tags stack, so inside `mp` you see `case mp.inl`, `case mp.inr` |

Every membership rule above holds **by definition** (`Iff.rfl` in Mathlib). So `exact`, `rintro` patterns
and `⟨…⟩` see through them, and `rw [Set.mem_…]` is only needed when you want to *see* the unfolded form.

---

## Part 1 · `image_union_eq`

Statement: `f '' (A ∪ B) = f '' A ∪ f '' B`: the image of a union is the union of the images. A set equation,
so: reduce to membership (R1), split the `↔` (R2), and in each direction unpack the hypothesis (R5, R6) and
build the goal (R7, R8).

**R1 · `ext x`** changes the **goal and the context**. It applies `Set.ext : (∀ x, x ∈ a ↔ x ∈ b) → a = b`:
two sets are equal when they have the same members. Placeholders: `{α : Type} (s t : Set α)`.

| Before | After |
|---|---|
| `⊢ s = t` | `x : α ⊢ x ∈ s ↔ x ∈ t` |

**R2 · `constructor`** on an `↔` changes the **goal list**: one goal per direction (E005). Placeholders:
`(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B`, `⊢ B → A` |

**R3 · `Set.mem_image`** changes the **goal**. The lemma is `y ∈ f '' s ↔ ∃ x ∈ s, f x = y`: `y` is in the
image when some `x ∈ s` is sent to it. Placeholders: `{α β : Type} (f : α → β) (s : Set α) (b : β)`.
It holds by definition, so you can skip the `rw` and go straight to R5 or R8.

| Before | After `rw [Set.mem_image]` |
|---|---|
| `⊢ b ∈ f '' s` | `⊢ ∃ x ∈ s, f x = b` |

**R4 · `Set.mem_union`** changes the **goal**. The lemma is `x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b`, also by
definition. Placeholders: `{α : Type} (s t : Set α) (a : α)`.

| Before | After `rw [Set.mem_union]` |
|---|---|
| `⊢ a ∈ s ∪ t` | `⊢ a ∈ s ∨ a ∈ t` |

**R5 · `rintro ⟨x, hx, rfl⟩`** changes the **context**. On a goal `y ∈ f '' s → …` it introduces the
membership and splits it as R3's `∃ x, x ∈ s ∧ f x = y`: a point `x`, a proof `hx : x ∈ s`, and the
equation `f x = y`. The pattern `rfl` consumes that equation by **substituting** `f x` for the variable `y`
everywhere, so `y` disappears. Placeholders: `{α β : Type} (f : α → β) (s : Set α) (P : β → Prop) (y : β)`.

| Before | After |
|---|---|
| `y : β ⊢ y ∈ f '' s → P y` | `x : α, hx : x ∈ s ⊢ P (f x)` |

**R6 · `rintro (ha | hb)`** changes the **goal list**. On `a ∈ s ∪ t → …` it splits the `∨` of R4: one goal
assumes `a ∈ s`, the other `a ∈ t`. Patterns nest: inside an image it is `⟨x, hx | hx, rfl⟩` (one goal per
side, each with its own `x` and `hx`), and a union of two images is `(⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)`.
Placeholders: `{α : Type} (s t : Set α) (a : α) (P : Prop)`.

| Before | After |
|---|---|
| `⊢ a ∈ s ∪ t → P` | `ha : a ∈ s ⊢ P`, `hb : a ∈ t ⊢ P` |

**R7 · `refine Or.inl ?_`, `refine Or.inr ?_`** change the **goal**: to prove a union membership, pick a side.
`Or.inl : a → a ∨ b`, `Or.inr : b → a ∨ b`; they work on `a ∈ s ∪ t` directly because it *is* an `∨`. Write
`exact Or.inl proof` to do it in one step. Placeholders: `{α : Type} (s t : Set α) (a : α)`.

| Before | After `refine Or.inl ?_` | After `refine Or.inr ?_` |
|---|---|---|
| `⊢ a ∈ s ∪ t` | `⊢ a ∈ s` | `⊢ a ∈ t` |

**R8 · `refine ⟨x, ?_, rfl⟩`** changes the **goal**. To prove `f x ∈ f '' s`, give R3's three parts: the
witness `x`, a proof of `x ∈ s` (left open as `?_`), and `rfl : f x = f x`. `exact ⟨x, hx, rfl⟩` does all
three at once. Placeholders: `{α β : Type} (f : α → β) (s : Set α) (x : α)`.

| Before | After |
|---|---|
| `⊢ f x ∈ f '' s` | `⊢ x ∈ s` |

**W1: R5 with a `∧` inside, R8 twice.** `f '' (s ∩ t) ⊆ f '' s ∩ f '' t` (a different law). After
`rintro y ⟨x, ⟨hs, ht⟩, rfl⟩` the goal is

```lean-goal
⊢ f x ∈ f '' s ∩ f '' t
```

and `exact ⟨⟨x, hs, rfl⟩, ⟨x, ht, rfl⟩⟩` builds the `∧` (R11) of two R8 terms.

---

## Part 2 · `image_preimage_sub`

Statement: `f '' (f ⁻¹' B) ⊆ B`: pushing forward what was pulled back lands inside `B`. A subset goal:
introduce a point (R9) and unpack its image membership in the same `rintro` (R5); what you get is a
preimage membership, which is the goal by definition (R10).

**R9 · `intro x hx`** on `s ⊆ t` changes the **context**. `Set.subset_def : (s ⊆ t) = ∀ x ∈ s, x ∈ t`, so a
subset is proved like any `∀ … →`. `rintro y ⟨…⟩` introduces and destructs at once, and in term mode
`fun x hx => …` does the same. Placeholders: `{α : Type} (s t : Set α)`.

| Before | After |
|---|---|
| `⊢ s ⊆ t` | `x : α, hx : x ∈ s ⊢ x ∈ t` |

**R10 · `Set.mem_preimage`** changes the **goal**. The lemma is `a ∈ f ⁻¹' s ↔ f a ∈ s`, by definition.
So a hypothesis `h : a ∈ f ⁻¹' s` already proves `f a ∈ s` with `exact h`, no rewrite needed.
Placeholders: `{α β : Type} (f : α → β) (s : Set β) (a : α)`.

| Before | After `rw [Set.mem_preimage]` |
|---|---|
| `⊢ a ∈ f ⁻¹' s` | `⊢ f a ∈ s` |

| Before | After `exact h` |
|---|---|
| `h : a ∈ f ⁻¹' s ⊢ f a ∈ s` | closed |

---

## Part 3 · `sub_preimage_image`

Statement: `A ⊆ f ⁻¹' (f '' A)`: every point of `A` is sent into the image of `A`. Introduce the point
(R9); the goal `x ∈ f ⁻¹' (f '' A)` is by definition `f x ∈ f '' A` (R10), which R8 proves. The whole proof
fits in one term `fun x hx => …`.

**W4: R9 and R10 in term mode.** `(f ⁻¹' s)ᶜ ⊆ f ⁻¹' sᶜ` is `fun _ hx => hx`: both sides unfold to
`¬ f x ∈ s`, so the hypothesis is the goal.

---

## Part 4 · `preimage_inter_eq`

Statement: `f ⁻¹' (B ∩ C) = f ⁻¹' B ∩ f ⁻¹' C`. After R1, both sides of the `↔` unfold (R10, R11) to the
same proposition `f x ∈ B ∧ f x ∈ C`, and R12 closes it. No directions to split.

**R11 · `Set.mem_inter_iff`** changes the **goal**. The lemma is `x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b`, by definition.
Build such a membership with `⟨ha, hb⟩`. Placeholders: `{α : Type} (s t : Set α) (a : α)`.

| Before | After `rw [Set.mem_inter_iff]` |
|---|---|
| `⊢ a ∈ s ∩ t` | `⊢ a ∈ s ∧ a ∈ t` |

**R12 · `rfl`** on an `↔` **closes** the goal when both sides unfold to the same proposition (it uses
`Iff.rfl`). It fails when they are only *logically* equivalent, as with images (Part 1, where an `∃` must be
rebuilt). Placeholders: `{α : Type} (s t : Set α) (a : α)`.

| Before | After |
|---|---|
| `⊢ a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t` | closed |

**W2: R1 then R12 on a union.** `f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t`: after `ext x`

```lean-goal
⊢ x ∈ f ⁻¹' (s ∪ t) ↔ x ∈ f ⁻¹' s ∪ f ⁻¹' t
```

both sides are `f x ∈ s ∨ f x ∈ t` by definition, and `rfl` closes it.

**W3: nested `|` inside `⟨…⟩`.** `(s ∪ t) ∩ u ⊆ s ∩ u ∪ t ∩ u` by `rintro x ⟨hs | ht, hu⟩` (R9, R11, R6),
which leaves two goals, both

```lean-goal
⊢ x ∈ s ∩ u ∪ t ∩ u
```

closed by `exact Or.inl ⟨hs, hu⟩` and `exact Or.inr ⟨ht, hu⟩` (R7).

---

## Traps

- The `rfl` pattern substitutes a **variable**: it works on `f x = y` because `y` is a local variable (from
  `ext y` or `rintro y`). After it, the goal speaks about `f x`; there is no `y` left to mention.
- Image membership has three parts, `⟨x, hx, rfl⟩`, in that order: witness, membership, equation. Writing
  `⟨x, rfl, hx⟩` fails.
- `rfl` (R12) cannot prove an image equation: `f '' (A ∪ B)` and `f '' A ∪ f '' B` unfold to an `∃` of an `∨`
  and an `∨` of `∃`s, which are equivalent but not the same. Split with R2 instead.
- In `exact Or.inl ⟨x, hx, rfl⟩` the anonymous constructor belongs to the image, the `Or.inl` to the union
  outside it. Read the goal from the outside in: `f x ∈ f '' A ∪ f '' B` is first a union.
- `''` is two apostrophes and `⁻¹'` is `⁻¹` followed by an apostrophe (`\inv'`); `"` or a missing `'` gives a
  parse error.
- Banned: `Set.image_union`, `Set.image_preimage_subset`, `Set.subset_preimage_image`, `Set.preimage_inter`
  (they are the four statements).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| set equation → membership | `ext x` | R1 |
| split `↔` | `constructor` | R2 |
| see `y ∈ f '' s` as `∃ x ∈ s, f x = y` | `rw [Set.mem_image]` (or nothing: definitional) | R3 |
| see `a ∈ s ∪ t` as `a ∈ s ∨ a ∈ t` | `rw [Set.mem_union]` | R4 |
| use `y ∈ f '' s` | `rintro ⟨x, hx, rfl⟩` / `obtain ⟨x, hx, rfl⟩ := h` | R5 |
| use `a ∈ s ∪ t` | `rintro (ha \| hb)`; nested `⟨x, hx \| hx, rfl⟩` | R6 |
| prove `a ∈ s ∪ t` | `exact Or.inl …` / `exact Or.inr …` | R7 |
| prove `f x ∈ f '' s` | `exact ⟨x, hx, rfl⟩` | R8 |
| prove `s ⊆ t` | `intro x hx` / `rintro x ⟨…⟩` / `fun x hx => …` | R9 |
| `a ∈ f ⁻¹' s` ↔ `f a ∈ s` | `exact h` (definitional) or `rw [Set.mem_preimage]` | R10 |
| `a ∈ s ∩ t` ↔ `a ∈ s ∧ a ∈ t` | `⟨ha, hb⟩`, `rw [Set.mem_inter_iff]` | R11 |
| both sides of `↔` unfold to the same thing | `rfl` | R12 |
| see the state | infoview | |
