# E025 · Bounded quantifiers: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics up to E024: `intro` and `exact` (E003), anonymous constructors `⟨…⟩` (E004, E007),
`obtain ⟨…⟩ := h` (E005), `rcases h with h | h`, `Or.inl`/`Or.inr` (E006), `rw [l] at h` (E009),
`omega` (E011), `decide` (E001), `List.map` and `++` (E024). **New here:** the bounded quantifiers
`∀ x ∈ l, P x` and `∃ x ∈ l, P x` over lists, the library lemmas `List.mem_map`, `List.mem_append`,
`List.mem_cons` that say what membership in `map`, `++` and `::` means, and the `rfl` pattern in `obtain`.
No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`apply`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change. A
  hypothesis that itself contains a comma (`hy : ∃ a, …`) is written on its own line above the `⊢` line.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- `G : Prop` is a goal the step leaves alone: the entry changes the context, and `k : … → G` finishes it.
- `{α β : Type}` are any types of elements (`Nat`, `Bool`, `List Nat`, …).
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Bounded quantifiers

`x ∈ l` (type `Prop`) says that `x` occurs in the list `l`. A bounded quantifier ranges over the elements of
a list; it is pure notation:

| You write | It means | Infoview shows |
|---|---|---|
| `∀ x ∈ l, P x` | `∀ x, x ∈ l → P x` | `∀ (x : α), x ∈ l → P x` |
| `∃ x ∈ l, P x` | `∃ x, x ∈ l ∧ P x` | `∃ x, x ∈ l ∧ P x` |

So everything from E003–E007 applies unchanged: a `∀ … ∈` goal is introduced with **two** names, a
`∀ … ∈` hypothesis `h` is a function taking an element and a membership proof (`h x hx : P x`), an
`∃ … ∈` hypothesis unpacks into three pieces, and an `∃ … ∈` goal needs a witness, a membership proof and
a proof of `P`. The only new work is turning `y ∈ (something built from lists)` into a statement about the
pieces, which is what the three `List.mem_…` lemmas do.

## Reading the goals

| You see | It means |
|---|---|
| `y ∈ l` | `y` is an element of the list `l` |
| `∀ (y : Nat), y ∈ l → P y` | `∀ y ∈ l, P y`, printed unfolded |
| `∃ a, a ∈ l ∧ f a = b` | `∃ a ∈ l, f a = b`, printed unfolded |
| `List.map f l` | `l.map f`: apply `f` to every element |
| `fun x => x * 2` | the function written `(· * 2)` in the statement |
| `s ++ t` | `s` followed by `t` |
| `b :: l` | the list with head `b` and tail `l`; `0 :: xs` puts `0` in front of `xs` |
| `this : P a` | the fact added by a `have :=` with no name (R4) |
| `case inl`, `case inr` | the two goals made by `rcases h with h \| h` (left and right side of `∨`) |
| `case refine_1`, `case refine_2` | the goals for the two `?_` of a `refine` (R9) |

---

## Part 1 · `all_map_double`

Statement: if every element of `xs` is positive, then every element of `xs.map (· * 2)` (every element
doubled) is greater than 1. Introduce `y` and `hy : y ∈ List.map (fun x => x * 2) xs`, read `hy` as "`y` is
`x * 2` for some `x ∈ xs`", substitute `y := x * 2`, get `x > 0` from `h`, and finish by arithmetic.

**R1 · `intro y hy`** changes the **goal and the context**: the goal `∀ y ∈ l, P y` loses its binder and its
membership premise, which become `y : α` and `hy : y ∈ l`. `intro y` alone would leave `y ∈ l → P y`.
Placeholders: `{α : Type} (l : List α) (P : α → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ (y : α), y ∈ l → P y` | `y : α, hy : y ∈ l ⊢ P y` |

**R2 · `rw [List.mem_map] at hy`** changes the **context**. The lemma is
`List.mem_map : b ∈ List.map f l ↔ ∃ a, a ∈ l ∧ f a = b`: `b` is in the mapped list exactly when it is
the image `f a` of some `a` in `l`. `rw` with an `↔` replaces one proposition by the other. With
`f := fun x => x * 2`, Lean also simplifies `(fun x => x * 2) a` to `a * 2`. Placeholders:
`{α β : Type} (f : α → β) (l : List α) (b : β)`.

| Before | After |
|---|---|
| `hy : b ∈ List.map f l ⊢ G` | `hy : ∃ a, a ∈ l ∧ f a = b`<br>`⊢ G` |

**R3 · `obtain ⟨a, ha, rfl⟩ := hy`** changes the **context and the goal**. `hy` splits into the witness
`a : α`, `ha : a ∈ l`, and the equation `f a = b`. The pattern `rfl` does not keep the equation: it
substitutes `b := f a` everywhere and removes `b`. This works because `b` is a local variable (here: the
`y` you introduced). Placeholders: `{α β : Type} (f : α → β) (l : List α) (b : β) (P : β → Prop)`.

| Before | After |
|---|---|
| `hy : ∃ a, a ∈ l ∧ f a = b`<br>`⊢ P b` | `a : α, ha : a ∈ l ⊢ P (f a)` |

**R4 · `have := h a ha`** changes the **context**: it applies the bounded hypothesis
`h : ∀ x ∈ l, P x` to the element `a` and the proof `ha : a ∈ l`, and adds the result `this : P a`. Needed
before `omega`, which uses facts about numbers but never instantiates a `∀`. Placeholders:
`{α : Type} (l : List α) (P : α → Prop) (a : α) (ha : a ∈ l)`, with
`h : ∀ x ∈ l, P x` (printed `h : ∀ (x : α), x ∈ l → P x`) in the context.

| Before | After |
|---|---|
| `ha : a ∈ l ⊢ G` | `ha : a ∈ l, this : P a ⊢ G` |

**R5 · `omega`** **closes** a goal of linear arithmetic over `Nat` (`+`, `*` by a literal, `<`, `≤`, `>`,
`=`), using the arithmetic hypotheses in the context. Placeholders: `(a : Nat)`.

| Before | After |
|---|---|
| `this : a > 0 ⊢ a * 3 > 2` | no goals |

**W1 (on `(· + 3)`, no hypothesis):** `∀ y ∈ xs.map (· + 3), y ≥ 3` by R1, R2, R3, R5. After R2 the
function is already applied:

```lean-goal
⊢ ∀ (y : Nat), y ∈ List.map (fun x => x + 3) xs → y ≥ 3
⊢ y ≥ 3
⊢ x + 3 ≥ 3
```

The middle line is the goal both after R1 and after R2 (R2 changes only `hy`, to
`∃ a, a ∈ xs ∧ a + 3 = y`); the last is after R3, where `y` has become `x + 3`.

---

## Part 2 · `all_append`

Statement: if `p` holds on every element of `xs` and on every element of `ys`, it holds on every element of
`xs ++ ys`. Introduce `z` and `hz`, read `hz : z ∈ xs ++ ys` as `z ∈ xs ∨ z ∈ ys`, split the `∨`, and close
each case with the matching hypothesis.

**R1** as in Part 1, with names `z hz`.

**R6 · `rw [List.mem_append] at hz`** changes the **context**. The lemma is
`List.mem_append : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t`. Placeholders: `{α : Type} (s t : List α) (c : α)`.

| Before | After |
|---|---|
| `hz : c ∈ s ++ t ⊢ G` | `hz : c ∈ s ∨ c ∈ t ⊢ G` |

**R7 · `rcases hz with hz | hz`** changes the **goal list and the context**: one goal per side of the `∨`,
each with `hz` proving that side. Handle each with a `·` bullet. Placeholders:
`{α : Type} (s t : List α) (c : α) (P : α → Prop)`.

| Before | After |
|---|---|
| `hz : c ∈ s ∨ c ∈ t ⊢ P c` | `hz : c ∈ s ⊢ P c`, `hz : c ∈ t ⊢ P c` |

**R8 · `exact h a ha`** **closes** the goal `P a`: R4 used directly as the proof instead of stored as `this`.
Placeholders: `{α : Type} (l : List α) (P : α → Prop) (h : ∀ x ∈ l, P x) (a : α) (ha : a ∈ l)`.

| Before | After |
|---|---|
| `ha : a ∈ l ⊢ P a` | no goals |

---

## Part 3 · `exists_big`

Statement: if `3 ∈ xs`, then some element of `0 :: xs` is greater than 2. The witness is `3`; it sits in the
**tail** `xs` of `0 :: xs`, not at the head. The proof is one anonymous constructor
`⟨witness, membership proof, proof of 3 > 2⟩`, either as a term or via `refine` with two `?_`.

**R9 · `refine ⟨a, ?_, ?_⟩`** changes the **goal list**: the goal `∃ x ∈ l, P x`, that is
`∃ x, x ∈ l ∧ P x`, becomes the two goals `a ∈ l` and `P a`. As a term, `⟨a, hm, hp⟩` with
`hm : a ∈ l`, `hp : P a` proves it in one go: the constructor flattens `⟨a, ⟨hm, hp⟩⟩`. Placeholders:
`{α : Type} (l : List α) (P : α → Prop) (a : α)`.

| Before | After |
|---|---|
| `⊢ ∃ x, x ∈ l ∧ P x` | `⊢ a ∈ l`, `⊢ P a` |

**R10 · `apply List.mem_cons.mpr`** changes the **goal**. The lemma is
`List.mem_cons : a ∈ b :: l ↔ a = b ∨ a ∈ l`: an element of `b :: l` is the head or an element of the tail.
For an `↔` named `e`, `e.mpr` is its right-to-left direction (a function `(a = b ∨ a ∈ l) → a ∈ b :: l`) and
`e.mp` the left-to-right one. As a term: `List.mem_cons.mpr hor` with `hor : a = b ∨ a ∈ l`.
Placeholders: `{α : Type} (a b : α) (l : List α)`.

| Before | After |
|---|---|
| `⊢ a ∈ b :: l` | `⊢ a = b ∨ a ∈ l` |

**R11 · `exact Or.inr h`** **closes** `A ∨ B` from `h : B`; `Or.inl` takes a proof of the left side `A`.
Placeholders: `(A B : Prop) (h : B)`.

| Before | After |
|---|---|
| `h : B ⊢ A ∨ B` | no goals |

**R12 · `decide`** **closes** a comparison of `Nat` literals by computing it. As a term inside `⟨…⟩`, write
`by decide`.

| Before | After |
|---|---|
| `⊢ 7 > 4` | no goals |

**W2 (witness at the head):** `∃ x ∈ 5 :: xs, x > 4` with witness `5`. R9 gives

```lean-goal
⊢ 5 ∈ 5 :: xs
⊢ 5 > 4
```

The first goal: R10, then the **left** side `5 = 5` by `Or.inl rfl`. The second: R12.

---

## Traps

- `intro y` with one name leaves `⊢ y ∈ l → P y`; a bounded `∀` needs two names (R1).
- `omega` does not use `h : ∀ x ∈ xs, x > 0`: it never instantiates a `∀`. Put `h x hx` into the context
  first (R4).
- The `rfl` pattern (R3) substitutes a **variable**: it works because the equation is `x * 2 = y` with `y`
  a local name. For an equation between two compound terms, name it (`⟨x, hx, hxy⟩`) and `rw [← hxy]`.
- `rw [List.mem_map]` rewrites the goal; to rewrite the hypothesis write `at hy`.
- `Or.inl` vs `Or.inr`: in `0 :: xs` the witness `3` is in the tail, so the right side `3 ∈ xs` (R11).
  `Or.inl` would need `3 = 0`.
- `decide` needs closed terms: it proves `3 > 2`, not `x > 2` for a variable `x`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| prove `∀ y ∈ l, P y` | `intro y hy` | R1 |
| `hy : b ∈ l.map f` → `∃ a ∈ l, f a = b` | `rw [List.mem_map] at hy` | R2 |
| unpack and substitute `b := f a` | `obtain ⟨a, ha, rfl⟩ := hy` | R3 |
| use `h : ∀ x ∈ l, P x` at `a` | `have := h a ha` / `exact h a ha` | R4, R8 |
| linear `Nat` arithmetic | `omega` | R5 |
| `hz : c ∈ s ++ t` → `c ∈ s ∨ c ∈ t` | `rw [List.mem_append] at hz` | R6 |
| split an `∨` hypothesis | `rcases hz with hz \| hz` | R7 |
| prove `∃ x ∈ l, P x` | `⟨a, hm, hp⟩` / `refine ⟨a, ?_, ?_⟩` | R9 |
| prove `a ∈ b :: l` | `List.mem_cons.mpr (Or.inl …)` / `(Or.inr …)` | R10, R11 |
| compare `Nat` literals | `decide` | R12 |
| see the state | infoview | |
