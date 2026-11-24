# E006 · Or: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** E001–E005: tactic mode, `intro`, `exact`, `apply`, the anonymous constructor `⟨ha, hb⟩`,
`constructor` on `∧` and on `↔` (E005 R1), `·` blocks (E005 R2), `rintro ⟨ha, hb⟩` and `obtain` for `∧`.
**New here:** the connective `∨` (or). Using a hypothesis `h : A ∨ B` means a **case split**: one goal for
each side (`cases … with`, `rcases … with ha | hb`). Proving `A ∨ B` means **choosing a side** (`left`,
`right`, or the terms `Or.inl`, `Or.inr`). Patterns nest: `⟨_, _⟩` for `∧`, `_ | _` for `∨`.

## How to read an entry

Each entry is one tactic or one proof term. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses (the **context**) `Γ`, **goal** `G`. A cell shows only the
  hypotheses that change. With several goals open, a tactic acts on the first one; the others wait.
- `A B C G : Prop` are arbitrary propositions. `G` plays the role of "whatever the goal is".
- A hypothesis `k`, `k1`, `k2` only finishes the example.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `A ∨ B` | "A or B" (type `\or`). A proof is **either** a proof of `A` **or** a proof of `B`, tagged with which |
| `Or.inl ha`, `Or.inr hb` | the two ways to build `A ∨ B`: from `ha : A` (left) or from `hb : B` (right) |
| `A ∨ B ∨ C` | `A ∨ (B ∨ C)`: `∨` nests to the right, like `∧` |
| `A ∧ B ∨ A ∧ C` | `(A ∧ B) ∨ (A ∧ C)`: `∧` binds tighter than `∨`, so Lean drops these parentheses |
| `A ∧ (B ∨ C)` | here the parentheses are needed and Lean prints them |
| `case inl`, `case inr` | the two goals of a split on `∨`: the left side holds, the right side holds |
| `case mp`, `case mpr` | the two directions after `constructor` on `↔` (E005 R1): `→` and `←` |
| `case mp.inl`, `case inr.inl` | a split inside a split, outer label first: `mp.inl` is the left case of the `∨` inside direction `mp`; `inr.inl` (three-way split) is the right side of the outer `∨`, then the left side of the inner one |
| `h✝ : B`, `right✝ : B` | a hypothesis with no usable name (the `✝`); it came from a `_` in a pattern, or from `cases` without `with` |

---

## Part 1 · `or_swap`

Statement: `P ∨ Q → Q ∨ P`: the order of a disjunction does not matter. Introduce the hypothesis, split it into
its two cases (R1 or R2), and in each case choose the side of the goal where the proof you have fits (R3, R4,
or R5, R6).

### Using an `∨` hypothesis

**R1 · `cases h with | inl ha => tac₁ | inr hb => tac₂`** changes the **goal list and the context**: the goal
is proved twice, once per way `h` could have been built. In `tac₁` the context has `ha : A` instead of `h`;
in `tac₂` it has `hb : B`. Each alternative is `| constructor name => tactics`, with `inl` for the left side
and `inr` for the right. Placeholders: `(A B G : Prop) (h : A ∨ B)`.

| Before | Inside `inl` | Inside `inr` |
|---|---|---|
| `h : A ∨ B ⊢ G` | `ha : A ⊢ G` | `hb : B ⊢ G` |

**R2 · `rcases h with ha | hb`** changes the **goal list and the context**: the same split as R1, in pattern
form. `ha | hb` reads "either `ha` or `hb`". Both goals stay open, labelled `case inl` and `case inr`; close
them in order, or with one `·` block each. Placeholders: as in R1.

| Before | After |
|---|---|
| `h : A ∨ B ⊢ G` | `ha : A ⊢ G`, `hb : B ⊢ G` |

### Proving an `∨` goal

**R3 · `right`** changes the **goal**: it commits to proving the right side. There is no way back: if you
picked the wrong side, the goal may now be unprovable. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `hb : B ⊢ A ∨ B` | `hb : B ⊢ B` |

**R4 · `left`** changes the **goal**: it commits to proving the left side. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `ha : A ⊢ A ∨ B` | `ha : A ⊢ A` |

**R5 · `exact Or.inl ha`** **closes** `A ∨ B` from `ha : A`: `Or.inl : A → A ∨ B` is the left constructor of
`Or`, and `B` is read off the goal. It is `left` followed by `exact ha` in one term. Placeholders:
`(A B : Prop) (ha : A)`.

| Before | After |
|---|---|
| `ha : A ⊢ A ∨ B` | no goals |

**R6 · `exact Or.inr hb`** **closes** `A ∨ B` from `hb : B`: `Or.inr : B → A ∨ B`, the right constructor.
Placeholders: `(A B : Prop) (hb : B)`.

| Before | After |
|---|---|
| `hb : B ⊢ A ∨ B` | no goals |

**W1** (R1 with the same tactic in both branches) on `A ∨ A → A`:

| Step | State |
|---|---|
| start | `⊢ A ∨ A → A` |
| `intro h` | `h : A ∨ A ⊢ A` |
| `cases h with` / `\| inl ha => exact ha` / `\| inr ha => exact ha` | no goals |

**W2** (three alternatives). `A ∨ B ∨ C` is `A ∨ (B ∨ C)`, and `rcases h with ha | hb | hc` splits both `∨`s at
once. Reaching the middle of a goal `A ∨ C ∨ B` takes two choices: `right` then `left`, or the term
`Or.inr (Or.inl hc)`.

| Step | Goals left |
|---|---|
| `intro h` | `h : A ∨ B ∨ C ⊢ A ∨ C ∨ B` |
| `rcases h with ha \| hb \| hc` | `ha : A ⊢ A ∨ C ∨ B`, `hb : B ⊢ A ∨ C ∨ B`, `hc : C ⊢ A ∨ C ∨ B` |

---

## Part 2 · `and_or_distrib`

Statement: `P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R)`: `∧` distributes over `∨`. Lean prints the right side as
`P ∧ Q ∨ P ∧ R`. Split the `↔` with `constructor` (E005 R1) and handle each direction in a `·` block
(E005 R2). In each direction one nested pattern takes the premise apart into two cases (R7, R8); then build
the conclusion (`left`/`right` and `⟨_, _⟩`, or R9).

**R7 · `rintro ⟨ha, hb | hc⟩`** changes the **goal list and the context**: `intro` plus destructuring of a
conjunction whose second half is a disjunction. `⟨_, _⟩` takes the `∧` apart; inside it, `hb | hc` splits the
`∨`, so there are two goals and both keep `ha : A`. Placeholders: `(A B C G : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ (B ∨ C) → G` | `ha : A, hb : B ⊢ G`, `ha : A, hc : C ⊢ G` |

**R8 · `rintro (⟨ha, hb⟩ | ⟨ha', hc⟩)`** changes the **goal list and the context** when the `∨` is outermost:
the alternative `|` is the outer pattern and each side is a `∧` pattern. The **parentheses are required**:
without them `rintro` reads two separate patterns for two separate premises. The names in the two
alternatives may repeat (`⟨ha, hb⟩ | ⟨ha, hc⟩`), since each lives in its own goal. Placeholders:
`(A B C G : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ B ∨ A ∧ C → G` | `ha : A, hb : B ⊢ G`, `ha' : A, hc : C ⊢ G` |

**R9 · `exact ⟨ha, Or.inl hb⟩`** **closes** `A ∧ (B ∨ C)`: the anonymous constructor builds the `∧`, and its
second half is an `∨` proof built with R5. From `hc : C`, write `⟨ha, Or.inr hc⟩` (R6). Placeholders:
`(A B C : Prop) (ha : A) (hb : B)`.

| Before | After |
|---|---|
| `ha : A, hb : B ⊢ A ∧ (B ∨ C)` | no goals |

**W3** (R7, then a different side in each goal; `_` discards the proof of `B`):

| Step | Goals left |
|---|---|
| start | `⊢ A ∧ (B ∨ C) → C ∨ A` |
| `rintro ⟨ha, _ \| hc⟩` | `ha : A, h✝ : B ⊢ C ∨ A`, `ha : A, hc : C ⊢ C ∨ A` |
| `· right` / `exact ha` | `ha : A, hc : C ⊢ C ∨ A` |
| `· left` / `exact hc` | no goals |

**W4** (R8, keeping only the shared part): on `A ∧ B ∨ A ∧ C → A`, `rintro (⟨ha, _⟩ | ⟨ha, _⟩)` gives
two goals, each with `ha : A`, and `exact ha` closes both.

| Before | After `rintro (⟨ha, _⟩ \| ⟨ha, _⟩)` |
|---|---|
| `⊢ A ∧ B ∨ A ∧ C → A` | `ha : A, right✝ : B ⊢ A`, `ha : A, right✝ : C ⊢ A` |

**W5** (`obtain`, for a hypothesis already in the context): `obtain ⟨ha, hb | hc⟩ := h` is R7 without the
`intro`.

| Before | After |
|---|---|
| `h : A ∧ (B ∨ C) ⊢ (B ∨ C) ∧ A` | `ha : A, hb : B ⊢ (B ∨ C) ∧ A`, `ha : A, hc : C ⊢ (B ∨ C) ∧ A` |

---

## Traps

- **Choosing a side too early.** In `or_swap`, `left` or `right` before splitting `h` commits to one side for
  both cases, and one of the two cases is then unprovable. Split the hypothesis first, then choose.
- `cases h` without `with` still splits, but names the new hypothesis `h✝`, which you cannot write. Use
  `cases h with | inl ha => … | inr hb => …` or `rcases h with ha | hb`.
- In `cases … with`, every alternative line starts with `|`. Indent the `|` lines at least as far as `cases`,
  and keep each alternative's tactics after its `=>` (or indented below it).
- `rintro ⟨hp, hq⟩ | ⟨hp, hr⟩` without the outer parentheses is two patterns, not one alternative: write
  `rintro (⟨hp, hq⟩ | ⟨hp, hr⟩)`.
- The goal `P ∧ Q ∨ P ∧ R` means `(P ∧ Q) ∨ (P ∧ R)`: its outermost connective is `∨`, so it needs `left` or
  `right` first, and `constructor` does not apply to it.
- `simp`, `simp_all`, `grind`, and the library facts `or_comm` and `and_or_left` are banned here: the point is
  to do each split and each choice by hand.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| use `h : A ∨ B` (named cases) | `cases h with` / `\| inl ha => …` / `\| inr hb => …` | R1 |
| use `h : A ∨ B` (pattern) | `rcases h with ha \| hb` | R2 |
| prove `A ∨ B` from `B` | `right`, then `exact hb` | R3 |
| prove `A ∨ B` from `A` | `left`, then `exact ha` | R4 |
| the same as terms | `Or.inl ha`, `Or.inr hb` | R5, R6 |
| intro and split `A ∧ (B ∨ C)` | `rintro ⟨ha, hb \| hc⟩` | R7 |
| intro and split `(A ∧ B) ∨ (A ∧ C)` | `rintro (⟨ha, hb⟩ \| ⟨ha, hc⟩)` | R8 |
| prove `A ∧ (B ∨ C)` | `exact ⟨ha, Or.inl hb⟩` / `⟨ha, Or.inr hc⟩` | R9 |
| split `A ∨ B ∨ C` three ways | `rcases h with ha \| hb \| hc` | W2 |
| split a hypothesis already in context | `obtain ⟨ha, hb \| hc⟩ := h` | W5 |
| split an `↔` goal | `constructor`, then one `·` block per direction | E005 R1, R2 |
| see the state | infoview (cursor after a tactic) | |
