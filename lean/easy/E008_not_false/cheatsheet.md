# E008 · Not and False: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** E003 (`intro`, `exact`, `apply`), E004 (`fun`, anonymous constructor `⟨_, _⟩`), E005
(`constructor`, `rintro ⟨_, _⟩`, `↔`, focusing with `·`) and E006 (`Or.inl`, `Or.inr`, the case pattern
`a | b`).
**New here:** negation and falsity. `False` is the proposition with no proof. `¬A` is **defined** as
`A → False`: a proof of `¬A` is a function turning any proof of `A` into a proof of `False`. Everything below
follows from that one definition, plus *ex falso*: from `False`, any goal follows (`exfalso`, `absurd`,
`contradiction`).

## How to read an entry

Each entry is one tactic or one term. It says what changes (**goal**, **context**, or **goal list**), lists
the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `A B C D G : Prop` are arbitrary propositions; `G` is any goal when the step does not look at it. A
  hypothesis `k` only finishes the example.
- "no goals" means the step closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `¬A` | `A → False` ("not `A`"); typed `\not` or `\neg` |
| `False` | the proposition with no proof; reaching it means the context is contradictory |
| `hn : ¬A` | a function: `hn ha : False` for any `ha : A` |
| `¬(A ∧ B)` | `A ∧ B → False`; parentheses matter: `¬A ∧ B` is `(¬A) ∧ B` |
| `¬A ∧ ¬B` | `(¬A) ∧ (¬B)`: `¬` binds tighter than `∧`, `∨`, `→`, `↔` |
| `A ∧ C ∨ B ∧ D` | `(A ∧ C) ∨ (B ∧ D)`: `∧` binds tighter than `∨`, so Lean drops these parentheses |
| `¬¬A` | `(A → False) → False` |
| `A → B → ¬C` | `A → (B → (C → False))`: `→` nests to the right |
| `¬A ↔ A → False` | `¬A ↔ (A → False)`; Lean prints it without the parentheses |
| `case mp`, `case mpr` | the `→` and `←` goals after `constructor` on `↔` |
| `case inl`, `case inr` | the left and right cases after splitting an `∨` |

---

## Part 1 · `not_and_not`

Statement: `¬(P ∧ ¬P)`: `P` and `¬P` cannot both hold. Open the negation and split the conjunction in one
step (R3), then apply the negation to its argument (R2), or let Lean find the clash (R4).

**R1 · `intro h` on `¬A`** changes the **goal and the context**: `¬A` is `A → False`, so `intro` works as on
any implication. Placeholders: `(A : Prop)`.

| Before | After |
|---|---|
| `⊢ ¬A` | `h : A ⊢ False` |

**R3 · `rintro ⟨ha, hb⟩` on `¬(A ∧ B)`** changes the **goal and the context**: it introduces the `A ∧ B`
hidden in `¬(A ∧ B) = (A ∧ B → False)` and splits it in one step. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ ¬(A ∧ B)` | `ha : A, hb : B ⊢ False` |

**R2 · `exact hn ha`** **closes** `False`: `hn : ¬A` is a function `A → False`, so `hn ha : False`.
Placeholders: `(A : Prop) (ha : A) (hn : ¬A)`.

| Before | After |
|---|---|
| `ha : A, hn : ¬A ⊢ False` | no goals |

**R4 · `contradiction`** **closes** any goal when the context contains some `ha : A` together with
`hn : ¬A` (also: a hypothesis `False`, or `a ≠ a`). It finds the pair itself. It does **not** look inside
functions: `h : A → ¬A` with `ha : A` is not a clash it sees. Placeholders: `(A G : Prop)`.

| Before | After |
|---|---|
| `ha : A, hn : ¬A ⊢ G` | no goals |

**W2** (R3, R2): from `hna : ¬A`, refute `A ∧ B`:

| Step | State |
|---|---|
| start | `hna : ¬A ⊢ ¬(A ∧ B)` |
| `rintro ⟨ha, hb⟩` | `hna : ¬A, ha : A, hb : B ⊢ False` |
| `exact hna ha` | no goals |

## Part 2 · `contrapositive`

Statement: `(P → Q) → ¬Q → ¬P`. Three arrows, the last one hidden inside `¬P`: introduce three names (R5),
then chain the two functions (R6).

**R5 · `intro h1 h2 h3` through a trailing `¬`** changes the **goal and the context**: `A → B → ¬C` is
`A → B → C → False`, so a third name takes the `C`, and the goal becomes `False`. Placeholders:
`(A B C : Prop)`.

| Before | After `intro ha hb hc` |
|---|---|
| `⊢ A → B → ¬C` | `ha : A, hb : B, hc : C ⊢ False` |

**R6 · `exact hnb (hab ha)`** **closes** `False` by nested application, read inside out: `hab ha : B`, then
`hnb (hab ha) : False`. Placeholders: `(A B : Prop) (hab : A → B) (hnb : ¬B) (ha : A)`.

| Before | After |
|---|---|
| `hab : A → B, hnb : ¬B, ha : A ⊢ False` | no goals |

**W3** (R5, R6 with a lambda, R10, as the argument): `¬¬¬A → ¬A`.

| Step | State |
|---|---|
| start | `⊢ ¬¬¬A → ¬A` |
| `intro h ha` | `h : ¬¬¬A, ha : A ⊢ False` |
| `exact h (fun hn => hn ha)` | no goals (`fun hn => hn ha : ¬¬A`) |

## Part 3 · `from_clash`

Statement: from `hp : P` and `h : P → ¬P`, prove an arbitrary `Q`. `Q` has nothing to do with `P`, so
switch the goal to `False` (R7) and build `False` from the clash: `h hp : ¬P`, and `¬P` applied to `hp`
gives `False` (R2, R6). Or close it in one step with `absurd` (R8).

**R7 · `exfalso`** changes the **goal** to `False`; the context is unchanged. Valid because `False` implies
anything. Placeholders: `(G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ False` |

**R8 · `exact absurd ha hn`** **closes** any goal. The lemma is `absurd : a → ¬a → b` (for any
propositions `a`, `b`): the first argument proves `A`, the second `¬A`. Either argument can be a compound
term, e.g. `absurd ha (f ha)` when `f ha : ¬A`. Placeholders: `(A G : Prop) (ha : A) (hn : ¬A)`.

| Before | After |
|---|---|
| `ha : A, hn : ¬A ⊢ G` | no goals |

**W4** (R7, then a full application): `h : ¬A → ¬B` takes `hna : ¬A` and returns `¬B`, which takes one
more argument:

| Step | State |
|---|---|
| start | `h : ¬A → ¬B, hna : ¬A, hb : B ⊢ C` |
| `exfalso` | `h : ¬A → ¬B, hna : ¬A, hb : B ⊢ False` |
| `exact h hna hb` | no goals |

## Part 4 · `not_or_iff`

Statement: `¬(P ∨ Q) ↔ ¬P ∧ ¬Q` (one of De Morgan's laws). Split the `↔` (R9).
**→:** introduce `h : ¬(P ∨ Q)` with a plain `intro h` (E003), and give the pair (R12) of two negations, each
a lambda (R10) that feeds `h` an `∨` built by R11. **←:** one `rintro` that splits the `∧` (R3's pattern)
and then the `∨` (R13), giving two `False` goals, each closed by R2.

**R9 · `constructor` on `A ↔ B`** changes the **goal list**: one goal per direction, named `mp` (→) and
`mpr` (←). Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B`, `⊢ B → A` |

**R10 · `fun ha => e`** is a **term** that **closes** `¬A`, where `e : False` may use `ha : A`. It is the
term-mode twin of R1. Placeholders: `(A : Prop) (k : A → False)`.

| Before | After `exact fun ha => k ha` |
|---|---|
| `k : A → False ⊢ ¬A` | no goals |

**R11 · `Or.inl ha`, `Or.inr hb`** are **terms** of `A ∨ B` built from `ha : A` or `hb : B`. Their main use
here is as an argument: with `h : ¬(A ∨ B)`, `h (Or.inl ha) : False`. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `ha : A ⊢ A ∨ B` | no goals (`exact Or.inl ha`) |
| `hb : B ⊢ A ∨ B` | no goals (`exact Or.inr hb`) |

**R12 · `exact ⟨e₁, e₂⟩`** **closes** `A ∧ B` from any terms `e₁ : A`, `e₂ : B`, lambdas included.
Placeholders: `(A B : Prop) (ka : A → False) (kb : B → False)`.

| Before | After `exact ⟨fun ha => ka ha, fun hb => kb hb⟩` |
|---|---|
| `ka : A → False, kb : B → False ⊢ ¬A ∧ ¬B` | no goals |

**R13 · `rintro (hc | hd)` on `¬(C ∨ D)`** changes the **goal list and the context**: it introduces the
`C ∨ D` and splits it by cases, so there is one `False` goal per side, `inl` with `hc : C`, `inr` with
`hd : D`. Focus each with `·`. Placeholders: `(C D : Prop)`.

| Before | After |
|---|---|
| `⊢ ¬(C ∨ D)` | `hc : C ⊢ False`, `hd : D ⊢ False` |

**W5** (R3's pattern, then R13's, in one `rintro`): patterns are consumed left to right, one per arrow.

| Step | State |
|---|---|
| start | `⊢ A ∧ B → C ∨ D → A ∧ C ∨ B ∧ D` |
| `rintro ⟨ha, hb⟩ (hc \| hd)` | `ha : A, hb : B, hc : C ⊢ A ∧ C ∨ B ∧ D`, `ha : A, hb : B, hd : D ⊢ A ∧ C ∨ B ∧ D` |
| `· exact Or.inl ⟨ha, hc⟩` | `ha : A, hb : B, hd : D ⊢ A ∧ C ∨ B ∧ D` |
| `· exact Or.inr ⟨hb, hd⟩` | no goals |

**W1** (R9, then R1 and R2 in each direction): `¬A` and `A → False` are the same proposition.

| Step | State |
|---|---|
| start | `⊢ ¬A ↔ A → False` |
| `constructor` | `⊢ ¬A → A → False`, `⊢ (A → False) → ¬A` |
| `· intro h ha; exact h ha` (each) | no goals |

---

## Traps

- `¬A` is a function, not a fact about `A`. With `hn : ¬A`, write `hn ha`, not `hn` alone, to get `False`;
  and `exact hn` closes only a goal `¬A` (or `A → False`).
- `contradiction` looks for `A` and `¬A` side by side. In `from_clash` the `¬P` is hidden behind `h : P → ¬P`,
  so `contradiction` fails there until you add `h hp : ¬P` to the context; use `exfalso` + application or
  `absurd` instead.
- `intro` on a goal `¬A` does not fail: it takes `A` and leaves `False`. On `(A → B) → ¬B → ¬A` you need
  **three** names, the third for the `A` inside `¬A`.
- `¬A ∧ ¬B` is `(¬A) ∧ (¬B)`, not `¬(A ∧ B)`: `¬` binds tightest.
- `rintro (hp | hq)` produces two goals. `t ; u` runs `u` on the first only; focus each with `·`
  (TACTIC_STATES, "Structure").
- `simp`, `simp_all`, `grind` and the library lemma for this De Morgan law are banned: prove it by hand.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| prove `¬A` (tactic) | `intro ha` (goal becomes `False`) | R1 |
| prove `¬A` (term) | `fun ha => …` | R10 |
| `False` from `ha : A`, `hn : ¬A` | `exact hn ha` | R2 |
| open `¬(A ∧ B)` and split | `rintro ⟨ha, hb⟩` | R3 |
| let Lean find `A`, `¬A` in context | `contradiction` | R4 |
| several arrows, the last a `¬` | `intro h1 h2 h3` | R5 |
| chain functions into `False` | `exact hnb (hab ha)` | R6 |
| any goal → `False` | `exfalso` | R7 |
| any goal from `A` and `¬A` | `exact absurd ha hn` | R8 |
| split `↔` | `constructor`, then `·` per direction | R9 |
| build `A ∨ B` | `Or.inl ha` / `Or.inr hb` | R11 |
| build `A ∧ B` | `⟨e₁, e₂⟩` | R12 |
| open `¬(C ∨ D)` and split by cases | `rintro (hc \| hd)` | R13 |
| `∧` then `∨`, one pattern per arrow | `rintro ⟨h1, h2⟩ (ha \| hb)` | R3, R13, W5 |
| see the state | infoview | |
