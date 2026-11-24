# E058 · Classical logic: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `intro`/`exact`/`apply` (E003), anonymous
constructors `⟨_, _⟩` (E004, E005), `left`/`right` and `rcases` on `∨` (E006), `¬A` as `A → False` (E008),
`·` focusing and `refine … ?_` (E031). **New here:** classical reasoning in core Lean: the excluded middle
`Classical.em`, proof by contradiction `Classical.byContradiction`, the `by_cases` tactic on an arbitrary
`Prop`, and `absurd`. No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `A B : Prop` are arbitrary propositions; `G : Prop` is "whatever the goal is".
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Classical vs constructive in one paragraph

Lean's logic is constructive by default: a proof of `A ∨ B` must say which side holds, and `¬A` is just the
function type `A → False`. From `A` you get `¬¬A` for free (`fun hna => hna ha`), but the converse `¬¬A → A`,
and every tautology in this exercise, is not provable without an extra axiom. Core Lean supplies it as
`Classical.em (p : Prop) : p ∨ ¬p` (derived from the axiom of choice `Classical.choice`). Everything classical
here comes from it: `Classical.byContradiction` (R1) and the `by_cases` tactic (R4) are built on it. That is why
`#print axioms` on your solution lists `Classical.choice` (allowed by the checker).

## Reading the goals

| You see | It means |
|---|---|
| `¬A` | `Not A`, defined as `A → False`: a function from proofs of `A` to `False` |
| `¬¬A` | `¬(¬A)`, i.e. `(A → False) → False` |
| `False` | the proposition with no proof; a goal `False` means "derive a contradiction" |
| `A → B` | implication; a proof is a function from proofs of `A` to proofs of `B` |
| `A ∨ B` | `Or A B`: a proof is `Or.inl ha` or `Or.inr hb` |
| `A ∧ B` | `And A B`: a proof is a pair `⟨ha, hb⟩` |
| `¬P ∨ ¬Q`, `¬(P ∧ Q)` | `¬` binds tighter than `∧` and `∨`: the first is `(¬P) ∨ (¬Q)`; the second negates the whole conjunction |
| `Not P`, `And P Q`, `Or P Q` | the same as `¬P`, `P ∧ Q`, `P ∨ Q`, written as function applications (how `#print axioms` and the checker print them) |
| `A → B → C` | `→` nests to the right: `A → (B → C)`; parentheses on the left, as in `(A → B) → C`, mean an argument that is itself a function |
| `case pos`, `case neg` | the two goals after `by_cases h : A`: with `h : A`, then with `h : ¬A` |
| `case inl`, `case inr` | the two goals after `rcases … with ha \| hna` on an `∨` |

---

## Part 1 · `dne`

Statement: double-negation elimination, `¬¬P → P` (with the hypothesis `h : ¬¬P` already in the context).
Assume `¬P` and derive `False` using `h`.

**R1 · `refine Classical.byContradiction fun hn => ?_`** changes the **context and the goal**: it adds
`hn : ¬A` and the goal becomes `False`. The lemma is `Classical.byContradiction {p : Prop} : (¬p → False) → p`.
`fun hn => ?_` is the function it expects; `?_` is the hole you fill next. Placeholders: `(A G : Prop)`.
As a term, `Classical.byContradiction f` proves `A` directly from any `f : ¬A → False`.

| Before | After |
|---|---|
| `⊢ A` | `hn : ¬A ⊢ False` |

**R2 · `exact hna ha`** **closes** `False`: `hna : ¬A` is a function `A → False`, applied to `ha : A`.
Placeholders: `(A : Prop) (ha : A) (hna : ¬A)`.

| Before | After |
|---|---|
| `ha : A, hna : ¬A ⊢ False` | no goals |

In `dne` the function and the argument are both already there: compare the type of `h` with the type
`Classical.byContradiction` expects.

## Part 2 · `peirce`

Statement: Peirce's law, `((P → Q) → P) → P`. Introduce the hypothesis `h : (P → Q) → P`, split on `P`. If `P`
holds you are done. If `¬P` holds, `h` still produces `P` once you give it a function `P → Q`, and such a
function exists because its input `P` contradicts `¬P`.

**R3 · `intro h`** on `A → B` changes the **context and the goal**: `h : A` is added, the goal becomes `B`.
Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A → B` | `h : A ⊢ B` |

**R4 · `by_cases h : A`** changes the **goal list**: one goal becomes two, the first with `h : A`
(case `pos`), the second with `h : ¬A` (case `neg`). It works for every `A : Prop` because it uses
`Classical.em` when `A` is not decidable. Placeholders: `(A G : Prop)`. Follow it with two `·` blocks.

| Before | After |
|---|---|
| `⊢ G` | `h : A ⊢ G`, `h : ¬A ⊢ G` |

**R5 · `apply h`** with `h : A → B` changes the **goal**: to prove `B`, it suffices to prove `A`.
Placeholders: `(A B : Prop) (h : A → B)`. In `peirce` the hypothesis has type `(P → Q) → P`, so `apply h`
turns the goal `P` into `P → Q`.

| Before | After |
|---|---|
| `h : A → B ⊢ B` | `h : A → B ⊢ A` |

**R6 · `absurd`** **closes** any goal from contradictory facts. The lemma is
`absurd {a : Prop} {b : Sort v} : a → ¬a → b` (`Sort v` covers both `Prop` and `Type`, so `b` can be any
goal). Placeholders: `(A G : Prop) (ha : A) (hna : ¬A)`. Note the argument order: the fact first, its negation
second.

| Before | After |
|---|---|
| `ha : A, hna : ¬A ⊢ G` | no goals |

R5, then R3, then R6 is the step-by-step form. The one-term form passes the function `fun x => …`
directly as the argument of `h`, the way W1 does with a different `h`.

**W1: `¬(A → B) → A`** (R3, R1, then a `fun` argument closed by R6):

```lean-goal
⊢ ¬(A → B) → A
⊢ A
⊢ False
```

## Part 3 · `contrapos`

Statement: from `h : ¬Q → ¬P`, conclude `P → Q`. Introduce `hp : P`, then split on `Q` with the excluded
middle. If `Q`, done. If `¬Q`, then `h` gives `¬P`, which contradicts `hp`.

**R7 · `rcases Classical.em A with ha | hna`** changes the **goal list**: one goal becomes two, the first with
`ha : A` (case `inl`), the second with `hna : ¬A` (case `inr`). The lemma is `Classical.em (p : Prop) : p ∨ ¬p`.
Same effect as R4, with the excluded middle named explicitly. Placeholders: `(A G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `ha : A ⊢ G`, `hna : ¬A ⊢ G` |

In the `¬Q` branch, `h hnq : ¬P` is a term (R2's "apply the function" again), and R6 combines it with `hp`.

**W3: `(¬A → B) → A ∨ B`** (R3, R7, then R11 / R8):

```lean-goal
⊢ (¬A → B) → A ∨ B
⊢ A ∨ B
```

## Part 4 · `not_and_split`

Statement: De Morgan for `∧`: from `h : ¬(P ∧ Q)`, conclude `¬P ∨ ¬Q`. Split on `P`. If `P`, the right side
`¬Q` holds: assuming `Q` gives `P ∧ Q`, contradicting `h`. If `¬P`, the left side holds directly.

**R8 · `right`** changes the **goal**: `A ∨ B` becomes `B`. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∨ B` | `⊢ B` |

**R9 · `intro hb`** on `¬B` changes the **context and the goal**: `¬B` is `B → False`, so `hb : B` is added and
the goal becomes `False`. Placeholders: `(B : Prop)`.

| Before | After |
|---|---|
| `⊢ ¬B` | `hb : B ⊢ False` |

**R10 · `exact h ⟨ha, hb⟩`** **closes** `False` when `h : ¬(A ∧ B)`: the argument `h` needs is a proof of
`A ∧ B`, and `⟨ha, hb⟩` is one. Placeholders: `(A B : Prop) (h : ¬(A ∧ B)) (ha : A) (hb : B)`.

| Before | After |
|---|---|
| `h : ¬(A ∧ B), ha : A, hb : B ⊢ False` | no goals |

**R11 · `left`** changes the **goal**: `A ∨ B` becomes `A`. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∨ B` | `⊢ A` |

**W2: `(A → B) → ¬A ∨ B`** (R3, R4, then R8 in case `pos` and R11 in case `neg`):

| Start | After `intro h` | After `by_cases ha : A` |
|---|---|---|
| `⊢ (A → B) → ¬A ∨ B` | `h : A → B ⊢ ¬A ∨ B` | `ha : A ⊢ ¬A ∨ B`, `ha : ¬A ⊢ ¬A ∨ B` |

---

## Traps

- `by_contra` does not exist in core Lean: it is a Mathlib tactic. Write
  `refine Classical.byContradiction fun h => ?_` (R1), or use the term `Classical.byContradiction f`.
- `absurd` takes the fact first and its negation second: `absurd ha hna`, not `absurd hna ha` (R6).
- `¬A` is a function. `intro` works on a goal `¬A` (R9), and `hna ha : False` applies a hypothesis `hna : ¬A`
  (R2). No unfolding is needed.
- `by_cases h : A` and `rcases Classical.em A with ha | hna` name the hypothesis differently: one name for
  both branches vs one name per branch.
- After a split, the two goals are worked on in order. Use `·` for each, or the second branch's tactics run on
  the wrong goal (TACTIC_STATES, "Structure").
- `simp`, `simpa`, `simp_all`, `grind` and the library forms of these laws (`Classical.not_not`, …) are on the
  BANNED line: do the case splits yourself.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| assume `¬A`, prove `False` | `refine Classical.byContradiction fun hn => ?_` | R1 |
| `False` from `ha : A`, `hna : ¬A` | `exact hna ha` | R2 |
| prove `A → B` | `intro h` | R3 |
| split on any `A : Prop` | `by_cases h : A` | R4 |
| prove `B` from `h : A → B` | `apply h` | R5 |
| any goal from `ha : A`, `hna : ¬A` | `exact absurd ha hna` | R6 |
| split on `A ∨ ¬A` explicitly | `rcases Classical.em A with ha \| hna` | R7 |
| prove the right side of `∨` | `right` | R8 |
| prove `¬B` | `intro hb` (goal `False`) | R9 |
| `False` from `h : ¬(A ∧ B)` | `exact h ⟨ha, hb⟩` | R10 |
| prove the left side of `∨` | `left` | R11 |
| see the state | infoview | |
