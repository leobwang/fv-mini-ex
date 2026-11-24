# E052 · Pairs: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `rfl` (E001), `exact`/`apply` (E003),
`obtain ⟨_, _⟩` on `∧`/`∃` (E005, E007), `Nat.add_comm` (E009), `unfold` (E012), structures, projections and
`dsimp only` (E017). **New here:** the product type `α × β`: its projections `.1`/`.2`, eta
(`(p.1, p.2) = p` by definition), extensionality `Prod.ext`, `obtain ⟨a, b⟩` on a pair, and functions
defined by a pattern-matching lambda `fun (a, b) => …`. Core Lean only, no Mathlib.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**), lists
the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`, `P : α × β → Prop`, `P : Nat → Prop`). The step changes only
  the part inside `P (…)`, wherever it sits in a larger goal.
- `{α β : Type}` are arbitrary types. "no goals" means the step closed the goal.
- The entries use the guide's own functions: `mapFst f p := (f p.1, p.2)` and
  `mulPair := fun (a, b) => a * b`. In the exercise, `swap` and `addPair` play these roles.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Pairs in one paragraph

`α × β` (notation for `Prod α β`) is a structure with one constructor `Prod.mk (fst : α) (snd : β)`, written
`(a, b)`. Its projections are `p.fst` and `p.snd`; `p.1`, `p.2` are the same thing and the infoview always
prints `.fst`/`.snd`. A projection of a literal pair reduces by definition, `(a, b).fst ≡ a` (R1), and so does
**eta**: `(p.fst, p.snd) ≡ p` for every `p`, even a variable one (R2). Because of this, `rfl` proves any goal
whose two sides agree after unfolding definitions and reducing projections. A `match` on a *variable* pair
does **not** reduce: `fun (a, b) => a + b` applied to `p` is stuck until `p` is split into `(a, b)` (R5).

## Reading the goals

| You see | It means |
|---|---|
| `α × β`, `Nat × Nat` | the type of pairs with first component in `α`, second in `β` |
| `(a, b)` | `Prod.mk a b`, the pair with components `a`, `b` |
| `p.fst`, `p.snd` | the first / second component; what you wrote as `p.1` / `p.2` |
| `(a, b).fst` | a projection of a literal pair; reduces to `a` (R1) |
| `swap (swap p)` | your `swap` applied twice; `unfold swap` shows the pair it builds (R3) |
| `fun (a, b) => a + b` | a pattern-matching lambda on a pair: `fun x => match x with \| (a, b) => a + b` |
| `match (x, y) with \| (a, b) => a * b` | an unfolded pattern lambda applied to `(x, y)`; reduces to `x * y` (R6) |
| `case fst`, `case snd` | the two goals `apply Prod.ext` produces (R4) |

---

## Part 1 · `swap_swap`

Statement: `swap (swap p) = p` for `p : α × β`: swapping twice gives the pair back. Unfold `swap` (R3); both
occurrences go, leaving `((p.snd, p.fst).snd, (p.snd, p.fst).fst) = p`. Reducing the projections (R1) gives
`(p.fst, p.snd) = p`, which is eta, so `dsimp only` closes the goal right there (W4); an `rfl` after it fails
with "no goals". Alternatively, `rfl` (R2) does the whole proof in one step.

**R1 · `dsimp only`** changes the **goal**: a projection of a literal pair is replaced by that component,
`(a, b).fst → a`, `(a, b).snd → b`. If the two sides of an equation then agree (eta included), `dsimp only`
closes it. Placeholders: `{α β : Type} (a : α) (b : β) (P : α → Prop)`.

| Before | After |
|---|---|
| `⊢ P (a, b).fst` | `⊢ P a` |

**R2 · `rfl`** **closes** `(p.fst, p.snd) = p`: eta for pairs holds by definition, for any `p : α × β`. `rfl`
also unfolds definitions and reduces projections first, so it closes any goal R3 and R1 would reduce to this.
Placeholders: `{α β : Type} (p : α × β)`.

| Before | After |
|---|---|
| `p : α × β ⊢ (p.fst, p.snd) = p` | no goals |

**R3 · `unfold D`** changes the **goal**: every occurrence of the defined name `D` is replaced by its body.
Placeholders: `{α β γ : Type} (f : α → γ) (p : α × β) (P : γ × β → Prop)`, `D := mapFst`.

| Before | After |
|---|---|
| `⊢ P (mapFst f p)` | `⊢ P (f p.fst, p.snd)` |

**W1:** `mapFst id p = p` by `unfold mapFst` (R3), then `rfl` (R2; it also unfolds `id`):

```lean-goal
⊢ (id p.fst, p.snd) = p
```

**W4:** `mapFst (fun x => x) p = p` by `unfold mapFst` (R3), then `dsimp only` (R1), which reduces
`(fun x => x) p.fst` to `p.fst` and closes the eta goal `(p.fst, p.snd) = p` by itself. The state after R3:

```lean-goal
⊢ ((fun x => x) p.fst, p.snd) = p
```

## Part 2 · `pair_ext`

Statement: two pairs of naturals with equal first components and equal second components are equal. This is
the extensionality principle for `×`, and the library already has it.

**R4 · `apply Prod.ext`** changes the **goal list**: one equation of pairs becomes one equation per
component. The lemma is `Prod.ext : x.fst = y.fst → x.snd = y.snd → x = y`, with `{α β : Type} {x y : α × β}`
implicit (Lean infers them from the goal). As a term, `Prod.ext h₁ h₂` with `h₁ : x.fst = y.fst`,
`h₂ : x.snd = y.snd` proves `x = y` directly (W3). Placeholders: `{α β : Type} (a : α) (b : β) (p : α × β)`;
the right side `(a, b)` shows that each new goal may still contain a projection of a literal pair, which
`exact` sees through (R1).

| Before | After |
|---|---|
| `⊢ p = (a, b)` | `⊢ p.fst = (a, b).fst`, `⊢ p.snd = (a, b).snd` |

## Part 3 · `addPair_swap`

Statement: `addPair (swap p) = addPair p` for `p : Nat × Nat`: adding the components does not depend on their
order. `addPair` is a pattern-matching lambda, so with `p` a variable neither side reduces. Split `p` first
(R5): the goal becomes `addPair (swap (a, b)) = addPair (a, b)`. Now everything computes: unfolding (R3) and
reducing (R1, R6) give `b + a = a + b`, which is `Nat.add_comm b a` (R7). `exact` sees through the unfolding,
so R3, R6 may be skipped.

**R5 · `obtain ⟨a, b⟩ := p`** changes the **context** and the **goal**: `p : α × β` is replaced by its
components `a : α`, `b : β`, and every `p` in the goal by `(a, b)`. It is the same `obtain` as for `∧` and `∃`,
because `×` is a structure with two fields. Placeholders: `{α β : Type} (p : α × β) (P : α × β → Prop)`.

| Before | After |
|---|---|
| `p : α × β ⊢ P p` | `a : α, b : β ⊢ P (a, b)` |

**R6 · `dsimp only`** changes the **goal**: a `match` on a literal pair reduces to its branch with the
components substituted. A definition `D := fun (a, b) => …` unfolds (R3) to such a `match`. Placeholders:
`(x y : Nat) (P : Nat → Prop)`, `D := mulPair`. The three states, before `unfold`, after it, after `dsimp only`:

```lean-goal
⊢ P (mulPair (x, y))
⊢ P (match (x, y) with | (a, b) => a * b)
⊢ P (x * y)
```

**R7 · `Nat.add_comm`** **closes** the goal with `exact Nat.add_comm a b`. The lemma is
`Nat.add_comm : ∀ (n m : Nat), n + m = m + n`; the arguments choose which sum is on the left. Placeholders:
`(a b : Nat)`.

| Before | After |
|---|---|
| `a b : Nat ⊢ a + b = b + a` | no goals |

**W2: the full route** on `mulPair p = mulPair (p.2, p.1)`: `obtain ⟨a, b⟩ := p` (R5), `unfold mulPair` (R3),
`dsimp only` (R1, R6), `exact Nat.mul_comm a b` (`Nat.mul_comm : ∀ (n m : Nat), n * m = m * n`):

```lean-goal
⊢ mulPair (a, b) = mulPair ((a, b).snd, (a, b).fst)
⊢ (match (a, b) with | (a, b) => a * b) = match ((a, b).snd, (a, b).fst) with | (a, b) => a * b
⊢ a * b = b * a
```

---

## Traps

- A pattern lambda on a **variable** pair is stuck: `addPair p` does not reduce, so `rfl`, `dsimp` and
  `Nat.add_comm` all fail before `obtain ⟨a, b⟩ := p`. Split the pair first.
- `dsimp only` closes a goal outright when, after reducing, both sides agree (eta included). Then a following
  `rfl` fails with "no goals": check the infoview before adding a closing step.
- After `obtain ⟨a, b⟩ := p`, the name `p` is gone. Lemmas must now mention `a` and `b`.
- `Nat.add_comm b a : b + a = a + b`, `Nat.add_comm a b : a + b = b + a`: the order of the arguments is the
  order on the **left** side. Check which side of your goal has `b` first.
- `apply Prod.ext` leaves two goals; close both (`exact h1`, then `exact h2`), or give the term
  `Prod.ext h1 h2` at once.
- `p.1` and `p.fst` are the same; the infoview only ever shows `.fst`/`.snd`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `(a, b).1 → a`, `(a, b).2 → b` | `dsimp only` | R1 |
| `(p.1, p.2) = p`, or anything that computes to it | `rfl` | R2 |
| see what a definition builds | `unfold swap` | R3 |
| equal pairs from equal components | `apply Prod.ext` / `exact Prod.ext h1 h2` | R4 |
| split a pair variable | `obtain ⟨a, b⟩ := p` | R5 |
| reduce a pattern lambda on `(a, b)` | `unfold addPair` then `dsimp only` | R3, R6 |
| `b + a = a + b` | `exact Nat.add_comm b a` | R7 |
| see the state | infoview | |
