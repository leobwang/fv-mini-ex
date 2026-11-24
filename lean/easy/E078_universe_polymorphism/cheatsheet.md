# E078 · Universe polymorphism: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `def`, `rfl`, `unfold`, `exact`, pairs
`α × β`, and `Prop` versus `Type`. **New here:** universe variables (`universe u`), the hierarchy
`Prop = Sort 0`, `Type u = Sort (u + 1)`, `Type u : Type (u + 1)`, definitions that are polymorphic over
universes, how Lean picks the levels when such a definition is applied to *types*, and why `rfl` proves
statements about pairs (projections compute, structure eta). No Mathlib.

## How to read an entry

Each entry is one tactic, one piece of syntax, or one universe fact. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal.
- `{α : Type u}` is any type at universe level `u`; `{α : Sort u}` is any type at level `u` *or* any
  proposition (R5).
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

The guide's own functions: `idS a = a` (over `Sort u`), `swapU p = (p.2, p.1)` and `dup a = (a, a)` (over
`Type u`). None is the exercise's.

## The universe hierarchy

Every type has a type, its **universe**. Lean's universes are `Sort 0, Sort 1, Sort 2, …`, indexed by a
**universe level** (`0`, `1`, `u`, `u + 1`, `max u v`):

| Universe | Other name | Holds | And itself lives in |
|---|---|---|---|
| `Sort 0` | `Prop` | propositions: `1 = 1`, `∀ n, n + 0 = n` | `Sort 1` |
| `Sort 1` | `Type` = `Type 0` | data types: `Nat`, `Bool`, `List Nat`, `Nat × Nat` | `Sort 2` |
| `Sort 2` | `Type 1` | `Type` itself, `Type × Nat`, `Type → Type` (e.g. `List`) | `Sort 3` |
| `Sort (u + 1)` | `Type u` | | `Type (u + 1)` |

`Type : Type` would be inconsistent (Girard's paradox), so a definition written for `{α : Type}` cannot be
applied to `Type` or `List`. Writing `{α : Type u}` with a universe variable `u` (declared by
`universe u`) makes one definition available at every level; Lean chooses `u` at each use (R13).

## Reading the goals

| You see | It means |
|---|---|
| `α : Type u` | `α` is a type at universe level `u` (a universe variable) |
| `α : Sort u` | `α` is a proposition when `u = 0`, otherwise a type in `Type (u - 1)` |
| `α × β` | pairs `(a, b)` with `a : α`, `b : β`; it lives in `Type (max u v)` |
| `p.fst`, `p.snd` | the projections `p.1`, `p.2` (Lean prints the long names) |
| `(a, b).fst` | the first projection of a literal pair; it computes to `a` (R7) |
| `id a` | the identity function applied to `a`; computes to `a` (R8) |
| `g ∘ f` | `Function.comp g f`, the function `fun x => g (f x)` (R11) |
| `idS.{2}`, `Prod.mk.{1, 1}` | the universe levels Lean chose, shown with `set_option pp.universes true in` |
| `Eq.{2} a b` | `a = b` between terms of a type that lives in `Sort 2 = Type 1` |
| `_b` in a binder | an argument the body ignores; the `_` prefix silences the unused-variable warning |

---

## Part 1 · `mapFst`

Statement: write the body of `mapFst f p : γ × β`, which applies `f : α → γ` to the first component of
`p : α × β` and keeps the second. The three types live at three independent levels `u`, `v`, `w`; the
body does not mention them. (If you write the body as `by …`, the infoview shows the binders as context
and `γ × β` as the goal.)

**R1 · `universe u v` and `{α : Type u}`** changes the **context**: the binders appear with their
universes. `universe u v` must come before the first use of `u`, `v` (the exercise declares
`universe u v w` inside its first spec region). Placeholders: `{α : Type u} {β : Type v} (a : α) (b : β)`.

| Before | After |
|---|---|
| `a : α, b : β ⊢ P a b` | no goals (after `exact h`) |

**R2 · `(x, y)`** **closes** a goal `α × β`: `(x, y)` is notation for `Prod.mk x y`. Placeholders:
`{α : Type u} {β : Type v} (a : α) (b : β)`.

| Before | After |
|---|---|
| `a : α, b : β ⊢ α × β` | no goals |

**R3 · `p.1`, `p.2`** **close** a goal `α` or `β`: the projections `Prod.fst p : α`, `Prod.snd p : β`.
Placeholders: `{α : Type u} {β : Type v} (p : α × β)`.

| Before | After |
|---|---|
| `p : α × β ⊢ β` | no goals |

**R4 · `f a`** **closes** a goal `γ`: apply `f : α → γ` to any term `a : α`, a projection included.
Placeholders: `{α γ : Type u} (f : α → γ) (a : α)`.

| Before | After |
|---|---|
| `f : α → γ, a : α ⊢ γ` | no goals |

---

## Part 2 · `pick`

Statement: write the body of `pick a _b : α`, which returns its first argument. Its binder is
`{α : Sort u}`, so `pick` works on proofs as well as on data and on types (Part 6).

**R5 · `{α : Sort u}`** changes the **context**: `α` may be a proposition (`Sort 0`) or a type at any
level. The guide's `idS {α : Sort u} (a : α) : α` is used at a proof (`u := 0`) and at the type `Nat`
(`α := Type = Sort 1`, which lives in `Sort 2`, so `u := 2`). Placeholders: `(p : Prop) (hp : p)`.

| Before | After |
|---|---|
| `hp : p ⊢ p` | no goals (after `exact idS hp`) |
| `⊢ Eq.{2} (idS.{2} Nat) Nat` | no goals (after `rfl`) |

---

## Part 3 · `mapFst_id`

Statement: `mapFst id p = p`. Mapping the identity over the first component gives the pair back. It holds
by the definitions: unfold `mapFst`, compute `id`, and the result is `p` rebuilt from its projections,
which is `p` by eta. `rfl` (R10) does all of that in one step; R6–R9 show the steps.

**R6 · `unfold f`** changes the **goal**: `f x` is replaced by the body of `f`, with the arguments
substituted. Placeholders: `{α : Type u} {β : Type v} (p : α × β)`.

| Before | After |
|---|---|
| `p : α × β ⊢ P (swapU p)` | `p : α × β ⊢ P (p.snd, p.fst)` |

**R7 · `dsimp only`** changes the **goal**: projections of literal pairs compute, `(a, b).1` → `a`,
`(a, b).2` → `b`. It uses no lemmas, only computation, and it closes the goal if both sides of an equation become equal by definition (Traps). Placeholders: `{α : Type u} {β : Type v} (a : α) (b : β)`.

| Before | After |
|---|---|
| `⊢ P (a, b).fst` | `⊢ P a` |

**R8 · `dsimp only [id]`** changes the **goal**: `id a` → `a`. Placeholders: `{α : Type u} (a : α)`.

| Before | After |
|---|---|
| `⊢ P (id a)` | `⊢ P a` |

**R9 · `rfl`** **closes** `(p.1, p.2) = p`. This is *structure eta*: Lean treats any structure value and
the value rebuilt from its fields as the same term, so no case split on `p` is needed. Placeholders:
`{α : Type u} {β : Type v} (p : α × β)`.

| Before | After |
|---|---|
| `⊢ (p.fst, p.snd) = p` | no goals |

**R10 · `rfl`** **closes** an equation whose two sides become the same term after unfolding definitions
and computing. It does R6–R9 and R11 by itself. Placeholders: `{α : Type u} {β : Type v} (a : α) (b : β)`.

| Before | After |
|---|---|
| `⊢ swapU (a, b) = (b, a)` | no goals |

**W1 (on `swapU`):** `swapU (swapU p) = p` by R6, then `rfl` (projections and eta); `rfl` alone also works.

```lean-goal
⊢ swapU (swapU p) = p
⊢ ((p.snd, p.fst).snd, (p.snd, p.fst).fst) = p
```

---

## Part 4 · `mapFst_comp`

Statement: `mapFst g (mapFst f p) = mapFst (g ∘ f) p`. Mapping `f` and then `g` equals mapping the
composite once. Both sides unfold to a pair with second component `p.2`; the first components are
`g (f p.1)` and `(g ∘ f) p.1`, which agree by the definition of `∘`. Again `rfl` (R10).

**R11 · `dsimp only [Function.comp]`** changes the **goal**: `(g ∘ f) x` → `g (f x)`. Placeholders:
`{α β γ : Type u} (f : α → β) (g : β → γ) (a : α)`.

| Before | After |
|---|---|
| `⊢ P ((g ∘ f) a)` | `⊢ P (g (f a))` |

Note that in `mapFst_comp` the types `γ δ : Type w` share one level, while `α : Type u`; `g ∘ f` composes
across levels without trouble.

---

## Part 5 · `mapFst_types`

Statement: `mapFst List (Nat, 3) = (List Nat, 3)`. Here the "first component" is the type `Nat`, and the
function is the type constructor `List : Type → Type`. So `α := Type`, `γ := Type`, `β := Nat`, and Lean
must choose `u := 1`, `w := 1`, `v := 0`. That is possible only because `mapFst` is universe-polymorphic.
Once the levels are chosen, the proof is `rfl` (R10), as in Part 3.

**R12 · `Type : Type 1`** **closes** a goal `Type 1` with any type of types. A pair type lives at the
larger of its two levels: `Type × Nat : Type 1`, because `Type : Type 1` and `Nat : Type 0`. So the pair
`(Nat, 3)` has type `Type × Nat`, which lives in `Type 1`.

| Before | After |
|---|---|
| `⊢ Type 1` | no goals (after `exact Type × Nat`, or `exact Type → Type`) |

**R13 · instantiating a universe** **closes** the goal with `rfl` once Lean has picked the levels. `dup`
is declared for `{α : Type u}`; applied to `Nat` it gets `α := Type`, hence `u := 1`, printed `dup.{1}`
(with `set_option pp.universes true in`).

| Before | After |
|---|---|
| `⊢ Eq.{2} (dup.{1} Nat) (Prod.mk.{1, 1} Nat Nat)` | no goals |

**W2 (on `swapU`, a pair of types):** `α := Type`, `β := Type`, so `u := 1`, `v := 1`:

```lean-goal
⊢ Eq.{2} (swapU.{1, 1} (Prod.mk.{1, 1} Nat Bool)) (Prod.mk.{1, 1} Bool Nat)
```

**W3 (type constructors are functions):** `Option : Type → Type` composed with `id`, closed by
`dsimp only [Function.comp, id]` (R8, R11):

```lean-goal
⊢ (Option ∘ id) Nat = Option Nat
```

---

## Part 6 · `pick_type`

Statement: `pick Nat Bool = Nat`. Both arguments are types, so `α := Type`, which lives in `Sort 2`:
`pick` is used at `u := 2` (R5, compare `idS.{2}`). Then `rfl` (R10).

---

## Traps

- With `{α : Type}` in place of `{α : Sort u}` (or `{α : Type u}`), `idS Nat` and `pick Nat Bool` fail: they
  need `α := Type`, and `Type : Type 1`, not `Type`. The error is a universe-level mismatch, not a type
  error in the body.
- `Type u` is never `Prop`: a definition over `{α : Type u}` cannot take a proof. Use `Sort u` to cover
  both (R5).
- `universe u` must come before `u` is used. The exercise already declares `universe u v w` in its first
  spec region; do not declare them again.
- `p.1` and `p.fst` are the same term; you may type either, and the infoview prints `p.fst`.
- `mapFst_id` needs no `cases p`: `rfl` uses structure eta (R9).
- `dsimp` closes the goal by itself when, after its rewriting, the two sides are equal by definition
  (eta included). Writing out `mapFst_id` as `unfold mapFst` then `dsimp only [id]` leaves no goals, so a
  further `rfl` fails with "No goals to be solved". The same holds for `dsimp only [Function.comp]` in
  `mapFst_comp`.
- The holes come right after `:=`, so they expect a term: write `rfl` (a term) or `by` followed by
  tactics (`by rfl`). A tactic such as `unfold` without `by` is a parse error.
- You never write a level yourself: Lean infers `u`, `v`, `w` at each use of `mapFst` and `pick`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| a type at any level | `universe u` then `{α : Type u}` | R1 |
| a type, *or* a proposition | `{α : Sort u}` | R5 |
| build a pair | `(x, y)` | R2 |
| take a pair apart | `p.1`, `p.2` | R3 |
| apply a function | `f a` | R4 |
| replace a function by its body | `unfold f` | R6 |
| compute `(a, b).1`, `id a`, `(g ∘ f) a` | `dsimp only`, `dsimp only [id]`, `dsimp only [Function.comp]` | R7, R8, R11 |
| `(p.1, p.2) = p` | `rfl` (structure eta) | R9 |
| an equation that holds by the definitions | `rfl` | R10 |
| where a type lives | `Type : Type 1`, `α × β : Type (max u v)` | R12 |
| see the levels Lean chose | `set_option pp.universes true in` before the declaration | R13 |
| see the state | infoview | |
