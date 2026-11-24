# E029 · Constructor injectivity: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics up to E028, in particular `intro`/`exact`/`apply` (E003), anonymous constructors
`⟨_, _⟩` (E004), `∧` (E005), `¬` and `False` (E008), `simp at h` (E010), lists and `::` (E015), and
`inductive` types with constructors (E018).
**New here:** the two facts every `inductive` type comes with. (1) Constructors are **injective**: if
`C x₁ … xₙ = C y₁ … yₙ` for the same constructor `C`, then `xᵢ = yᵢ` for every `i` (`injection`).
(2) Different constructors are **disjoint**: `C₁ … = C₂ …` is never provable (`nomatch`, `nofun`).
Lean derives both from an auto-generated function `T.noConfusion`; you never call it directly here.

## How to read an entry

Each entry is one tactic, one term or one fact. It says what changes (**goal**, **context**, or **goal
list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `G : Prop` is any goal, when the step does not look at it. A hypothesis `k` only finishes the example.
- "no goals" means the tactic closed the goal.
- The guide's own type is `inductive T (α : Type) | leaf | one (a : α) | two (a b : α)`: a constructor with
  no, one and two arguments. In the exercise, `Shape.circle` (one argument) and `Shape.rect` (two) play
  the roles of `T.one` and `T.two`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Shape.circle a = Shape.circle b` | two shapes built by the same constructor are equal |
| `Shape.circle r ≠ Shape.rect w h` | `¬(Shape.circle r = Shape.rect w h)`, i.e. `Shape.circle r = Shape.rect w h → False` |
| `x :: xs` | `List.cons x xs`: the list with head `x` and tail `xs`; `::` is a constructor |
| `a_eq✝ : a = b` | a hypothesis with an inaccessible name (the `✝`): it is there, but you cannot type its name. `injection h` without `with` names it after the constructor's argument: `r_eq✝` for `Shape.circle (r : Nat)`, `head_eq✝`, `tail_eq✝` for `List.cons` |
| `h✝ : Nat` | a variable shadowed by a newer one with the same name: after `intro h` in `circle_ne_rect`, the argument `h : Nat` is shown as `h✝` |
| `h1 : a = c` | the hypothesis you named with `injection h with h1 …` |
| `⊢ False` | after `intro h` on a `≠` goal: derive a contradiction from `h` |

---

## Part 1 · `circle_inj`

Statement: from `h : Shape.circle a = Shape.circle b`, conclude `a = b`. Same constructor on both sides,
one argument: `injection` (R1) produces exactly the goal and closes it.

**R1 · `injection h`** changes the **context**, and may **close** the goal. `h` must be an equation between
two applications of the same constructor; `injection` adds one equation per argument, with inaccessible
names (`a_eq✝`). Then it runs `assumption` (close the goal with a hypothesis that states it exactly,
inaccessible ones included): if the goal is one of the new equations, it closes. Placeholders:
`{α : Type} (a b : α) (G : Prop)`.

| Before | After `injection h` | After `apply k` |
|---|---|---|
| `h : T.one a = T.one b ⊢ G` | `a_eq✝ : a = b ⊢ G` | `a_eq✝ : a = b ⊢ a = b` |

The last state is closed by `assumption`. **W1** shows `injection h` alone closing
`h : some a = some b ⊢ a = b` (`some` is a constructor of `Option`):

```lean-goal
⊢ a = b
```

## Part 2 · `rect_inj`

Statement: from `h : Shape.rect a b = Shape.rect c d`, conclude `a = c ∧ b = d`. Same constructor, two
arguments: name the two argument equations (R2) and pair them (R3).

**R2 · `injection h with h1 h2`** changes the **context**: it adds one equation per constructor argument,
named left to right by the `with` list. Here the goal (`G`) is not one of them, so it stays open.
Placeholders: `{α : Type} (a b c d : α) (G : Prop)`.

| Before | After |
|---|---|
| `h : T.two a b = T.two c d ⊢ G` | `h1 : a = c, h2 : b = d ⊢ G` |

**R3 · `exact ⟨h1, h2⟩`** **closes** `A ∧ B` (anonymous constructor, E004). Placeholders: `(A B : Prop)
(h1 : A) (h2 : B)`.

| Before | After |
|---|---|
| `h1 : A, h2 : B ⊢ A ∧ B` | no goals |

**W2** (R2, R3 on a pair): `(a, b)` is `Prod.mk a b`, a constructor application. The order of the
conjuncts is up to you; the order of the names in `with` follows the constructor's arguments:

| Step | State |
|---|---|
| start (`h : (a, b) = (c, d)`) | `⊢ b = d ∧ a = c` |
| `injection h with h1 h2` | `h1 : a = c, h2 : b = d ⊢ b = d ∧ a = c` |
| `exact ⟨h2, h1⟩` | no goals |

**R8 · `simp at h`** (another route for Parts 1, 2, 4) changes the **context**: Lean generates, for every
constructor, a `simp` lemma such as `T.two.injEq : (T.two a b = T.two a' b') = (a = a' ∧ b = b')`, so the
equation in `h` becomes the conjunction of the argument equations. Placeholders:
`{α : Type} (a b c d : α) (G : Prop)`.

| Before | After |
|---|---|
| `h : T.two a b = T.two c d ⊢ G` | `h : a = c ∧ b = d ⊢ G` |

## Part 3 · `circle_ne_rect`

Statement: `Shape.circle r ≠ Shape.rect w h`. Different constructors: the equation has no proof. Either
introduce it (R4) and refute it (R5), or write the whole proof as one term (R6).

**R4 · `intro h`** on `x ≠ y` changes the **goal and the context**: `x ≠ y` is `¬(x = y)`, which is
`x = y → False`, so `intro` applies. Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `⊢ T.leaf ≠ T.two a b` | `h : T.leaf = T.two a b ⊢ False` |

**R5 · `nomatch h`** **closes** any goal when `h` equates two different constructors. It is a `match` on
`h` with zero arms: Lean checks that no case is possible. Placeholders: `{α : Type} (a b : α) (G : Prop)`.

| Before | After |
|---|---|
| `h : T.leaf = T.two a b ⊢ G` | no goals |

**R6 · `nofun`** is a **term** that **closes** `x ≠ y` (or `x = y → False`) when `x`, `y` start with
different constructors. It is `fun h => nomatch h`: a function with no arms, accepted because no argument
`h` exists. In term mode write `:= nofun`; in tactic mode `exact nofun`. Placeholders: `{α : Type} (a : α)`.

| Before | After |
|---|---|
| `⊢ T.leaf ≠ T.one a` | no goals |

**W3** (R4, R5 on `Option`): `intro h` then `nomatch h` closes `none ≠ some n`; `nofun` alone closes
`[] ≠ x :: xs`.

| Step | State |
|---|---|
| start | `⊢ none ≠ some n` |
| `intro h` | `h : none = some n ⊢ False` |
| `nomatch h` | no goals |

## Part 4 · `cons_inj_head`

Statement: from `h : x :: xs = y :: ys`, conclude `x = y ∧ xs = ys`. `::` is the constructor `List.cons`
with two arguments (head, tail), so this is Part 2 again (R7, then R2, R3).

**R7 · `::` is a constructor** (`List.cons`): `injection h with e1 e2` on `h : a :: l = b :: m` changes the
**context**, giving the head equation and the tail equation. `[]` is the other constructor `List.nil`, so
`nofun` refutes `[] = x :: xs` (W3). Placeholders: `{α : Type} (a b : α) (l m : List α) (G : Prop)`.

| Before | After |
|---|---|
| `h : a :: l = b :: m ⊢ G` | `e1 : a = b, e2 : l = m ⊢ G` |

**W4** (R2 then R1, nested constructors): one `injection` peels one constructor layer.

| Step | State |
|---|---|
| start | `h : T.one (T.one a) = T.one (T.one b) ⊢ a = b` |
| `injection h with h1` | `h1 : T.one a = T.one b ⊢ a = b` |
| `injection h1` | no goals |

---

## Traps

- `injection h` works only when both sides of `h` start with a constructor. On `h : f a = f b` for a
  function `f`, it fails: functions need not be injective.
- Without `with`, the new equations are inaccessible (`a_eq✝`). If the goal is not exactly one of them,
  you cannot refer to them; write `injection h with h1 h2` instead.
- `injection h with h1 h2` names the equations in the order of the constructor's arguments, not in the
  order of the goal's conjuncts.
- `nofun` is a term. As a tactic write `exact nofun`; after `:=` write `nofun` alone.
- `≠` hides an implication: `intro h` works on `x ≠ y`, and the goal becomes `False`.
- `injection h with q` also runs `assumption`: when the goal is exactly `q`'s equation (as in `circle_inj`),
  the goal is already closed, and a following `exact q` fails with "No goals to be solved".
- In `circle_ne_rect` the arguments are `(r w h : Nat)`, so `intro h` shadows the `Nat` called `h` (it becomes
  `h✝`). It still works, but `intro e; nomatch e` keeps the state readable.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| from `h : C a = C b` get goal `a = b` (one argument) | `injection h` | R1 |
| name the argument equations | `injection h with h1 h2` | R2 |
| pair two facts into `A ∧ B` | `exact ⟨h1, h2⟩` | R3 |
| open a `≠` goal | `intro h` (goal becomes `False`) | R4 |
| `h : C₁ … = C₂ …` (different constructors) | `nomatch h` | R5 |
| `C₁ … ≠ C₂ …` in one term | `nofun` | R6 |
| lists: `x :: xs = y :: ys` | same as R2 (`::` is `List.cons`) | R7 |
| constructor equation → argument equations in `h` | `simp at h` | R8 |
| see the state | infoview | |
