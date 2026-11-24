# E030 · Prop-valued definitions: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics up to E029, in particular `intro`/`exact` (E003), anonymous constructors
`⟨_, _⟩` (E004), `rcases` on `∨` (E006), `∃` and `obtain` (E007), `rw` (E009), `unfold` (E012), `show`
(E021) and bounded quantifiers `∀ x ∈ xs, …` (E025).
**New here:** predicates defined with `def D (args) : Prop := body`. Such a `D` is a function into `Prop`:
`D a b` is a proposition that *means* its body with `a, b` plugged in, and Lean treats the two as equal
by definition (*definitionally equal*: equal after unfolding names). Two kinds of tactics meet such a goal
or hypothesis:

- **See through definitions on their own:** the anonymous constructor `⟨_, _⟩`, `obtain`/`rcases`
  patterns, `intro`, `exact`, `show`. They unfold `D` as far as they need.
- **Work on the literal text:** `rw`, `simp`, `omega`. They see the name `D a b`, not its body; `unfold D`
  (or `show`) first.

## How to read an entry

Each entry is one tactic, one term or one lemma used with `rw`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- `G : Prop` is any goal, when the step does not look at it. A hypothesis `k` only finishes the example.
- "no goals" means the step closed the goal.
- The guide's own predicates, standing in for the exercise's:

  | Guide | Body | Shape it shares with |
  |---|---|---|
  | `SomeP p` | `∃ x, p x` | any defined `∃` |
  | `Image f y` | `∃ x, y = f x` | a defined `∃` whose body is an equation `y = …` (`Divides`) |
  | `AllIn p xs` | `∀ x ∈ xs, p x` | a defined bounded `∀` (`UpperBound`) |

- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that. A
  hypothesis whose statement contains a comma (`h : ∀ (x : α), …`, `h : ∃ k, …`) is shown in its own
  code span next to the state.

## Reading the goals

| You see | It means |
|---|---|
| `Divides n n`, `UpperBound b xs` | a defined proposition: the name, not yet unfolded |
| `∃ k, n = d * k` | there is a `k : Nat` with `n = d * k` (the body of `Divides d n`) |
| `∀ (x : Nat), x ∈ xs → x ≤ b` | how the infoview prints `∀ x ∈ xs, x ≤ b` after unfolding |
| `x_1` | a bound variable renamed because `x` is already in the context (`∀ (x_1 : Nat), x_1 ∈ x :: xs → …`) |
| `x :: xs` | the list with head `x` and tail `xs` (`List.cons x xs`) |
| `a * b * c` | `(a * b) * c`: `*` groups to the left |
| `case inl`, `case inr` | the two goals after `rcases` on an `∨` (E006): left side holds, right side holds |
| `h.symm` | the equation `h : a = b` turned around, `b = a` |

---

## Part 1 · `divides_refl`

Statement: `Divides n n`, i.e. `∃ k, n = n * k`. The witness is `k = 1`, and the equation `n = n * 1` is
`Nat.mul_one n` turned around. The anonymous constructor sees through `Divides` (R3), so the whole proof
can be one term. R1 and R2 only show you the body.

**R1 · `unfold D`** changes the **goal**: the name is replaced by its body. Placeholders:
`{α : Type} (p : α → Prop)`.

| Before | After |
|---|---|
| `⊢ SomeP p` | `⊢ ∃ x, p x` |

**R2 · `show T`** changes the **goal** to `T`, which must be definitionally equal to it (Lean checks by
unfolding). Same placeholders as R1. Unlike `unfold`, you write the new goal yourself.

| Before | After |
|---|---|
| `⊢ SomeP p` | `⊢ ∃ x, p x` |

**R3 · `exact ⟨w, hw⟩`** **closes** a goal `D …` whose body is `∃ x, q x`, given a witness `w` and
`hw : q w`. No `unfold` needed. In term mode write `:= ⟨w, hw⟩`. Placeholders:
`{α : Type} (p : α → Prop) (w : α) (hw : p w)`.

| Before | After |
|---|---|
| `⊢ SomeP p` | no goals |

**R4 · `Nat.mul_one`** changes the **goal** with `rw`. The lemma is `Nat.mul_one (n : Nat) : n * 1 = n`.
Placeholders: `(a : Nat)`.

| Before | After |
|---|---|
| `⊢ P (a * 1)` | `⊢ P a` |

**R5 · `h.symm`** (`Eq.symm`) is a **term**: from `h : a = b` it gives `b = a`, and **closes** that goal.
For a lemma, put the application in parentheses: `(Nat.mul_one a).symm : a = a * 1`. Placeholders:
`{α : Type} (a b : α) (h : a = b)`.

| Before | After |
|---|---|
| `h : a = b ⊢ b = a` | no goals |

**W1** (R3): `exact ⟨3, rfl⟩` closes `Even2 6`, where `Even2 n := ∃ k, n = k + k`; `rfl` proves
`6 = 3 + 3` by computation.

| Before | After |
|---|---|
| `⊢ Even2 6` | no goals |

## Part 2 · `divides_trans`

Statement: from `h1 : Divides a b` and `h2 : Divides b c`, prove `Divides a c`. Unpack both witnesses with
the `rfl` pattern (R7): `b` becomes `a * k`, then `c` becomes `a * k * m`. The goal is then
`Divides a (a * k * m)`, i.e. `∃ j, a * k * m = a * j`: witness `k * m` (R3), equation by associativity (R8).

**R6 · `obtain ⟨x, hx⟩ := h`** changes the **context**: `h : D …` with body `∃ x, q x` is replaced by a
witness `x` and `hx : q x`. `obtain` sees through `D`. Placeholders: `{α : Type} (p : α → Prop) (G : Prop)`.

| Before | After |
|---|---|
| `h : SomeP p ⊢ G` | `x : α, hx : p x ⊢ G` |

**R7 · `obtain ⟨x, rfl⟩ := h`** changes the **context and the goal**: when the body is `∃ x, y = f x` and
`y` is a local variable, the pattern `rfl` substitutes `y := f x`. `y` leaves the context, and every
hypothesis and the goal that mentioned `y` now mention `f x`. Placeholders:
`{α β : Type} (f : α → β) (y : β) (P : β → Prop)`.

| Before | After |
|---|---|
| `y : β, h : Image f y ⊢ P y` | `x : α ⊢ P (f x)` |

**W2** (R7, then R3 with `by omega` for the equation):

| Step | State |
|---|---|
| start | `h : Even2 n ⊢ Even2 (n + 2)` |
| `obtain ⟨k, rfl⟩ := h` | `k : Nat ⊢ Even2 (k + k + 2)` |
| `exact ⟨k + 1, by omega⟩` | no goals |

**R8 · `Nat.mul_assoc`** changes the **goal** with `rw`. The lemma is
`Nat.mul_assoc (a b c : Nat) : a * b * c = a * (b * c)`. As a term, `Nat.mul_assoc a b c` is that
equation for the given numbers, so it can be the second component of an anonymous constructor.
Placeholders: `(a b c : Nat)`.

| Before | After |
|---|---|
| `⊢ P (a * b * c)` | `⊢ P (a * (b * c))` |

## Part 3 · `upperBound_cons`

Statement: from `hx : x ≤ b` and `h : UpperBound b xs`, prove `UpperBound b (x :: xs)`. Unfold everywhere
(R9), introduce an element `y` with `hy : y ∈ x :: xs` (R10), turn `hy` into `y = x ∨ y ∈ xs` (R11), split
it (R12): the first case is `hx`, the second is `h` applied to `y` (R13).

**R9 · `unfold D at *`** changes the **context and the goal**: every occurrence of `D …` becomes its body.
`unfold D at h` does the hypothesis `h` only. Placeholders: `{α : Type} (p : α → Prop) (xs ys : List α)`.

| Before | After |
|---|---|
| `h : AllIn p xs ⊢ AllIn p ys` | `h : ∀ (x : α), x ∈ xs → p x` and `⊢ ∀ (x : α), x ∈ ys → p x` |

**R10 · `intro y hy`** changes the **goal and the context**: `∀ x ∈ xs, Q x` is `∀ x, x ∈ xs → Q x`, two
binders, so `intro` takes two names. `intro` sees through definitions, so it works even before R9.
Placeholders: `{α : Type} (p : α → Prop) (xs : List α)`.

| Before | After |
|---|---|
| `⊢ ∀ (x : α), x ∈ xs → p x` | `y : α, hy : y ∈ xs ⊢ p y` |

**R11 · `rw [List.mem_cons] at hy`** changes the **context**. The lemma is
`List.mem_cons : a ∈ b :: l ↔ a = b ∨ a ∈ l`; `rw` with an `↔` replaces one proposition by the other.
Placeholders: `{α : Type} (a b : α) (l : List α) (G : Prop)`.

| Before | After |
|---|---|
| `hy : a ∈ b :: l ⊢ G` | `hy : a = b ∨ a ∈ l ⊢ G` |

**R12 · `rcases hy with rfl | hy`** changes the **goal list**: one goal per side of the `∨` (E006). On the
left side `a = b` the pattern `rfl` substitutes. With a local variable on both sides, Lean removes the
**right** one: `b` disappears and every `b` becomes `a`; hypothesis names stay. On the right side, the
hypothesis gets the name after `|`. Placeholders: `{α : Type} (a b : α) (l : List α) (P : α → Prop)`.

| Before | After |
|---|---|
| `hb : P b, hy : a = b ∨ a ∈ l ⊢ P a` | `hb : P a ⊢ P a` (case `inl`), `hb : P b, hy : a ∈ l ⊢ P a` (case `inr`) |

In the exercise `hy : y = x ∨ y ∈ xs`, so `x` is the one replaced, by `y`: `hx` keeps its name and now
states `y ≤ b`, which is the goal. Solve the two cases with `·` (TACTIC_STATES, "Structure").

**R13 · `h y hy`** is a **term**: a bounded `∀` is a function of two arguments, the element and the proof
of membership. From `h : ∀ x ∈ xs, Q x` and `hy : y ∈ xs` it gives `Q y`, and `exact h y hy` **closes**
that goal. Placeholders: `{α : Type} (p : α → Prop) (xs : List α) (y : α)`.

| Before | After |
|---|---|
| `h : ∀ (x : α), x ∈ xs → p x` and `hy : y ∈ xs ⊢ p y` | no goals |

**W3** (R9, R10, membership lemmas as in R11, R12 without `rfl`, R13) on
`Bounded a xs := ∀ x ∈ xs, a ≤ x` and an append instead of a cons:

| Step | State |
|---|---|
| start | `h : Bounded a xs ⊢ Bounded a (xs ++ [x])` |
| `unfold Bounded at *` | `h : ∀ (x : Nat), x ∈ xs → a ≤ x` and `⊢ ∀ (x_1 : Nat), x_1 ∈ xs ++ [x] → a ≤ x_1` |
| `intro y hy` | `y : Nat, hy : y ∈ xs ++ [x] ⊢ a ≤ y` |
| `rw [List.mem_append] at hy` | `hy : y ∈ xs ∨ y ∈ [x] ⊢ a ≤ y` |
| `rcases hy with hy \| hy` | `hy : y ∈ xs ⊢ a ≤ y` and `hy : y ∈ [x] ⊢ a ≤ y` |

The first case is `exact h y hy` (R13); the second uses `List.mem_singleton : a ∈ [b] ↔ a = b`.

---

## Traps

- `rw`, `simp` and `omega` work on the text of the goal, and the text is the name `UpperBound b xs`, not
  its body. `rw [List.mem_cons]` finds no `∈` there: `unfold` (R9) and `intro` (R10) first. **W4**: with
  `h : Even2 n`, `omega` needs both `unfold Even2 at h` and `obtain`, because it uses neither definitions
  nor `∃`:

  | Step | State |
  |---|---|
  | start | `h : Even2 n, h1 : n = 3 ⊢ False` |
  | `unfold Even2 at h` | `h : ∃ k, n = k + k` and `h1 : n = 3 ⊢ False` |
  | `obtain ⟨k, hk⟩ := h` | `k : Nat, hk : n = k + k ⊢ False` |

- The `rfl` pattern needs a local variable on one side. `obtain ⟨k, rfl⟩ := h` with `h : Divides 2 6`
  fails (`6 = 2 * k` has no variable to replace); use `⟨k, hk⟩` there.
- After `obtain ⟨k, rfl⟩ := h1`, `b` is gone: `h2 : Divides b c` now reads `h2 : Divides (a * k) c`.
- `rcases … with rfl | …` may remove the variable you expected to keep (R12). Refer to hypotheses by name
  (`exact hx`), not by what you think they say.
- `(Nat.mul_one n).symm` needs the parentheses; `Nat.mul_one n.symm` parses as `Nat.mul_one (n.symm)`.
- After unfolding, a bound `x` that clashes with a context `x` prints as `x_1`. It is the same statement.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| see the body of `D …` in the goal | `unfold D` / `show body` | R1, R2 |
| prove a defined `∃` | `exact ⟨w, hw⟩` or `:= ⟨w, hw⟩` | R3 |
| `n * 1 = n` | `Nat.mul_one n` | R4 |
| turn an equation around | `h.symm`, `(lemma args).symm` | R5 |
| unpack a defined `∃` | `obtain ⟨x, hx⟩ := h` | R6 |
| unpack and substitute `y = f x` | `obtain ⟨x, rfl⟩ := h` | R7 |
| `a * b * c = a * (b * c)` | `Nat.mul_assoc a b c` | R8 |
| unfold in goal and hypotheses | `unfold D at *` | R9 |
| open a bounded `∀` goal | `intro y hy` | R10 |
| `y ∈ x :: xs` → `y = x ∨ y ∈ xs` | `rw [List.mem_cons] at hy` | R11 |
| split the `∨`, substituting the equation | `rcases hy with rfl \| hy` | R12 |
| use a bounded `∀` hypothesis | `h y hy` | R13 |
| see the state | infoview | |
