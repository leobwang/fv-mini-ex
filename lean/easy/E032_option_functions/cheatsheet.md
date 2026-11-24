# E032 · Option-returning functions: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics up to E031, in particular `rfl` (E001), `match` (E002), `intro`/`exact` (E003),
anonymous constructors `⟨_, _⟩` (E004), `constructor` (E005), `rw` (E009), `simp [f]` and `simp at h`
(E010), `omega` (E011), `if-then-else` (E012), `by_cases` (E013), `Option` and its constructors (E016).
**New here:** writing a partial function with `Option` (`none` for failure, `some x` for success), the
pattern-matching lambda `fun | … => …` with a catch-all arm, deciding an `if` with `simp [h]`, simplifying
an `Option` equation in a hypothesis, and the library lemma `Nat.div_mul_le_self`.

## How to read an entry

Each entry is one tactic, one term or one lemma. It says what changes (**goal**, **context**, or **goal
list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal. `G : Prop` is any goal, when the step does not look at it.
- "no goals" means the tactic closed the goal.
- The guide's own functions are `safeSub a b := if a < b then none else some (a - b)` and
  `first? := fun | x :: _ => some x | _ => none`. In the exercise, `safeDiv` and `second` play their roles.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Option Nat` | a `Nat` that may be missing: either `none` or `some n` |
| `none` | "no result" (here: division by zero, or a list too short) |
| `some (a / b)` | "the result is `a / b`" |
| `if b = 0 then none else some (a / b)` | the `if` as you wrote it; `simp [hb]` picks a branch (R5, R6) |
| `(if b = 0 then … else …) = some q` | after unfolding `safeDiv` in `h`: the parentheses mark the whole `if` as the left side |
| `a / b * b` | `(a / b) * b`: `/` and `*` have equal precedence and group to the left |
| `b ≠ 0`, `¬b = 0` | the same proposition: `b ≠ 0` is notation for `¬(b = 0)` |
| `a / b` | `Nat` division, rounded down; `a / 0 = 0` |
| `a :: b :: rest` | the list whose first two elements are `a`, `b`, followed by the list `rest` |
| `[a]` | the one-element list `a :: []` |
| `inst✝ : Decidable c` | an unnamed instance: Lean can compute whether `c` holds (needed by `if c`) |
| `case pos`, `case neg` | after `by_cases hc : c`: the goal with `hc : c`, the goal with `hc : ¬c` (R7) |
| `case left`, `case right` | the two halves of an `∧` after `constructor` (R3) |

---

## Part 1 · `safeDiv` (definition body)

Statement: `safeDiv (a b : Nat) : Option Nat`. You write the body: `none` exactly when `b = 0`, otherwise
`some (a / b)` (that is what `safeDiv_spec` demands).

**R1 · `if c then none else some x`** is a **term**: an `Option α` value that is `none` when `c` holds and
`some x` otherwise. As a tactic, `exact if c then none else some x` **closes** a goal of type `Option α`; in a
`def` body you write the term itself after `:=`. Both branches must have type `Option α`: write `some x`
(a bare `x` is also accepted: Lean inserts the coercion `Nat → Option Nat`, which is `some`, so the definition is the same; writing `some` keeps it explicit). Placeholders: `{α : Type} (c : Prop) [Decidable c] (x : α)`. `[Decidable c]` means Lean can compute
the truth of `c`; `b = 0` and `a < b` on `Nat` meet it.

| Before | After |
|---|---|
| `x : α ⊢ Option α` | no goals |

## Part 2 · `second` (definition body)

Statement: `second : List Nat → Option Nat`. Note there is no named argument: the body is a function. It
must give `none` on `[]` and on `[a]`, and the second element `b` on `a :: b :: rest` (`second_spec`).

**R2 · `fun | pat₁ => e₁ | _ => e₂`** is a **term**: a function defined by pattern matching on its
argument, short for `fun l => match l with | pat₁ => e₁ | _ => e₂`. Arms are tried top to bottom and the
first fitting pattern wins, so the catch-all `_` goes **last**. A pattern can look several cells deep:
`x :: y :: rest` fits exactly the lists with at least two elements, and `_` names a part you ignore. As a
tactic, `exact fun | x :: _ => some x | _ => none` **closes** the goal. Placeholders: `{α : Type}`.

| Before | After |
|---|---|
| `α : Type ⊢ List α → Option α` | no goals |

## Part 3 · `safeDiv_spec`

Statement: `(b = 0 → safeDiv a b = none) ∧ (b ≠ 0 → safeDiv a b = some (a / b))`. Split the `∧` (R3); in each
half introduce the assumption (R4) and let `simp`, given the definition's name and the assumption, unfold
`safeDiv` and pick the branch (R5 in the first half, R6 in the second).

**R3 · `constructor`** on `A ∧ B` changes the **goal list**: one goal becomes `case left` and `case right`.
Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ B` | `⊢ A` (`case left`), `⊢ B` (`case right`) |

**R4 · `intro h`** changes the **goal and the context**: the premise of an implication moves into the
context as `h`. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A → B` | `h : A ⊢ B` |

**R5 · `simp [hc]` with `hc : c`** changes the **goal**: `simp` rewrites `c` to `True` using `hc`, then
`if True then x else y` to `x`. With `simp [D, hc]` it first unfolds the definition `D` (E010). When the goal
is an equation whose sides then agree, `simp` closes it. Placeholders:
`{α : Type} (c : Prop) [Decidable c] (x y : α) (P : α → Prop) (hc : c)`.

| Before | After |
|---|---|
| `hc : c ⊢ P (if c then x else y)` | `hc : c ⊢ P x` |

**R6 · `simp [hc]` with `hc : ¬c`** changes the **goal**: `c` becomes `False`, and the `if` takes the
`else` branch. `hc : n ≠ 0` counts, since `n ≠ 0` is `¬(n = 0)`. Placeholders:
`{α : Type} (n : Nat) (x y : α) (P : α → Prop) (hc : n ≠ 0)`.

| Before | After |
|---|---|
| `hc : n ≠ 0 ⊢ P (if n = 0 then x else y)` | `hc : n ≠ 0 ⊢ P y` |

**W1** (R4, then R5 with the definition's name): `intro h` and `simp [safeSub, h]` close
`a < b → safeSub a b = none`:

```lean-goal
⊢ a < b → safeSub a b = none
⊢ safeSub a b = none
```

## Part 4 · `safeDiv_bound`

Statement: from `h : safeDiv a b = some q`, conclude `q * b ≤ a`. The information is in the hypothesis, so
work on `h`: split on `b = 0` (R7), and in each case let `simp [safeDiv, hb] at h` unfold `safeDiv` and pick
the branch inside `h` (R5/R6, used `at h`). For `b = 0`, `h` becomes `none = some q`, which is impossible (R8:
the goal closes). For `b ≠ 0`, `h` becomes `some (a / b) = some q`, then `a / b = q` (R9). Turn the goal's
`q` back into `a / b` (R10) and finish with the library bound (R11).

**R7 · `by_cases hc : c`** changes the **goal list and the context**: two copies of the goal, `case pos` with
`hc : c` and `case neg` with `hc : ¬c`. Placeholders: `(c G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `hc : c ⊢ G` (`case pos`), `hc : ¬c ⊢ G` (`case neg`) |

**R8 · `simp at h` with `h : none = some q`** **closes** the goal: two different constructors of `Option`
are never equal, so `h` simplifies to `False`, and a false hypothesis proves anything. Placeholders:
`{α : Type} (q : α) (G : Prop)`.

| Before | After |
|---|---|
| `h : none = some q ⊢ G` | no goals |

**R9 · `simp at h` with `h : some a = some b`** changes the **context**: `some` is injective (lemma
`Option.some.injEq : (some a = some b) = (a = b)`, a `simp` lemma), so `h` becomes `a = b`. Placeholders:
`{α : Type} (a b : α) (G : Prop)`.

| Before | After |
|---|---|
| `h : some a = some b ⊢ G` | `h : a = b ⊢ G` |

**R10 · `rw [← h]` with `h : e = q`** changes the **goal**: `h` is used right to left, so every `q` becomes
`e`. Placeholders: `(e q : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `h : e = q ⊢ P q` | `h : e = q ⊢ P e` |

**R11 · `exact Nat.div_mul_le_self m n`** **closes** the goal. The lemma is
`Nat.div_mul_le_self : ∀ (m n : Nat), m / n * n ≤ m`: `/` rounds down, so multiplying back never overshoots
(also for `n = 0`, where `m / 0 = 0`). Placeholders: `(m n : Nat)`.

| Before | After |
|---|---|
| `m n : Nat ⊢ m / n * n ≤ m` | no goals |

**W2** (R7, then `simp [safeSub, hab] at h` in each case, then `omega`) on
`h : safeSub a b = some r ⊢ r + b = a`. In `case pos` the `simp` closes the goal (R5 + R8 at `h`); in
`case neg` it leaves `h : a - b = r` (R6 + R9 at `h`):

| Step | State |
|---|---|
| start | `h : safeSub a b = some r ⊢ r + b = a` |
| `by_cases hab : a < b`, `case pos` | `hab : a < b ⊢ r + b = a` |
| first `simp [safeSub, hab] at h` | closes `case pos`; `hab : ¬a < b ⊢ r + b = a` is left |
| second `simp [safeSub, hab] at h` | `h : a - b = r, hab : ¬a < b ⊢ r + b = a` |
| `omega` | no goals |

## Part 5 · `second_spec`

Statement: `second [] = none ∧ second [a] = none ∧ second (a :: b :: rest) = some b`. Three equations, each
about a list whose shape is known. Give all three at once with an anonymous constructor (R12); each one holds
by computation (R13).

**R12 · `exact ⟨ha, hb, hc⟩`** **closes** `A ∧ B ∧ C`: `∧` nests to the right, `A ∧ (B ∧ C)`, and
`⟨_, _, _⟩` fills all three parts. In term mode write the triple directly after `:=`. Placeholders:
`(A B C : Prop)`.

| Before | After |
|---|---|
| `ha : A, hb : B, hc : C ⊢ A ∧ B ∧ C` | no goals |

**R13 · `rfl`** **closes** `f l = v` when `f` is defined by pattern matching and the shape of `l` is known
(`[]`, `[x]`, `x :: xs`, `x :: y :: rest`): Lean selects the matching arm by computation, although the
elements are variables. Placeholders: `(x : Nat) (xs : List Nat)`.

| Before | After |
|---|---|
| `x : Nat, xs : List Nat ⊢ first? (x :: xs) = some x` | no goals |

**W3** (R12 with three R13s): `dropTwo? := fun | _ :: _ :: rest => some rest | _ => none`, and
`⟨rfl, rfl, rfl⟩` closes

```lean-goal
⊢ dropTwo? [] = none ∧ dropTwo? [x] = none ∧ dropTwo? (x :: y :: rest) = some rest
```

---

## Traps

- `if b = 0 then none else a / b` (no `some`) is accepted, but only because Lean silently inserts the
  coercion `Nat → Option Nat`, which it unfolds to `some` (the goals then show `some (a / b)` anyway). Do not
  rely on it: write `some (a / b)` yourself, since the coercion is not inserted in every position.
- In a pattern-matching function, a catch-all `| _ => none` placed **first** catches every list, and Lean
  reports the later arms as redundant. Put the specific pattern (`_ :: y :: _`) first.
- `second` has no named argument (`second : List Nat → Option Nat :=`), so its body is a function: `fun | …`,
  not `match l with` (there is no `l`).
- `simp [safeDiv]` alone stops at the `if`: give it the case hypothesis too, `simp [safeDiv, hb]`.
- In `case pos` of `safeDiv_bound`, `simp [safeDiv, hb] at h` **closes** the goal (R8). A further tactic in
  that case then fails with "no goals".
- `rw [h]` with `h : a / b = q` would look for `a / b` in the goal `q * b ≤ a` and fail; you need `rw [← h]`
  (R10).
- `a / 0 = 0` in Lean, so `Nat.div_mul_le_self` needs no `b ≠ 0`; the `b = 0` case is closed by `h`
  being impossible, not by arithmetic.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| a function that may fail | `if c then none else some x` | R1 |
| a function by cases on a list | `fun \| _ :: y :: _ => … \| _ => …` (catch-all last) | R2 |
| split `A ∧ B` | `constructor` | R3 |
| assume the premise of `A → B` | `intro h` | R4 |
| unfold `f` and decide its `if` using `h` | `simp [f, h]` | R5, R6 |
| case on a condition | `by_cases hb : b = 0` | R7 |
| `h : none = some q` (impossible) | `simp at h` (closes the goal) | R8 |
| `h : some a = some b` → `h : a = b` | `simp at h` | R9 |
| use `h : e = q` right to left | `rw [← h]` | R10 |
| `m / n * n ≤ m` | `exact Nat.div_mul_le_self m n` | R11 |
| prove `A ∧ B ∧ C` in one term | `⟨_, _, _⟩` | R12 |
| a pattern-matching function on a known shape | `rfl` | R13 |
| see the state | infoview | |
