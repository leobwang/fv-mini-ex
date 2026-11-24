# E016 · Bool and Option cases: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics up to E015: `rfl` (E001), definitions by `match` (E002), `cases h` on an `Or`
(E006), `simp`, `simp at h`, `simp [f]` (E010), `omega` (E011), `induction` (E014, E015). **New here:**
`cases` on a value of an inductive type with no recursion (`Bool`, `Option α`), the combinator `t <;> s`,
how `simp` handles `Option.map` and `some a = some b`, and `simp_all`. No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Bool → Prop`, `P : Nat → Prop`, or a plain `P : Prop` when the entry
  only changes a hypothesis). The step changes only the part inside `P (…)`.
- `{α β : Type}` are any types (`Nat`, `Bool`, `List Nat`, …); `f : α → β` is any function.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Case analysis on a finite inductive type

`Bool` has exactly two constructors, `false` and `true`. `Option α` has two: `none` (no value) and
`some x` (carrying `x : α`). Unlike `Nat` or `List`, neither constructor takes an argument of the type being
defined, so there is no induction hypothesis: `cases v` just makes one goal per constructor, with `v`
replaced by that constructor. A function defined by `match` on `v` (or a Bool operation such as `&&`) then
computes, because its argument is now a constructor.

## Reading the goals

| You see | It means |
|---|---|
| `b && c`, `b \|\| c`, `!b` | Bool and, or, not (functions `Bool → Bool → Bool` and `Bool → Bool`) |
| `(b && !b) = false` | an equation between two `Bool` values; it is a `Prop` |
| `Option Nat` | a `Nat` that may be missing: `none` or `some n` |
| `o.map f`, `Option.map f o` | apply `f` inside: `none ↦ none`, `some a ↦ some (f a)` |
| `(· + 1)` | in the statement: the function `fun x => x + 1`; the infoview prints it as `fun x => x + 1` |
| `Option.map (fun x => x + 1) o` | how the infoview prints `o.map (· + 1)` |
| `match o with \| some x => x \| none => d` | `getOr o d` unfolded while `o` is unknown: stuck until `cases o` picks an arm |
| `case false`, `case true` | the two goals made by `cases b` (R1) |
| `case none`, `case some` | the two goals made by `cases o` (R4) |
| `val✝ : α` | the value inside `some`, with a name you cannot type (R4) |

---

## Part 1 · `and_not_self_bool`

Statement: `(b && !b) = false` for every `b : Bool`. Split `b`; in each case both sides are closed `Bool`
terms that compute, so `rfl` closes them. Do both at once with `<;>`.

**R1 · `cases b`** changes the **goal list and the context**: `b : Bool` leaves the context; one goal becomes a
`false` goal and a `true` goal. Placeholders: `(P : Bool → Prop) (b : Bool)`.

| Before | After |
|---|---|
| `b : Bool ⊢ P b` | `⊢ P false`, `⊢ P true` |

**R2 · `rfl`** **closes** an equation whose two sides compute to the same `Bool` once no variables are left:
`!true` is `false`, `false && true` is `false`.

| Before | After |
|---|---|
| `⊢ (!true && true) = false` | no goals |

**R3 · `t <;> s`** changes the **goal list**: it runs `t`, then `s` on **every** goal `t` produced. `cases b <;> rfl`
is R1 then R2 on both cases. If `s` fails on any one goal, the whole line fails.

| Before | After |
|---|---|
| `b : Bool ⊢ (b && b) = b` | no goals |

**W1:** `(!(b && b)) = !b` by `cases b <;> rfl`, the same pattern.

---

## Part 2 · `getOr_le`

Statement: `getOr o d ≤ getOr o 0 + d`, where `getOr (some x) d = x` and `getOr none d = d`. `getOr o _` does
not compute while `o` is unknown, so split `o` (R4). Then `simp [getOr]` unfolds both sides (R5) and closes
the arithmetic that is left (R6): case `none` becomes `d ≤ 0 + d`, case `some x` becomes `x ≤ x + d`.

**R4 · `cases o`** changes the **goal list and the context**: a `none` goal and a `some` goal. In the `some` goal
the context gains the value inside, printed `val✝` because Lean made up the name (you cannot refer to it).
`cases o with | none => … | some x => …` names it `x` instead, as `induction … with` did in E014.
Placeholders: `{α : Type} (P : Option α → Prop) (o : Option α)`.

| Before | After |
|---|---|
| `o : Option α ⊢ P o` | `⊢ P none`, `val✝ : α ⊢ P (some val✝)` |

**R5 · `simp [f]` on a constructor** changes the **goal**: `f (some x)` and `f none` are replaced by the right side
of the matching `match` arm. Here `orDouble (some x) = 2 * x`. On `f o` with `o` unknown
it only exposes `match o with …`, which cannot pick an arm: split first. Placeholders: `(x : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (orDouble (some x))` | `⊢ P (2 * x)` |

**R6 · `simp`** **closes** the small `Nat` facts left over. It knows `Nat.le_add_right : n ≤ n + k` and
`Nat.zero_add : 0 + n = n`, and `n ≤ n` is `True`. `omega` would also do. Placeholders: `(a d : Nat)`.

| Before | After |
|---|---|
| `⊢ a ≤ a + d ∧ d ≤ 0 + d` | no goals |

**W2:** `orDouble o % 2 = 0` by `cases o <;> simp [orDouble]`: R4, then R5 and a closing `simp` in each case.

---

## Part 3 · `map_eq_some`

Statement: from `h : o.map (· + 1) = some 5` conclude `o = some 4`. Here the information is in the
**hypothesis**, so after splitting `o` (R4) you simplify `h` and then use it on the goal.

- Case `none`: `h` becomes `none = some 5` (R7), which is impossible, so the case closes (R8).
- Case `some a`: `h` becomes `some (a + 1) = some 5` (R9), then `a + 1 = 5` (R10), then `a = 4` (R11). The goal
  `some a = some 4` follows from it (R10 on the goal, then `h`).

`simp_all` (R12) does all of this in one step in each case, so `cases o <;> simp_all` is the whole proof shape.

**R7 · `Option.map_none`** changes the **context**. The lemma is `Option.map_none : Option.map f none = none`;
`rw [Option.map_none] at h` rewrites `h`. Placeholders: `{α β : Type} (f : α → β) (b : β)`.

| Before | After |
|---|---|
| `h : Option.map f none = some b ⊢ P` | `h : none = some b ⊢ P` |

**R8 · `simp at h` on `h : none = some b`** changes the **goal list**: the goal is closed. Distinct constructors
are never equal, so `simp` turns `h` into `False`, and from `False` any goal follows.
Placeholders: `{β : Type} (b : β) (P : Prop)`.

| Before | After |
|---|---|
| `h : none = some b ⊢ P` | no goals |

**R9 · `Option.map_some`** changes the **context**. The lemma is
`Option.map_some : Option.map f (some a) = some (f a)`. Placeholders: `{α β : Type} (f : α → β) (a : α) (b : β)`.

| Before | After |
|---|---|
| `h : Option.map f (some a) = some b ⊢ P` | `h : some (f a) = some b ⊢ P` |

**R10 · `Option.some.injEq`** changes the **context** (or the goal). The lemma is
`Option.some.injEq : (some a = some b) = (a = b)`: `some` is injective. `simp` uses it by itself.
Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `h : some a = some b ⊢ P` | `h : a = b ⊢ P` |

**R11 · `simp at h` on `a + k = n`** changes the **context**: with numerals `k ≤ n` it solves for `a`.
Placeholders: `(a : Nat)`.

| Before | After |
|---|---|
| `h : a + 2 = 7 ⊢ P` | `h : a = 5 ⊢ P` |

**R12 · `simp_all`** **closes** the goal here (in general it changes **context and goal**). It simplifies every
hypothesis and the goal together, and uses each simplified hypothesis to rewrite the rest. If some hypothesis
becomes `False` it closes the goal. Placeholders: `{α β : Type} (f : α → β) (a : α) (b : β)`.

| Before | After |
|---|---|
| `h : f a = b ⊢ some (f a) = some b` | no goals |

**W3:** `(h : o.map (· + 2) = none) : o = none` by `cases o <;> simp_all`. The roles swap: case `none` is the
easy one, and in case `some` `h` becomes `some (a + 2) = none`, which is `False`.

| Before `cases o <;> simp_all` | After |
|---|---|
| `h : Option.map (fun x => x + 2) o = none ⊢ o = none` | no goals |

---

## Traps

- `simp [getOr]` on `getOr o d` with `o` unknown only unfolds it to `match o with | some x => x | none => d`:
  the `match` cannot pick an arm, so nothing closes. `cases o` first.
- After `cases o`, the value is `val✝` and cannot be typed. If you need to name it, use
  `cases o with | none => … | some x => …`.
- Plain `simp` acts on the goal only. In `map_eq_some` it fails with `simp made no progress` on `o = some 4`,
  and after `cases o` it still cannot use `h`. The information is in `h`: use `simp at h`, then use `h`, or `simp_all`.
- `t ; s` runs `s` only on the first goal after `t`; `t <;> s` runs it on all of them (TACTIC_STATES).
- If `s` in `t <;> s` already closed every goal, appending another `<;> u` is harmless, but a following
  standalone tactic fails with "no goals".

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| split `b : Bool` | `cases b` | R1 |
| closed `Bool` equation | `rfl` (or `decide`) | R2 |
| same tactic on every new goal | `t <;> s` | R3 |
| split `o : Option α` | `cases o` / `cases o with \| none => … \| some x => …` | R4 |
| unfold `f (some x)`, `f none` | `simp [f]` | R5 |
| `x ≤ x + d`, `0 + d` | `simp` (or `omega`) | R6 |
| `Option.map f none` → `none` | `simp at h` / `rw [Option.map_none] at h` | R7 |
| hypothesis `none = some b` | `simp at h` (closes the goal) | R8 |
| `Option.map f (some a)` → `some (f a)` | `simp at h` / `rw [Option.map_some] at h` | R9 |
| `some a = some b` → `a = b` | `simp at h` / `simp` | R10 |
| `a + 2 = 7` → `a = 5` | `simp at h` | R11 |
| simplify hypotheses and goal together | `simp_all` | R12 |
| see the state | infoview | |
