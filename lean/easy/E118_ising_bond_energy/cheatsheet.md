# E118 · Ising bond energy: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `cases` on an inductive type, `t <;> u`, `simp [defs]`,
`exact`, `rw`.
**New here:** Mathlib's real numbers `ℝ` as the codomain of a definition, `if` on a `Bool`, and the
handful of lemmas `simp` uses to evaluate a product of `±1` spins.

The physics: an Ising spin is $s \in \{+1, -1\}$, encoded as `b : Bool` via `spin b = if b then 1 else -1`.
A bond with coupling $J \in \mathbb{R}$ between spins $s_a, s_b$ has energy $E = -J\,s_a s_b$, so aligned
spins ($s_a = s_b$, $s_a s_b = 1$) give $-J$ and anti-aligned ones give $+J$. Flipping both spins leaves
$s_a s_b$ unchanged (the global $\mathbb{Z}_2$ symmetry of the Ising model).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[MulOneClass α]`
  is a requirement on `α` (a *type class*); each entry says which familiar types meet it (`ℝ` meets all
  of them).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers. `-J` is negation, `1`, `-1` are the real numerals |
| `Bool` | the two values `false`, `true` (not `Prop`: a `Bool` is data, `False`/`True` are statements) |
| `!a` | `not a` (Boolean negation): `!true = false`, `!false = true` |
| `bond J (!a) !b` | `bond J (!a) (!b)`: Lean drops the parentheses around the last argument |
| `(bond J false !false) = J` | the parentheses around the left side are only printing; it is `bond J false (!false) = J` |
| `if b = true then x else y` | `if b then x else y` with `b : Bool`: the condition is the statement `b = true` |
| `if True then x else y` | the condition already simplified to the statement `True`; it reduces to `x` (R6) |
| `- -a` | `-(-a)` |
| `-if c then x else y`, `t * if c then x else y` | an `if` runs to the end of the expression: `-(if c then x else y)`, `t * (if c then x else y)` |
| `case false`, `case true` | the goals made by `cases b` (R1) |
| `case false.true` | the goal with `a = false`, `b = true` after `cases a <;> cases b` (R2) |

---

## Part 1 · `bond_values`

Statement: for every coupling `J` and spin `a`, `bond J a a = -J` (aligned) and `bond J a (!a) = J`
(anti-aligned). `a` is a variable, so `simp` cannot evaluate `spin a`; split `a` into its two values first
(R1), then let `simp [bond, spin]` evaluate everything (R3–R10).

### Splitting on `Bool`

**R1 · `cases b`** changes the **goal list and the context**: `b : Bool` leaves the context and there is one
goal per constructor, `false` first. Placeholders: `(P : Bool → Prop) (b : Bool)`.

| Before | After |
|---|---|
| `⊢ P b` | `⊢ P false`, `⊢ P true` |

### What `simp [bond, spin]` does

You write one `simp [bond, spin]`; it applies R3–R10 in whatever order they match. Each is shown here as a
single step so you can recognise the leftovers if `simp` stops early.

**R3 · `simp only [D]`** changes the **goal**: a defined name is replaced by its body. Placeholders:
`D` defined by `def D (b : Bool) : ℝ := if b then 2 else 0`, `(b : Bool)`. When `b` is the literal `true`,
`simp` also turns the condition `true = true` into `True` on the spot.

| Before | After |
|---|---|
| `⊢ P (D b)` | `⊢ P (if b = true then 2 else 0)` |

**R4 · `Bool.not_true`, `Bool.not_false`** change the **goal**. Statements: `(!true) = false`,
`(!false) = true`. Placeholders: `(P : Bool → Prop)`.

| Before | After |
|---|---|
| `⊢ P !true` | `⊢ P false` |
| `⊢ P !false` | `⊢ P true` |

**R5 · `Bool.false_eq_true`** changes the **goal**. Statement: `(false = true) = False`: the condition of an
`if` on the literal `false` becomes the statement `False`. Placeholders: `(P : Prop → Prop)`.

| Before | After |
|---|---|
| `⊢ P (false = true)` | `⊢ P False` |

**R6 · `↓reduceIte`** changes the **goal**: an `if` whose condition is `True` or `False` is replaced by the
matching branch. It is a *simproc* (a procedure `simp` runs, not a lemma); `↓` means it fires before `simp`
enters the branches. Lemma versions: `if_pos : c → (if c then x else y) = x`, and `if_neg` for `¬c`.
Placeholders: `{α : Type} (x y : α)`.

| Before | After |
|---|---|
| `⊢ P (if True then x else y)` | `⊢ P x` |
| `⊢ P (if False then x else y)` | `⊢ P y` |

**R7 · `mul_one`** changes the **goal**. Statement: `mul_one : a * 1 = a`. Placeholders:
`{α : Type} [MulOneClass α] (a : α)` (α has `*` and a `1` that is neutral for it; `ℕ`, `ℤ`, `ℝ`, `ℂ` qualify).

| Before | After |
|---|---|
| `⊢ P (a * 1)` | `⊢ P a` |

**R8 · `mul_neg`** changes the **goal**: a minus sign moves out of the right factor. Statement:
`mul_neg : a * -b = -(a * b)`. Placeholders: `{α : Type} [Mul α] [HasDistribNeg α] (a b : α)`
(α has `*` and a negation that commutes with it; `ℤ`, `ℝ`, `ℂ` qualify, `ℕ` does not).

| Before | After |
|---|---|
| `⊢ P (a * -b)` | `⊢ P (-(a * b))` |

**R9 · `neg_neg`** changes the **goal**. Statement: `neg_neg : - -a = a`. Placeholders:
`{α : Type} [InvolutiveNeg α] (a : α)` (negation applied twice is the identity; `ℤ`, `ℝ`, `ℂ` qualify).

| Before | After |
|---|---|
| `⊢ P (- -a)` | `⊢ P a` |

**W3: the arithmetic of two down spins, `t * (-1 * -1)`, step by step** (R8, R7, R9, R7):

```lean-goal
⊢ t * (-1 * -1) = t
⊢ t * -(-1 * 1) = t
⊢ t * - -1 = t
⊢ t * 1 = t
```

### Closing the conjunction

**R10 · `and_self`** changes the **goal**. Statement: `and_self : (A ∧ A) = A`. `simp` first closes each
`x = x` to `True` (by `rfl`), then `True ∧ True` to `True` with this lemma, and a goal `True` is closed.
So `simp` proves both halves of `bond_values` at once; no `constructor` is needed. Placeholders: `(A : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ A` | `⊢ A` |

**W1: the same chain on another spin, `mag b = if b then 2 else -2`, proving `mag (!a) = -mag a`.**
After `cases a` (R1) and `simp only [mag]` (R3) the two goals are

```lean-goal
⊢ (if (!false) = true then 2 else -2) = -if false = true then 2 else -2
⊢ (if (!true) = true then 2 else -2) = -if True then 2 else -2
```

R4–R6 close the `true` goal (`-2 = -2`) and leave the `false` goal at

```lean-goal
⊢ 2 = - -2
```

which R9 closes. `cases a <;> simp [mag]` does all of it in one line.

---

## Part 2 · `bond_flip`

Statement: `bond J (!a) (!b) = bond J a b` for all `J`, `a`, `b`. Two Boolean variables: split both (R2),
then the same `simp [bond, spin]` as in Part 1 (R3–R9) closes all four goals.

**R2 · `cases a <;> cases b`** changes the **goal list and the context**: `cases a` makes two goals and
`<;>` runs `cases b` in each, so there are four, named `false.false`, `false.true`, `true.false`,
`true.true`. Placeholders: `(P : Bool → Bool → Prop) (a b : Bool)`.

| Before | After |
|---|---|
| `⊢ P a b` | `⊢ P false false`, `⊢ P false true`, `⊢ P true false`, `⊢ P true true` |

**W2.** `link a b = mag a * mag b` (W1's `mag`): `cases a <;> cases b <;> simp [link, mag]` proves
`link (!a) b = -link a b`. Pass every definition the goal mentions to `simp`, the inner ones (`mag`)
included: `simp [link]` alone leaves `mag (!a)` unevaluated.

```lean-goal
⊢ link (!a) b = -link a b
```

---

## Traps

- `simp [bond, spin]` before `cases a` cannot evaluate `spin a`: with a variable `a` the `if` has no
  literal condition, and `simp` does not split it. Split first, then `simp`.
- `simp [bond]` alone leaves `spin true`, `spin false` in the goal: name both definitions.
- `t1 ; t2` runs `t2` on the first goal only. After `cases`, use `cases a <;> simp [...]` or `all_goals`.
- `bond_flip` needs `cases` on both `a` and `b`: after `cases a` alone, `spin b` is still a variable.
- `Bool` and `Prop` differ: `true` is a value, `True` is a statement. `if b then …` means
  `if b = true then …`, and `simp` turns `true = true` into `True` and `false = true` into `False` (R5).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| split one `Bool` | `cases a` | R1 |
| split two `Bool`s | `cases a <;> cases b` | R2 |
| unfold definitions and evaluate | `simp [bond, spin]` | R3–R10 |
| unfold only | `simp only [D]` | R3 |
| `!true → false`, `!false → true` | `Bool.not_true`, `Bool.not_false` | R4 |
| `false = true → False` | `Bool.false_eq_true` | R5 |
| `if True/False then x else y → x / y` | `↓reduceIte` (or `if_pos`, `if_neg`) | R6 |
| `a * 1 → a` | `mul_one` | R7 |
| `a * -b → -(a * b)` | `mul_neg` | R8 |
| `- -a → a` | `neg_neg` | R9 |
| `A ∧ A → A` | `and_self` | R10 |
| run a tactic on every goal | `t <;> u`, `all_goals u` | TACTIC_STATES |
| see the state | infoview | |
