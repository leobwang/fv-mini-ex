# M054 · Exponent-2 groups are abelian: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's groups (`[Group G]`, `*`, `1`,
`⁻¹`), the lemmas `inv_eq_of_mul_eq_one_right` and `mul_inv_rev`, `calc` chains, and using a theorem
you proved earlier as a function.

## How to read an entry

Each entry is one tactic, one lemma used with `apply`/`rw`, or one proof term. It says what changes
(**goal**, **context**, or **goal list**), gives the lemma's statement, lists the placeholders with their
types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : G → Prop`). The step changes only the part inside `P (…)`.
- Placeholders are written as Lean binders. `{G : Type}` is any type. A bracket such as `[Group G]` is a
  requirement on `G` (a *type class*): `G` has `*`, `1`, `⁻¹` with associativity, `1 * a = a`,
  `a * 1 = a`, and `a⁻¹ * a = 1`. Nothing says `*` commutes. Familiar instances: permutations
  `Equiv.Perm α` under composition, invertible matrices. `ℤ` with `+` is a group, but Mathlib writes it
  additively (`[AddGroup ℤ]`, with `+`, `0`, `-`), so it does not meet `[Group G]`.
- Mathlib states R1 and R5 for `[DivisionMonoid G]` (a monoid with an `⁻¹` that reverses products).
  Every group is one, so `#check` showing `DivisionMonoid` is no obstacle: they apply to your `G`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `inst✝ : Group G` | the anonymous hypothesis the binder `[Group G]` creates: `G` is a group |
| `1` | the identity element of `G` (not the number one; `G` need not contain numbers) |
| `a⁻¹` | the group inverse of `a` |
| `a * b * c` | `(a * b) * c`: `*` groups to the left |
| `P (a * b)⁻¹` | `P` applied to `(a * b)⁻¹`; Lean drops the outer parentheses |
| `h : ∀ (g : G), g * g = 1` | for every `g`, `g * g = 1`; `h x : x * x = 1` for any `x : G` |
| `T h x` | a theorem `T` applied to its explicit arguments in order (here a hypothesis, then an element) |
| `_ = c := p` | a `calc` line: `_` is the right side of the previous line, `p` proves this step |
| `case calc_1` | inside `by calc`, the goal left by the first step written `?_` (R3) |

---

## Part 1 · `inv_eq_self`

Statement: if `g * g = 1` for every `g : G`, then `a⁻¹ = a`. In words: `a` is a right inverse of itself,
and in a group a right inverse is THE inverse.

**R1 · `apply inv_eq_of_mul_eq_one_right`** changes the **goal**. The lemma is
`inv_eq_of_mul_eq_one_right : a * b = 1 → a⁻¹ = b`; `apply` matches its conclusion with the goal, which
fixes `a` and `b`, and leaves its premise as the new goal. As a term, `inv_eq_of_mul_eq_one_right hab`
proves `a⁻¹ = b` from `hab : a * b = 1`. Placeholders: `{G : Type} [Group G] (a b : G)`.

| Before | After |
|---|---|
| `⊢ a⁻¹ = b` | `⊢ a * b = 1` |

**R2 · `exact h x`** **closes** the goal. A hypothesis `h : ∀ g, P g` is a function from elements to
proofs: `h x : P x`. A theorem you proved earlier is used the same way, with one argument per explicit
binder in the order they appear in its statement. Placeholders: `{G : Type} (P : G → Prop) (x : G)`.

| Before | After |
|---|---|
| `⊢ P x` (with `h : ∀ (g : G), P g` in the context) | no goals |

---

## Part 2 · `comm_of_sq_one`

Statement: under the same hypothesis `h`, `a * b = b * a`. In words: `a * b` is its own inverse (Part 1
at `a * b`), its inverse is `b⁻¹ * a⁻¹` (inverses reverse products), and `b⁻¹ * a⁻¹ = b * a` (Part 1
twice). Part 1's theorem is available here: `inv_eq_self h : ∀ (a : G), a⁻¹ = a`.

**R3 · `calc`** changes the **goal list**. `calc a = b := p₁` then lines `_ = c := p₂`, … prove `a = d` by
a chain; each `_` is the right side of the previous line. A step proved by `?_` becomes a goal after
the `calc`; a step proved by `by tac` is proved on the spot. In term mode (right after `:=`) write
`calc` with no `by`. Placeholders: `{α : Type} (a b c d : α)`.

| Before | After |
|---|---|
| `⊢ a = d` | `⊢ b = c` |

**R4 · `Eq.symm`** changes the **goal**: `apply Eq.symm` turns `b = a` into `a = b`. As a term, from
`h : a = b` the term `h.symm` proves `b = a`. Use it when a lemma gives the equation the wrong way round.
Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `⊢ b = a` | `⊢ a = b` |

**R5 · `mul_inv_rev`** changes the **goal**. The lemma is `mul_inv_rev a b : (a * b)⁻¹ = b⁻¹ * a⁻¹`: the
inverse of a product is the product of the inverses in reverse order. As a term it is a whole `calc`
step. Placeholders: `{G : Type} [Group G] (a b : G)`.

| Before | After |
|---|---|
| `⊢ P (a * b)⁻¹` | `⊢ P (b⁻¹ * a⁻¹)` |

**R6 · `rw [hinv]`, `hinv : ∀ g, g⁻¹ = g`** changes the **goal**. `rw` with a `∀` equation finds the first
subterm of the form `_⁻¹`, fixes `g` to it, and rewrites only that instance (all its copies). A second
`rw [hinv]` takes the next one. `rw [inv_eq_self h]` behaves the same. Placeholders:
`{G : Type} [Group G] (a b : G)`.

| Before | After `rw [hinv]` | After a second `rw [hinv]` |
|---|---|---|
| `⊢ P (b⁻¹ * a⁻¹)` | `⊢ P (b * a⁻¹)` | `⊢ P (b * a)` |

When the goal after `rw` is `x = x`, `rw` closes it itself (it tries `rfl`).

### Worked combinations (W1–W2, on a group where every element cubes to `1`)

`h3 : ∀ g : G, g * g * g = 1`. One extra lemma: `mul_assoc : a * b * c = a * (b * c)`.

**W1 · `inv_eq_sq`: `a⁻¹ = a * a`.** R1 leaves `a * (a * a) = 1`; `rw [← mul_assoc]` regroups it; R2
closes it with `h3 a`:

```lean-goal
⊢ a⁻¹ = a * a
⊢ a * (a * a) = 1
⊢ a * a * a = 1
```

**W2 · a `calc` that uses W1.** `a * b * (a * b) = (a * b)⁻¹` is `(inv_eq_sq h3 (a * b)).symm` (R2, R4);
the next step is `mul_inv_rev a b` (R5); the last is `by rw [inv_eq_sq h3, inv_eq_sq h3]` (R6).

---

## Traps

- `mul_comm`, `CommGroup` and `mul_comm_of_mul_self_eq_one` are banned. `ring`, `simp` and `group` do not
  know `*` commutes in `G`, so they cannot finish `a * b = b * a` for you.
- `apply inv_eq_of_mul_eq_one_right` needs the goal to be `_⁻¹ = _` with the inverse on the LEFT. For
  `a = a⁻¹` flip it first (R4).
- `inv_eq_self h (a * b)` proves `(a * b)⁻¹ = a * b`; the calc step `a * b = (a * b)⁻¹` needs `.symm`.
- `rw [inv_eq_self h]` rewrites one inverse per use (R6). With two inverses, write it twice.
- In a `calc` every line after the first starts with `_`, indented under the first term.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| goal `a⁻¹ = b` → `a * b = 1` | `apply inv_eq_of_mul_eq_one_right` | R1 |
| use `h : ∀ g, P g` at `x` | `h x` | R2 |
| use an earlier theorem `T` | `T h x` (arguments in order) | R2 |
| chain `a = b = c = d` | `calc a = b := p₁` / `_ = c := p₂` / `_ = d := p₃` | R3 |
| flip an equation | `h.symm`, `apply Eq.symm` | R4 |
| `(a * b)⁻¹ → b⁻¹ * a⁻¹` | `mul_inv_rev a b`, `rw [mul_inv_rev]` | R5 |
| remove inverses one at a time | `rw [hinv, hinv]` | R6 |
| regroup `a * (b * c) → a * b * c` | `rw [← mul_assoc]` | W1 |
| see the state | infoview | |
