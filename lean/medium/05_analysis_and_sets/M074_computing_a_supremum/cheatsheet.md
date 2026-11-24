# M074 · Computing a supremum: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ`, sets and
`Set.range`, upper/lower bounds, the supremum `sSup` and the predicate `IsLUB`, the Archimedean
property, and the arithmetic automation `positivity`, `linarith`, `nlinarith`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`apply`/`obtain`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. `G : Prop` is an arbitrary goal, and `g` a hypothesis that finishes it.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Preorder α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers (a complete ordered field) |
| `↑n` | the natural number `n : ℕ` cast into `ℝ` (written `(n : ℝ)` in source) |
| `Set α` | sets of elements of `α`, i.e. predicates `α → Prop`; `x ∈ s` is `s x` |
| `Set.range f` | the image `{f n \| n}`; `x ∈ Set.range f` unfolds to `∃ n, f n = x` |
| `Set.range fun n => 1 - 1 / (↑n + 1)` | the set $\{1 - \tfrac{1}{n+1} : n \in \mathbb N\}$ of the exercise |
| `upperBounds s` | the set `{x \| ∀ ⦃a⦄, a ∈ s → a ≤ x}` of upper bounds of `s` |
| `lowerBounds t` | the set `{x \| ∀ ⦃a⦄, a ∈ t → x ≤ a}` of lower bounds of `t` |
| `IsLUB s a` | `a` is the least upper bound: `a ∈ upperBounds s ∧ a ∈ lowerBounds (upperBounds s)` |
| `sSup s` | the supremum of `s`; Mathlib defines it for every set, as junk `0` when `s` is empty or unbounded |
| `s.Nonempty` | `∃ x, x ∈ s` |
| `⦃a⦄` | a strict-implicit binder: `a` is filled in once the membership proof is given |
| `(fun n => body) n` | a function applied to `n`, not yet simplified; `dsimp only` substitutes (R6) |
| `¬a ≤ b` | `a ≤ b → False` |
| `case H`, `case ne` | the two goals `apply IsLUB.csSup_eq` leaves when no argument is given (R1): `IsLUB s a` and `s.Nonempty` |
| `case left`, `case right` | the two halves of `IsLUB` after `constructor` (R3); `case H.left`, `case H.right` if R1 left `H` named |
| `1 / (↑n + 1)` | real division; `↑n + 1 > 0`, so it is a positive real |

---

## Part 1 · `sSup_one_sub_inv`

Statement: the supremum of $\{1 - \tfrac{1}{n+1} : n \in \mathbb N\}$ is $1$. Because `sSup` is junk on bad
sets, you prove the honest statement `IsLUB s 1` plus `s.Nonempty` (R1, R2). `IsLUB` has two halves (R3):
`1` is an upper bound (every term is `≤ 1`, since `1/(n+1) > 0`), and every upper bound `b` has `1 ≤ b`
(if `b < 1`, the Archimedean property gives `n` with `1/(n+1) < 1 - b`, so the term `1 - 1/(n+1)` beats `b`).

### Reducing `sSup` to `IsLUB`

**R1 · `apply IsLUB.csSup_eq`** changes the **goal list**. The lemma is
`IsLUB.csSup_eq : IsLUB s a → s.Nonempty → sSup s = a`; `apply` leaves its two hypotheses as goals (named
`H` and `ne`). Placeholders: `{α : Type} [ConditionallyCompleteLattice α] (s : Set α) (a : α)`; a
*conditionally complete lattice* is an order where every nonempty bounded set has a supremum, and `ℝ` is one.
Give an argument as `_` to leave it as a goal: `apply IsLUB.csSup_eq _ hne` leaves only `IsLUB s a`.

| Before | After |
|---|---|
| `⊢ sSup s = a` | `⊢ IsLUB s a`, `⊢ s.Nonempty` |

**R2 · `refine ⟨f i, ?_⟩`, then `Set.mem_range_self i`** closes `(Set.range f).Nonempty`. `Nonempty` is an
`∃`, so you give a witness and a membership proof; `Set.mem_range_self i : f i ∈ Set.range f`. As one term
(to pass into R1): `⟨_, Set.mem_range_self i⟩`, where `_` is inferred as `f i`. Placeholders:
`{ι α : Type} (f : ι → α) (i : ι)`.

| Before | After `refine ⟨f i, ?_⟩` |
|---|---|
| `⊢ (Set.range f).Nonempty` | `⊢ f i ∈ Set.range f` |

**R3 · `constructor`** on `IsLUB s a` changes the **goal list**. `IsLUB s a` is by definition the conjunction
`a ∈ upperBounds s ∧ a ∈ lowerBounds (upperBounds s)`, so `constructor` splits it (goals `left`, `right`).
Placeholders: `{α : Type} [Preorder α] (s : Set α) (a : α)`; `[Preorder α]` gives `≤`, `ℝ` qualifies.

| Before | After |
|---|---|
| `⊢ IsLUB s a` | `⊢ a ∈ upperBounds s`, `⊢ a ∈ lowerBounds (upperBounds s)` |

### Half 1: `1` is an upper bound

**R4 · `rintro _ ⟨n, rfl⟩`** changes the **goal and the context**. `a ∈ upperBounds (Set.range f)` unfolds to
`∀ ⦃x⦄, x ∈ Set.range f → x ≤ a`, and `x ∈ Set.range f` to `∃ n, f n = x`. The pattern introduces `x` (as
`_`), splits the `∃` into `n` and an equation, and `rfl` substitutes `x := f n`. Placeholders:
`{ι : Type} (f : ι → ℝ) (a : ℝ)`. With `f` a `fun`, the goal shows `(fun n => …) n ≤ a` (R6).

| Before | After |
|---|---|
| `⊢ a ∈ upperBounds (Set.range f)` | `n : ι ⊢ f n ≤ a` |

**R5 · `positivity`** **closes** a goal `0 < e` or `0 ≤ e` when `e` is built by `+`, `*`, `/`, `^`, casts
from obviously positive pieces (numerals, `↑n + 1`, hypotheses `0 < c`). Use it in
`have : 0 < 1 / ((n : ℝ) + 1) := by positivity`. Placeholders: `(n : ℕ) (c : ℝ) (hc : 0 < c)`.

| Before | After |
|---|---|
| `hc : 0 < c ⊢ 0 < c / (↑n + 2)` | closed |

**R6 · `dsimp only`** changes the **goal**: with no lemmas it only does definitional clean-up, here *beta
reduction* `(fun k => body) n ↦ body[k := n]`. `linarith` happens to cope with the unreduced form, but
the reduced goal is the one you reason about, and `rw` patterns are written against it. Placeholders:
`(g : ℕ → ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ((fun k => g k + 1) n)` | `⊢ P (g n + 1)` |

**R7 · `linarith`** **closes** a goal `t < u`, `t ≤ u`, `t = u` or `False` that follows from the hypotheses
by adding them with nonnegative coefficients. Non-linear pieces such as `1 / (↑n + 1)` are treated as
unknowns, so it needs the fact about them (from R5) in the context. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `hx : 0 < x ⊢ y - x ≤ y` | closed |
| `h1 : x ≤ y, h2 : y < x ⊢ False` | closed |

### Half 2: every upper bound is `≥ 1`

**R8 · `intro b hb`** changes the **goal and the context**. `a ∈ lowerBounds t` unfolds to
`∀ ⦃b⦄, b ∈ t → a ≤ b`, so two `intro`s give the bound and its proof. Placeholders: as in R3.

| Before | After |
|---|---|
| `⊢ a ∈ lowerBounds (upperBounds s)` | `b : α, hb : b ∈ upperBounds s ⊢ a ≤ b` |

**R9 · `by_contra hlt`** changes the **goal and the context**: assume the negation of the goal and prove
`False`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ≤ b` | `hlt : ¬a ≤ b ⊢ False` |

**R10 · `push Not at hlt`** changes the **context**: it pushes `¬` inward, so `¬a ≤ b` becomes `b < a`
(`push_neg`, the older spelling you may see in examples online, is deprecated and warns). Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `hlt : ¬a ≤ b ⊢ False` | `hlt : b < a ⊢ False` |

**R11 · `obtain ⟨n, hn⟩ := exists_nat_gt x`** changes the **context**. The lemma is
`exists_nat_gt (x : R) : ∃ n : ℕ, x < ↑n` for an *Archimedean* ordered semiring `R` (one with no element
above all naturals; `ℝ` is one). `obtain` splits the `∃`. Placeholders: `(x : ℝ)`. In the exercise choose
`x := 1 / (1 - b)`: then `1/(n+1) < 1/n < 1 - b`.

| Before | After |
|---|---|
| `⊢ G` | `n : ℕ, hn : x < ↑n ⊢ G` |

**R12 · `have hbn : f n ≤ b := hb ⟨n, rfl⟩`** changes the **context**. `hb : b ∈ upperBounds (Set.range f)`
is a function from membership proofs to bounds; `⟨n, rfl⟩ : f n ∈ Set.range f` (or `Set.mem_range_self n`).
Placeholders: `{ι : Type} (f : ι → ℝ) (b : ℝ) (n : ι)`. In the exercise write the type out,
`1 - 1 / ((n : ℝ) + 1) ≤ b`: Lean accepts it (it is `f n` beta-reduced) and the context stays readable.

| Before | After |
|---|---|
| `⊢ G` | `hbn : f n ≤ b ⊢ G` |

**R13 · `rw [div_lt_iff₀ hc]`** changes the **goal**. The lemma is
`div_lt_iff₀ (hc : 0 < c) : a / c < b ↔ a < b * c` (clear a positive denominator). `rw` with an `↔` rewrites
the proposition. Placeholders: `(a b c : ℝ) (hc : 0 < c)`; any ordered field qualifies. Write
`rw [div_lt_iff₀ (by positivity)]` when `c` is `↑n + 1`.

| Before | After |
|---|---|
| `⊢ a / c < b` | `⊢ a < b * c` |

**R14 · `rw [div_lt_iff₀ hc] at hn`** changes the **context**: the same rewrite inside hypothesis `hn`.
Placeholders: as in R13.

| Before | After |
|---|---|
| `hn : a / c < b ⊢ False` | `hn : a < b * c ⊢ False` |

**R15 · `nlinarith`** **closes** what `linarith` would, and more: it also adds products of pairs of
hypotheses (here `0 < x` times `0 < y - 1`, which `linarith` alone cannot find). Both tactics first multiply
out products, so `(1 - b) * (↑n + 1)` is seen as `↑n - b * ↑n + 1 - b`. In the exercise the final step is then
linear in the pieces `↑n`, `b`, `b * ↑n`, and `linarith` would also close it; `nlinarith` is the safe choice
when a product of hypotheses might be needed. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `hx : 0 < x, h : 1 < y ⊢ x < x * y` | closed |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: a constant sequence.** `sSup (Set.range fun _ : ℕ => 2) = 2`. R1 with R2 passed inline leaves one goal,
and R3 splits it:

```lean-goal
⊢ sSup (Set.range fun x => 2) = 2
⊢ IsLUB (Set.range fun x => 2) 2
⊢ 2 ∈ upperBounds (Set.range fun x => 2)
⊢ 2 ∈ lowerBounds (upperBounds (Set.range fun x => 2))
```

The upper bound: R4, R6, then `rfl`. The least part: R8, then R12 with `n := 0` closes it directly (the
supremum is attained, so no contradiction is needed).

**W2: `IsLUB (Set.Ico 0 1) 1` by contradiction.** `x ∈ Set.Ico a b` means `a ≤ x ∧ x < b`. In the `right`
goal: R8, R9, R10, then feed `hb` two members of the set, `0` and the midpoint `(b + 1) / 2`, and close with
R7. In the exercise the Archimedean term plays the midpoint's role.

**W3: the Archimedean step.** From `hc : 0 < c`, R11 with `x := 1 / c`, then R14:

```lean-goal
⊢ ∃ n, 1 < ↑n * c
```

| Before | After |
|---|---|
| `hc : 0 < c ⊢ ∃ n, 1 < ↑n * c` | `n : ℕ, hn : 1 / c < ↑n ⊢ ∃ n, 1 < ↑n * c` |
| `hn : 1 / c < ↑n ⊢ ∃ n, 1 < ↑n * c` | `n : ℕ, hn : 1 < ↑n * c ⊢ ∃ n, 1 < ↑n * c` |

---

## Traps

- `sSup s` is defined for **every** set: Mathlib returns `0` when `s` is empty or not bounded above. So no
  lemma turns `sSup s = a` into bounds without also asking for `s.Nonempty` (R1). Do not try to unfold `sSup`.
- After R4 the goal is `(fun n => 1 - 1 / (↑n + 1)) n ≤ 1`, a function not yet applied to `n`. It is the same
  statement as `1 - 1 / (↑n + 1) ≤ 1`; `dsimp only` (R6) shows it in that form.
- `linarith` does not know `1 / (↑n + 1) > 0`; prove it with `positivity` (R5) and put it in the context.
- `div_lt_iff₀` needs the denominator positive: `rw [div_lt_iff₀ (by positivity)]` for `↑n + 1`, and the
  hypothesis `0 < 1 - b` (from `b < 1` by `linarith`) for `1 / (1 - b)`. Prove that before R14.
- Filters and limits (`Tendsto`, `atTop`, `nhds`) are banned: the point is the ε-style argument.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `sSup s = a` → least upper bound | `apply IsLUB.csSup_eq _ ⟨_, Set.mem_range_self 0⟩` | R1, R2 |
| split `IsLUB s a` | `constructor` | R3 |
| take an element of `Set.range f` | `rintro _ ⟨n, rfl⟩` | R4 |
| `0 < 1 / (↑n + 1)` | `positivity` | R5 |
| simplify `(fun n => …) n` | `dsimp only` | R6 |
| linear (in)equality or `False` from hypotheses | `linarith` | R7 |
| take an upper bound | `intro b hb` | R8 |
| prove `a ≤ b` by contradiction | `by_contra hlt; push Not at hlt` | R9, R10 |
| a natural above `x` (Archimedes) | `obtain ⟨n, hn⟩ := exists_nat_gt x` | R11 |
| an upper bound applied to `f n` | `hb ⟨n, rfl⟩` | R12 |
| clear a positive denominator in `<` | `rw [div_lt_iff₀ hc]` / `… at hn` | R13, R14 |
| inequality needing a product of hypotheses | `nlinarith` | R15 |
| see the state | infoview | |
