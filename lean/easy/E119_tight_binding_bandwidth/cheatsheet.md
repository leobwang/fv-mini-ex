# E119 · Tight-binding bandwidth: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's `TightBindingChain` and its
`energyEigenvalue`; a set used as a type (subtype elements `k` and their values `↑k`); Mathlib's absolute
value `|x|`, `Real.cos`, and the order lemmas `abs_mul`, `abs_neg`, `abs_two`, `mul_le_of_le_one_right`;
the tactic `positivity`.

The physics: a tight-binding chain is a ring of `N` sites with spacing `a`; an electron sitting on a site
has energy `E0`, and `t` is the amplitude for it to hop to a neighbouring site. The energy eigenstates are
Bloch waves of wavenumber `k`, with `E(k) = E0 - 2t cos(ka)`. Since `|cos| ≤ 1`, every energy lies in
`[E0 - 2|t|, E0 + 2|t|]`: the band has width `4|t|`. In Lean: unfold `E(k)` (R1), cancel the `E0`s (R2),
split the absolute value of the product (R3–R5), and bound the product by its first factor (R6–R8).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`exact`/`apply`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[CommRing α]` is a
  requirement on `α` (a *type class*); each entry says which familiar types meet it.
- Every `⊢` cell written as code is a state Lean reaches in the companion file; `tools/guide_sync.py`
  checks that. Cells containing `|x|` are written as plain text (a raw `|` would split the table); the same
  states appear, checked, in the W1 goal block.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers (`Real`); numerals such as `2` in a real goal are reals |
| `Set ℝ` | a set of reals, i.e. a predicate `ℝ → Prop`; `x ∈ S` means `S x` holds |
| `T : TightBindingChain` | physlib structure (namespace `CondensedMatter`, opened by the file) with fields `N : ℕ` (sites), `a : ℝ` (spacing, `a_pos : 0 < a`), `E0 : ℝ` (on-site energy), `t : ℝ` (hopping) |
| `T.E0`, `T.t`, `T.a` | those fields of `T` (dot notation, E017) |
| `T.QuantaWaveNumber` | a `Set ℝ`: the allowed wavenumbers `2π/(aN) · (n - ⌊N/2⌋)` for `n : Fin N`. Its definition plays no role here |
| `k : ↑T.QuantaWaveNumber` | `k` is an element of that set used as a type (a *subtype*): a pair of a real number and a proof that it lies in the set. The `↑` turns the set into a type |
| `↑k` | the real number inside `k` (`Subtype.val k`, also `k.val`). In source you can write `k`; Lean inserts the `↑` |
| `T.energyEigenvalue k` | `E(k) = T.E0 - 2 * T.t * Real.cos (↑k * T.a)`. Opaque until unfolded (R1) |
| `Real.cos x` | cosine on the reals |
| `\|x\|` | the absolute value of `x` (`abs x`) |
| `\|(-x)\|` | how Lean prints `\|-x\|` |
| `2 * T.t * c` | `(2 * T.t) * c`: `*` groups to the left |
| `case ha`, `case h` | names of the two goals that `apply mul_le_of_le_one_right` leaves (R6) |

---

## Part 1 · `bandwidth`

Statement: for every chain `T` and allowed wavenumber `k`, `|T.energyEigenvalue k - T.E0| ≤ 2 * |T.t|`,
i.e. `|E(k) - E0| ≤ 2|t|`.

### From the energy to an algebraic expression

**R1 · `unfold TightBindingChain.energyEigenvalue`** changes the **goal**: the name is replaced by its
definition. `simp only [TightBindingChain.energyEigenvalue]` does the same. The short name
`TightBindingChain…` works because of `open CondensedMatter`. Placeholders: `(T : TightBindingChain)`,
`(k : T.QuantaWaveNumber)`, `(P : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (T.energyEigenvalue k)` | `⊢ P (T.E0 - 2 * T.t * Real.cos (↑k * T.a))` |

**R2 · `rw [show e₁ = e₂ by ring]`** changes the **goal**: `show e₁ = e₂ by ring` proves the identity on the
spot, and `rw` replaces `e₁` by `e₂`. `e₁` must appear literally in the goal: copy it from the infoview
(writing `k` for `↑k` is fine). In the exercise `e₁` is the whole expression inside `|…|` and `e₂` is minus
the product. Placeholders: `{α : Type} [CommRing α] (a b : α)` (a commutative `+`, `-`, `*`: `ℤ`, `ℝ`, `ℂ`).

| Before | After |
|---|---|
| `⊢ P (a - b - a)` | `⊢ P (-b)` |

### Absolute values

**R3 · `rw [abs_neg]`** changes the **goal**. The lemma is `abs_neg : |-a| = |a|`. Placeholders:
`{α : Type} [Lattice α] [AddGroup α] (a : α)` (an order with max/min and a group `+`; `ℝ` qualifies).

| Before | After |
|---|---|
| ⊢ P \|(-a)\| | ⊢ P \|a\| |

**R4 · `rw [abs_mul]`** changes the **goal**. The lemma is `abs_mul : |a * b| = |a| * |b|`. Since
`|x * y * z|` is `|(x * y) * z|`, the first `rw [abs_mul]` gives `|x * y| * |z|` and a second one gives
`|x| * |y| * |z|`. Placeholders: `{α : Type} [Ring α] [LinearOrder α] [IsOrderedRing α] (a b : α)` (a
ring with a total order compatible with `+` and `*`; `ℤ`, `ℚ`, `ℝ` qualify, `ℂ` does not).

| Before | After |
|---|---|
| ⊢ P \|a \* b\| | ⊢ P (\|a\| \* \|b\|) |

**R5 · `rw [abs_two]`** changes the **goal**. The lemma is `abs_two : |2| = 2`. Placeholders: as in R4.

| Before | After |
|---|---|
| ⊢ P \|2\| | `⊢ P 2` |

### Bounding a product

**R6 · `apply mul_le_of_le_one_right`** changes the **goal list**. The lemma is
`mul_le_of_le_one_right : 0 ≤ a → b ≤ 1 → a * b ≤ a`: multiplying a nonnegative `a` by a factor at most `1`
does not increase it. `apply` matches the goal against `a * b ≤ a` and leaves the two hypotheses as goals
(`case ha`, `case h`). `exact mul_le_of_le_one_right p₀ p₁` gives both proofs at once. Placeholders: as in
R4.

| Before | After |
|---|---|
| `⊢ a * b ≤ a` | `⊢ 0 ≤ a`, `⊢ b ≤ 1` |

**R7 · `positivity`** **closes** a goal `0 ≤ e` or `0 < e` when `e` is built from pieces it knows are
nonnegative: positive numerals, `|x|`, squares, and sums and products of those. It does not use hypotheses.
Use it inline for a lemma's argument: `(by positivity)`.

**R8 · `exact Real.abs_cos_le_one x`** **closes** the goal `|Real.cos x| ≤ 1`. The lemma is
`Real.abs_cos_le_one (x : ℝ) : |Real.cos x| ≤ 1`. Write `Real.abs_cos_le_one _` to let Lean find `x`.

### Worked combination (W1, on an expression that is not the exercise's)

**W1.** `|c + b * cos x - c| ≤ |b|`: R2 cancels the `c`s, R4 splits the product, and R6 closes the goal
with R7 and R8 as its two arguments:

```lean-goal
⊢ |c + b * Real.cos x - c| ≤ |b|
⊢ |b * Real.cos x| ≤ |b|
⊢ |b| * |Real.cos x| ≤ |b|
```

In the exercise there are two more steps: R3 (the `-` that R2 leaves) and a second R4 with R5 (the factor
`2`).

---

## Traps

- `rw [abs_mul]` before R2 fails: the goal is `|E0 - 2 t cos(ka) - E0|`, a difference, not a product.
  Cancel the `E0`s first.
- The `show … by ring` in R2 must match the goal exactly, including the grouping `2 * T.t * Real.cos …`.
  Copy the left side from the infoview after R1.
- `rw [abs_mul]` rewrites only the first product it finds (and every identical copy). Two nested products
  need it twice; the second application splits `|2 * T.t|`.
- `apply mul_le_of_le_one_right` needs the goal in the shape `a * b ≤ a` with the same `a` on both sides:
  `2 * |T.t| * |Real.cos …| ≤ 2 * |T.t|` works because `*` groups to the left, so `a = 2 * |T.t|`. With `|2|`
  still present (before R5), the two sides do not match.
- `positivity` proves `0 ≤ 2 * |T.t|` but not `0 ≤ T.t`: it cannot know the sign of a variable.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `T.energyEigenvalue k` → its formula | `unfold TightBindingChain.energyEigenvalue` | R1 |
| cancel `E0 - x - E0` → `-x` | `rw [show … = … by ring]` | R2 |
| `\|-x\|` → `\|x\|` | `rw [abs_neg]` | R3 |
| `\|x * y\|` → `\|x\| * \|y\|` | `rw [abs_mul]` (twice for `\|2 * t * c\|`) | R4 |
| `\|2\|` → `2` | `rw [abs_two]` | R5 |
| `a * b ≤ a` from `0 ≤ a`, `b ≤ 1` | `exact mul_le_of_le_one_right p₀ p₁` | R6 |
| `0 ≤ 2 * \|t\|` | `(by positivity)` | R7 |
| `\|Real.cos x\| ≤ 1` | `Real.abs_cos_le_one _` | R8 |
| see the state | infoview | |
