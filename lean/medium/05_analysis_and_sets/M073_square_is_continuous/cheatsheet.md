# M073 · x² is continuous (ε-δ): cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ`, absolute value
`|x|`, `min`, and the inequality tactics `positivity`, `linarith`, `gcongr`, `field_simp`; `calc` chains.
Mathlib's own `Continuous` and filters are banned: you build `δ` by hand.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. A bare `P : Prop` is "whatever the goal is" in entries that only add a fact.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[LinearOrder α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it; `ℝ` meets all of them.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers (a complete ordered field; not floating point) |
| `\|x\|` | `abs x`, the absolute value `max x (-x)` |
| `min b c` | the smaller of `b` and `c` |
| `ContAt f x` | the exercise's definition: for every `ε > 0` there is `δ > 0` with `\|y - x\| < δ → \|f y - f x\| < ε` for all `y` |
| `∀ ε > 0, Q ε` | `∀ ε, ε > 0 → Q ε`: `intro` takes two names (R1) |
| `∃ δ > 0, G δ` | `∃ δ, δ > 0 ∧ G δ`: a witness plus two proofs (R2) |
| `ε > 0` | `0 < ε` (`>` is notation for `<` with the sides swapped) |
| `(fun x => x ^ 2) y - (fun x => x ^ 2) a` | `f y - f a` with `f = (x ↦ x²)` substituted but not yet simplified to `y ^ 2 - a ^ 2` (R4) |
| `ε / (2 * \|a\| + 1)` | real division (exact, not truncating as on `ℕ`); Lean sets `x / 0 = 0`, so lemmas about `/` need the denominator `≠ 0` (R15) |
| `x ^ 2` | `x` to the natural-number power `2` (`Monoid.npow`) |
| `case refine_1`, `case hbc` | names Lean gives the goals that `refine` or `gcongr` create |

---

## Part 1 · `sq_contAt`

Statement: for every real `a`, `ContAt (fun x => x ^ 2) a`, i.e. for every `ε > 0` there is a `δ > 0` such that
`|y - a| < δ` implies `|y ^ 2 - a ^ 2| < ε`. The math: `|y² - a²| = |y - a| · |y + a|`; if `|y - a| < 1` then
`|y + a| = |(y - a) + 2a| ≤ |y - a| + 2|a| ≤ 2|a| + 1`; so `δ = min 1 (ε / (2|a| + 1))` gives
`|y² - a²| < (ε / (2|a| + 1)) · (2|a| + 1) = ε`.

### Opening the ε-δ statement

**R1 · `intro ε hε`** changes the **goal and the context**. `intro` unfolds a definition by itself when its body
starts with `∀`, so `ContAt f a` needs no `unfold` first. `∀ ε > 0, Q ε` is two binders: `ε : ℝ` and
`hε : ε > 0`. Placeholders: `(Q : ℝ → Prop)`, and `AllPos Q := ∀ ε > 0, Q ε` as the named definition.

| Before | After |
|---|---|
| `⊢ AllPos Q` | `ε : ℝ, hε : ε > 0 ⊢ Q ε` |

**R2 · `refine ⟨d, ?_, fun y hy => ?_⟩`** changes the **goal list**: the witness `d` is chosen, and two goals are
left: `d > 0`, and the conclusion for an arbitrary `y` with `hy`. `∃ δ > 0, G δ` is `∃ δ, δ > 0 ∧ G δ`, and the
anonymous constructor flattens the nesting, so one `⟨…⟩` fills all three parts. You may replace the first `?_` by
`by positivity` (R3) to close it on the spot. Placeholders: `(d : ℝ) (R : ℝ → ℝ → Prop) (S : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ ∃ δ > 0, ∀ (y : ℝ), R δ y → S y` | `⊢ d > 0`, `y : ℝ, hy : R d y ⊢ S y` |

**R3 · `positivity`** **closes** a goal `0 < e`, `e > 0`, `0 ≤ e` or `e ≠ 0` when `e` is built from pieces it knows
are positive or nonnegative: numerals, `|b| ≥ 0`, `+`, `*`, `/`, `min`, and atoms with a hypothesis such as
`hε : ε > 0`. Placeholders: `(ε b : ℝ)`.

With `hε : ε > 0` in the context, before (then closed; a goal block: a table cell cannot hold the `|` of `|x|` in code):

```lean-goal
⊢ min 2 (ε / (|b| + 3)) > 0
```

**R4 · `beta_reduce`** changes the **goal**: `(fun x => t x) y` becomes `t y` (β-reduction: substitute the
argument into the function body). Optional: a `calc` whose first term is written `|y ^ 2 - a ^ 2|` matches the
unreduced goal anyway (the same term up to β-reduction); `rw` patterns may not.
Placeholders: `(f : ℝ → ℝ) (y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((fun x => f x ^ 3) y)` | `⊢ P (f y ^ 3)` |

### Using `|y - a| < min b c`

**R5 · `min_le_left`, `min_le_right`** change the **context** (via `have`). Statements:
`min_le_left a b : min a b ≤ a`, `min_le_right a b : min a b ≤ b`. Placeholders: `{α : Type} [LinearOrder α] (a b : α)`
(α is totally ordered; `ℝ`, `ℕ`, `ℤ` qualify). Pass `_ _` and Lean finds `a`, `b` from the expected type.

| Before | After |
|---|---|
| `⊢ P` | `ha : min a b ≤ a, hb : min a b ≤ b ⊢ P` |

**R6 · `lt_of_lt_of_le`** changes the **context** (via `have`). Statement: `lt_of_lt_of_le : x < m → m ≤ b → x < b`
(strict then weak gives strict). Placeholders: `{α : Type} [Preorder α] (x m b : α)` (α has `≤` and `<`; `ℝ`
qualifies). With `m = min b c`, `lt_of_lt_of_le hy (min_le_left _ _)` turns `hy : |y - a| < min b c` into `|y - a| < b`.

| Before | After |
|---|---|
| `hx : x < m, hm : m ≤ b ⊢ P` | `h1 : x < b ⊢ P` |

### Chains of (in)equalities

**R7 · `calc`** changes the **goal list**: one goal `a < d` becomes one goal per step. Syntax:

```
calc a = b := proof₁
  _ ≤ c := proof₂
  _ < d := proof₃
```

`_` stands for the previous right-hand side; the steps line up under each other, indented past `calc`. Mixing
`=`, `≤`, `<` gives `<` as soon as one step is strict. Normally each `proofᵢ` is `by …` or a term; with
`refine calc … := ?_` the steps stay open as goals, as in the guide. A `calc` can also prove a `have`. The first
term must match the goal's left side up to definitions and β-reduction. Placeholders: `(a b c d : ℝ)`.

| Before | After |
|---|---|
| `⊢ a < d` | `⊢ a = b`, `⊢ b ≤ c`, `⊢ c < d` |

**R8 · `ring_nf` under `|·|`** changes the **goal** (and closes it when both sides become the same). `ring`
cannot prove `|u - v| = |(u + v) - 2 * v|` on its own, because it treats `|·|` as an unknown function; it then
falls back to `ring_nf` and prints "Try this: ring_nf", so write `ring_nf` directly. `ring_nf`
normalises every ring expression, including the arguments of `|·|`, so both sides become `|u - v|` and the
goal closes. Also used after `rw [← abs_mul]`: the two sides then differ only inside `|·|`. Placeholders: `(u v : ℝ)`.

Before, then after (a goal block: a table cell cannot hold the `|` of `|x|` in code):

```lean-goal
⊢ P |u + v - 2 * v|
⊢ P |u - v|
```

### Absolute values

**R9 · `abs_add_le`** changes the **context** (via `have`), or is a `calc` step on its own
(`_ ≤ |a| + |b| := abs_add_le _ _`). Statement: `abs_add_le a b : |a + b| ≤ |a| + |b|` (triangle inequality).
Placeholders: `(a b : ℝ)`; in general `{α : Type} [Lattice α] [AddCommGroup α] [AddLeftMono α]`, an ordered
additive group such as `ℝ` or `ℤ`.

| Before | After |
|---|---|
| `⊢ P` | `⊢ P`, and the context gains `ht` |

where `ht : |a + b| ≤ |a| + |b|`.

**R10 · `rw [abs_mul]`** changes the **goal**. Statement: `abs_mul a b : |a * b| = |a| * |b|`. Right to left,
`rw [← abs_mul]` merges `|a| * |b|` into `|a * b|`. Placeholders:
`{α : Type} [Ring α] [LinearOrder α] [IsOrderedRing α] (a b : α)` (a totally ordered ring; `ℝ`, `ℤ` qualify).

Before, then after (a goal block: a table cell cannot hold the `|` of `|x|` in code):

```lean-goal
⊢ P |a * b|
⊢ P (|a| * |b|)
```

**R11 · `rw [abs_two]`** changes the **goal**. Statement: `abs_two : |2| = 2`. Use it after `abs_mul` splits
`|2 * a|` into `|2| * |a|`. Placeholders: as R10, `(b : α)`.

Before, then after (a goal block: a table cell cannot hold the `|` of `|x|` in code):

```lean-goal
⊢ P (|2| * b)
⊢ P (2 * b)
```

### Closing inequalities

**R12 · `linarith`** **closes** a goal `t ≤ s`, `t < s`, `t = s` (or `False`) that follows from the hypotheses by
adding up linear inequalities. Nonlinear pieces such as `|t|` or `x * y` are treated as unknown atoms.
Placeholders: `(t c : ℝ)`.

With `h : |t| < 1` in the context, before (then closed):

```lean-goal
⊢ |t| + c ≤ c + 1
```

**R13 · `gcongr` on `≤`** changes the **goal**: `z * x ≤ z * y` becomes `x ≤ y` ("generalized congruence":
compare the parts that differ). The side goal `0 ≤ z` is proved by `positivity`, so `z = |t|` is fine. If a
hypothesis `x ≤ y` (or `x < y`) is in the context, `gcongr` uses it and closes the goal outright; in the guide
the hypothesis has the wrong shape, so the goal stays. Placeholders: `(t x y : ℝ)`.

Before, then after (a goal block: a table cell cannot hold the `|` of `|x|` in code):

```lean-goal
⊢ |t| * x ≤ |t| * y
⊢ x ≤ y
```

**R14 · `gcongr` on `<`** changes the **goal**: `x * c < y * c` becomes `x < y`, with the side goal `0 < c`
proved by `positivity` (so `c = |b| + 1` is fine; `c = |b|` is not). Placeholders: `(x y b : ℝ)`.

Before, then after (a goal block: a table cell cannot hold the `|` of `|x|` in code):

```lean-goal
⊢ x * (|b| + 1) < y * (|b| + 1)
⊢ x < y
```

**R15 · `field_simp`** **closes** `x / c * c = x` (and in general clears denominators) once it can show `c ≠ 0`;
it proves `|b| + 1 ≠ 0` by itself. Placeholders: `(x b : ℝ)`.

Before (then closed):

```lean-goal
⊢ x / (|b| + 1) * (|b| + 1) = x
```

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: ε-δ for `y ↦ 3 * y` at `c`, `δ = ε / 3`.** R1 then R2 (with `by positivity` for `ε / 3 > 0`):

```lean-goal
⊢ ∀ ε > 0, ∃ δ > 0, ∀ (y : ℝ), |y - c| < δ → |3 * y - 3 * c| < ε
⊢ ∃ δ > 0, ∀ (y : ℝ), |y - c| < δ → |3 * y - 3 * c| < ε
⊢ |3 * y - 3 * c| < ε
```

then a `calc` (R7): `= |3 * (y - c)|` by `ring_nf` (R8), `= |3| * |y - c|` by R10, `= 3 * |y - c|` by `norm_num`,
`< 3 * (ε / 3)` by `gcongr` (R14, using `hy`), `= ε` by `field_simp` (R15).

**W2: a bound from `|y - c| < min 1 (ε / 4)`.** R5 → R6 give `h1 : |y - c| < 1`; then
`calc |y| = |(y - c) + c| := by ring_nf` (R8), `_ ≤ |y - c| + |c| := abs_add_le _ _` (R9),
`_ ≤ |c| + 1 := by linarith` (R12).

---

## Traps

- The bans block Mathlib's `Continuous`/filter route (`continuous_pow`, `fun_prop`, `continuity`, `Tendsto`, …):
  the `δ` must be built by hand.
- `intro ε` alone leaves `ε > 0 → …` in the goal; `∀ ε > 0` needs two names, `intro ε hε`.
- `δ = ε / (2 * |a| + 1)` alone is not enough: the bound `|y + a| ≤ 2 * |a| + 1` needs `|y - a| < 1`, which is why
  `δ` is a `min` with `1`. Extract both halves of `hy` with R5 → R6.
- After `intro`, the goal shows `(fun x => x ^ 2) y`, not `y ^ 2`. `calc` and `gcongr` see through it; `rw`
  sometimes does not: use `beta_reduce` (R4) if a rewrite fails to find `y ^ 2`.
- `ring` cannot see inside `|·|` (it falls back to `ring_nf` with a "Try this" message); write `ring_nf` (R8),
  and in the main `calc` first merge the two factors with `rw [← abs_mul]` (R10) so both sides are one `|·|`.
- `gcongr` needs the factor that stays the same to be provably nonnegative (`≤`) or positive (`<`, on the
  multiplied side). `2 * |a| + 1` is positive, `|a|` alone is not.
- `|2 * a|` is not `2 * |a|` syntactically: `rw [abs_mul, abs_two]` (R10, R11).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| open `∀ ε > 0, …` (even under a definition) | `intro ε hε` | R1 |
| choose `δ`, get `y` and `hy` | `refine ⟨δ, by positivity, fun y hy => ?_⟩` | R2, R3 |
| `0 < e` for `e` built from positives | `positivity` | R3 |
| `(fun x => t x) y → t y` | `beta_reduce` | R4 |
| `min a b ≤ a` / `≤ b` | `min_le_left _ _` / `min_le_right _ _` | R5 |
| `x < m`, `m ≤ b` ⟹ `x < b` | `lt_of_lt_of_le hx hm` | R6 |
| chain `=`, `≤`, `<` | `calc a = b := … \n _ ≤ c := … \n _ < d := …` | R7 |
| equal up to ring algebra inside `\|·\|` | `ring_nf` | R8 |
| triangle inequality | `abs_add_le a b : \|a + b\| ≤ \|a\| + \|b\|` | R9 |
| split / merge `\|a * b\|` | `rw [abs_mul]` / `rw [← abs_mul]` | R10 |
| `\|2\| → 2` | `rw [abs_two]` | R11 |
| linear inequality from hypotheses | `linarith` | R12 |
| `z * x ≤ z * y` from `x ≤ y` | `gcongr` | R13 |
| `x * c < y * c` from `x < y`, `c > 0` | `gcongr` | R14 |
| `x / c * c = x` | `field_simp` | R15 |
| see the state | infoview | |
