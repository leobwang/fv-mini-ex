# M141 · CHSH inequality for local hidden variables: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ`, the absolute
value `|x|`, finite sums `∑` over a finite type, and the order lemmas that move `|·|` and `≤` through
sums and products.

**The physics, in one paragraph.** A *local hidden-variable (LHV) model* explains the outcomes of a
two-party experiment by a hidden value `l` drawn from a finite set `Λ` with probability `p l`
(`p l ≥ 0`, `∑ l, p l = 1`). Alice picks a setting `x ∈ {0, 1}`, Bob a setting `y ∈ {0, 1}`, and their
outcomes `A x l, B y l ∈ {+1, −1}` depend only on their own setting and on `l` (that is *locality*). The
correlation is `Eₓᵧ = ∑ l, p l · A x l · B y l`. CHSH (Clauser–Horne–Shimony–Holt) says every LHV model
obeys `|E₀₀ + E₀₁ + E₁₀ − E₁₁| ≤ 2`; quantum mechanics reaches `2√2`, which is how experiments rule
LHV models out.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`, `exact`, `refine` or `apply`. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the proof
state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal.
- Placeholders are written as Lean binders. `{ι : Type} [Fintype ι]` is any type with finitely many
  elements (a *type class* requirement: `Fin n`, `Bool`, and the problem's `Λ` meet it).
- The lemmas hold in any linearly ordered ring (or ordered additive group); the entries state them for
  `ℝ`, the only case this problem needs.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that. A state
  containing `|` (absolute value) cannot sit in a table's code span, so it is written plainly in the table
  and repeated exactly in the `lean-goal` block below it.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers |
| `\|x\|` | `abs x`, the absolute value. Typed with the ordinary `\|` key |
| `Fintype Λ` | `Λ` is a finite type, so sums over all of it make sense |
| `∑ l, f l` | the sum of `f l` over every `l : Λ`; it is `∑ l ∈ Finset.univ, f l` |
| `Finset.univ` | the finite set of all elements of a `Fintype` |
| `∑ i ∈ s, f i` | the sum over a finite set `s` (lemma statements are written this way) |
| `∀ x ∈ s, P x` | `∀ x, x ∈ s → P x`: a proof takes two arguments, `fun x hx => …` |
| `A B : Fin 2 → Λ → ℝ` | outcome tables: `A x l` is Alice's outcome for setting `x : Fin 2 = {0, 1}` and hidden value `l` |
| `(∑ i, f i) * a` | the whole sum times `a`; without brackets `∑ i, f i * a` sums the products |
| `1 * -1`, `x - -1 * -1` | how Lean prints `1 * (-1)` and `x - ((-1) * (-1))`: unary minus binds tighter than `*`, `*` tighter than `-` |
| `inst✝ : Fintype Λ` | the unnamed instance from the binder `[Fintype Λ]`; you never refer to it |
| `a✝ : i ∈ Finset.univ` | an unnamed hypothesis (from `intro i _`); you cannot refer to it, and you do not need to |
| `case inl.inr` | the goal where the first `rcases` took the left side (`inl`) and the second the right (`inr`) |

---

## Part 1 · `chsh_lhv`

Statement: for weights `p l ≥ 0` with `∑ l, p l = 1` and outcomes `A x l, B y l ∈ {1, −1}`,
`|∑ l, p l * (A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁)| ≤ 2` (subscripts: `A₀ = A 0 l`, etc.). It splits into a
**pointwise** bound for one `l` (step 1 of the skeleton, the fact `pt`) and an **averaging** estimate
(step 2, a `calc` chain).

Why the pointwise bound holds: `A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁ = A₀(B₀ + B₁) + A₁(B₀ − B₁)`. Since
`B₀, B₁ = ±1`, one bracket is `0` and the other is `±2`, so the total is `±2`. Lean does not need the
algebra: it checks all `2⁴ = 16` sign patterns.

### Step 1 · the pointwise bound `pt`: case split on ±1 values

**R1 · `rcases h with h | h`** changes the **goal list and the context**: a hypothesis `a = 1 ∨ a = -1`
becomes two goals, one with `h : a = 1` and one with `h : a = -1`. Then `rw [h]` puts the number in place
of `a`. Placeholders: `(a : ℝ) (P : ℝ → Prop)`. In the problem, the disjunction is `hA 0 l` (apply `hA`
to the setting and the hidden value first).

| Before | After |
|---|---|
| `ha : a = 1 ∨ a = -1 ⊢ P a` | `h : a = 1 ⊢ P a`, `h : a = -1 ⊢ P a` |

**R2 · `rcases ha with h | h <;> rcases hb with h' | h'`** changes the **goal list**: `t <;> u` runs `u` on
every goal `t` leaves, so two splits give 2 × 2 = 4 goals, and four splits give 16. Give each split its own
names (`h1`…`h4`) so the `rw` that follows can name all of them. Placeholders: `(a b : ℝ)
(P : ℝ → ℝ → Prop)`.

| Before | After |
|---|---|
| `ha : a = 1 ∨ a = -1, hb : b = 1 ∨ b = -1 ⊢ P a b` | `h : a = 1, h' : b = 1 ⊢ P a b`, `h : a = 1, h' : b = -1 ⊢ P a b`, `h : a = -1, h' : b = 1 ⊢ P a b`, `h : a = -1, h' : b = -1 ⊢ P a b` |

**R3 · `abs_le`** changes the **goal**. The lemma is `abs_le : |a| ≤ b ↔ -b ≤ a ∧ a ≤ b`: a bound on an
absolute value is two inequalities. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| ⊢ \|a\| ≤ b | `⊢ -b ≤ a ∧ a ≤ b` |

```lean-goal
⊢ |a| ≤ b
```

**R4 · `norm_num [abs_le]`** **closes** a goal made of numerals with an `|·|` bound: R3 turns it into two
numeric inequalities and `norm_num` evaluates both. After R2 and `rw [h1, h2, h3, h4]`, each of the 16
goals has this shape (for example `|1 * 1 + 1 * -1 + -1 * 1 - -1 * -1| ≤ 2`).

| Before | After |
|---|---|
| ⊢ \|1 \* -1 + -1 \* 1 + 3\| ≤ 2 | no goals |

```lean-goal
⊢ |1 * -1 + -1 * 1 + 3| ≤ 2
```

**W1** (guide) runs R2, `rw [h, h']` and R4 on `|a + a * b| ≤ 2`. After the `rw` the four goals are:

```lean-goal
⊢ |1 + 1 * 1| ≤ 2
⊢ |1 + 1 * -1| ≤ 2
⊢ |-1 + -1 * 1| ≤ 2
⊢ |-1 + -1 * -1| ≤ 2
```

### Step 2 · averaging over `l`: a `calc` chain

**R5 · `calc`** changes the **goal list**: it proves `a ≤ c` through a chain of steps, each with its own
proof. A `≤` step followed by `=` steps chains to `≤`. On the first line, `_` stands for the goal's left
side, so you need not retype it; every later line starts with `_` (the previous right side) and must
write its own right side out in full. Placeholders: `(a b c : ℝ)`. The guide uses `?_` to show the goals;
in the problem each `:=` is followed by its proof term directly.

| Before | After |
|---|---|
| `⊢ a ≤ c` | `⊢ a ≤ b`, `⊢ b = c` |

The four steps for this problem: `|∑ l, p l * X l| ≤ ∑ l, |p l * X l| = ∑ l, p l * |X l| ≤ ∑ l, p l * 2 = 2`,
where `X l` is the bracket `A 0 l * B 0 l + … - A 1 l * B 1 l`.

**R6 · `Finset.abs_sum_le_sum_abs`** **closes** the first step. The lemma is
`Finset.abs_sum_le_sum_abs f s : |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i|`, the triangle inequality for finite sums.
Write `Finset.abs_sum_le_sum_abs _ _` and Lean finds `f` and `s` from the goal. Placeholders:
`{ι : Type} [Fintype ι] (f : ι → ℝ)`.

| Before | After |
|---|---|
| ⊢ \|∑ i, f i\| ≤ ∑ i, \|f i\| | no goals |

```lean-goal
⊢ |∑ i, f i| ≤ ∑ i, |f i|
```

**R7 · `Finset.sum_congr rfl`** changes the **goal**: two sums over the same set are equal when the terms
are. The lemma is `Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`; `rfl` proves
`s₁ = s₂` (both are `Finset.univ`; `s.sum f` is another way to write `∑ x ∈ s, f x`). Then `intro i _` (or the term `fun i _ => …`) gives you one term.
Placeholders: `{ι : Type} [Fintype ι] (f g : ι → ℝ)`.

| Before | After `refine Finset.sum_congr rfl ?_` | After `intro i _` |
|---|---|---|
| `⊢ ∑ i, f i = ∑ i, g i` | `⊢ ∀ x ∈ Finset.univ, f x = g x` | `i : ι, a✝ : i ∈ Finset.univ ⊢ f i = g i` |

**R8 · `abs_mul`** changes the **goal**. The lemma is `abs_mul a b : |a * b| = |a| * |b|`.
Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| ⊢ P \|a \* b\| | ⊢ P (\|a\| \* \|b\|) |

```lean-goal
⊢ P |a * b|
⊢ P (|a| * |b|)
```

**R9 · `abs_of_nonneg`** changes the **goal**. The lemma is `abs_of_nonneg : 0 ≤ a → |a| = a`. Give it the
proof: `rw [abs_of_nonneg (hp l)]` with `hp l : 0 ≤ p l`. Placeholders: `(a : ℝ) (ha : 0 ≤ a)`.

| Before | After |
|---|---|
| ⊢ P \|a\| | `⊢ P a` |

```lean-goal
⊢ P |a|
```

So the second `calc` step is R7, then in each term R8 and R9: `|p l * X l|` → `|p l| * |X l|` →
`p l * |X l|`.

**R10 · `Finset.sum_le_sum`** changes the **goal**: a sum is at most another when each term is. The lemma
is `Finset.sum_le_sum : (∀ i ∈ s, f i ≤ g i) → ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i`. Placeholders:
`{ι : Type} [Fintype ι] (f g : ι → ℝ)`.

| Before | After `refine Finset.sum_le_sum ?_` | After `intro i _` |
|---|---|---|
| `⊢ ∑ i, f i ≤ ∑ i, g i` | `⊢ ∀ i ∈ Finset.univ, f i ≤ g i` | `i : ι, a✝ : i ∈ Finset.univ ⊢ f i ≤ g i` |

**R11 · `mul_le_mul_of_nonneg_left`** changes the **goal list**: to bound `a * b ≤ a * c` it asks for
`b ≤ c` and `0 ≤ a`. The lemma is `mul_le_mul_of_nonneg_left : b ≤ c → 0 ≤ a → a * b ≤ a * c`; as a term,
pass the bound first and the sign second: `mul_le_mul_of_nonneg_left (pt l) (hp l)`. Placeholders:
`(a b c : ℝ)`.

| Before | After `apply mul_le_mul_of_nonneg_left` |
|---|---|
| `⊢ a * b ≤ a * c` | `⊢ b ≤ c`, `⊢ 0 ≤ a` |

So the third `calc` step is R10, then in each term R11 with `pt l` from step 1: `p l * |X l| ≤ p l * 2`.

**R12 · `rw [← Finset.sum_mul]`** changes the **goal**. The lemma is
`Finset.sum_mul s f a : (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a`; right to left (`←`) it factors a constant
out of every term. Placeholders: `{ι : Type} [Fintype ι] (f : ι → ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i * a)` | `⊢ P ((∑ i, f i) * a)` |

**R13 · `rw [one_mul]`** changes the **goal**. The lemma is `one_mul a : 1 * a = a`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (1 * a)` | `⊢ P a` |

So the last `calc` step is R12, then `rw [hsum]` (`∑ l, p l` → `1`; after R12 the infoview may print the
sum as `∑ i, p i`, which is the same term, so `rw [hsum]` still matches), then R13: `∑ l, p l * 2` →
`(∑ l, p l) * 2` → `1 * 2` → `2`. The `rw` closes the goal itself once both sides are `2 = 2`.

**W2** (guide) runs the whole chain on a different statement: a weighted average of numbers `s i` with
`|s i| ≤ 1` has absolute value at most 1. It starts from

```lean-goal
⊢ |∑ i, q i * s i| ≤ 1
```

---

## Traps

- Prove `pt` **before** the `calc`: the third step needs `pt l` for each `l`. State it with `∀ l` and start
  its proof with `intro l`, then split `hA 0 l`, `hA 1 l`, `hB 0 l`, `hB 1 l`.
- Chain the four `rcases`, the `rw` and `norm_num` with `<;>`. `t1 ; t2` (or a new line) runs `t2` on the
  first goal only, and the other 15 are left open.
- `rw [h1, h2, h3, h4]` needs all four names to exist in every case: give each `rcases` the same names on
  both sides (`with h1 | h1`).
- `∀ i ∈ s, P i` is `∀ i, i ∈ s → P i`: the term after `Finset.sum_congr rfl` or `Finset.sum_le_sum` is
  `fun l _ => …` with **two** arguments. `fun l => …` is a type error.
- In `calc`, only the first left side may be `_`. The right sides must be written out, and each must match
  the next line's start exactly; the `…` in the hints is not Lean.
- `Finset.sum_mul` goes the other way from what you need: write `rw [← Finset.sum_mul]` to turn
  `∑ l, p l * 2` into `(∑ l, p l) * 2`, so that `rw [hsum]` finds `∑ l, p l`.
- `mul_le_mul_of_nonneg_left` takes the bound `b ≤ c` first and the sign `0 ≤ a` second.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| fact for every `l` first | `have pt : ∀ l, … := by intro l; …` | TACTIC_STATES |
| split `a = 1 ∨ a = -1` | `rcases h with h1 \| h1` | R1 |
| all 16 sign patterns | `rcases … <;> rcases … <;> … <;> rw [h1, h2, h3, h4] <;> norm_num [abs_le]` | R2, R4 |
| `\|a\| ≤ b` → two inequalities | `rw [abs_le]` | R3 |
| chain `≤` and `=` steps | `calc _ ≤ … := … ` / `_ = … := …` | R5 |
| `\|∑ f\| ≤ ∑ \|f\|` | `Finset.abs_sum_le_sum_abs _ _` | R6 |
| sums equal termwise | `Finset.sum_congr rfl fun l _ => by …` | R7 |
| `\|a * b\|` → `\|a\| * \|b\|` | `rw [abs_mul]` | R8 |
| `\|a\|` → `a` when `0 ≤ a` | `rw [abs_of_nonneg ha]` | R9 |
| sums `≤` termwise | `Finset.sum_le_sum fun l _ => …` | R10 |
| `a * b ≤ a * c` from `b ≤ c`, `0 ≤ a` | `mul_le_mul_of_nonneg_left hbc ha` | R11 |
| factor a constant out of a sum | `rw [← Finset.sum_mul]` | R12 |
| `1 * a` → `a` | `rw [one_mul]` | R13 |
| see the state | infoview | |
