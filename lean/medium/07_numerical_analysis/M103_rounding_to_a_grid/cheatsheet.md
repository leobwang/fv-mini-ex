# M103 · Rounding to a grid: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ`, `round`,
absolute value `|·|`, integer powers (`zpow`) `2 ^ (k : ℤ)`, the cast `ℕ → ℤ`, and the tactics
`field_simp`, `nlinarith`, `positivity`, `gcongr`, `calc`.

**The maths.** Grid `hℤ = {…, -h, 0, h, 2h, …}` for a spacing `h > 0`; `roundTo h x = h · round(x / h)`
is its point nearest to `x`, where `round y ∈ ℤ` is the integer nearest to `y` (ties go up), so
`|y - round y| ≤ 1/2`. A float with `p` fraction bits and exponent `e` lies in the *binade* `[2^e, 2^(e+1))`
on the grid of spacing `2^(e-p)`. The *relative error* of `x ↦ x̂` is `δ = (x̂ - x)/x`, i.e. `x̂ = x(1 + δ)`;
the bound `u = 2^(-p-1)` is the *unit roundoff*.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is a goal the step does not touch.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Field α]` is a
  requirement on `α` (a *type class*). `[Field α] [LinearOrder α] [IsStrictOrderedRing α]` together say
  "α is an ordered field" (`<`, `≤` compatible with `+`, `*`); ℚ and ℝ qualify.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that. A state
  containing `|·|` cannot sit in a code cell of a Markdown table, so those entries repeat it in a
  `lean-goal` block, which is checked.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ`, `ℤ`, `ℕ` | real numbers, integers, natural numbers |
| `round y` | `round : ℝ → ℤ`, the integer nearest `y`; `round 2.5 = 3` |
| `↑(round y)` | that integer cast back into `ℝ` (the up-arrow `↑` is a coercion between number types) |
| `↑p` with `p : ℕ` | `p` cast into `ℤ` (in `e - ↑p`) or into `ℝ`, depending on the surrounding type |
| `\|a\|` | absolute value `abs a`; `\|(-a)\|` is `\|-a\|` printed with brackets |
| `2 ^ (e - ↑p)` | an integer power (`zpow`): the exponent is in `ℤ`, so `2 ^ (-1) = 1 / 2` |
| `-↑p - 1` | the integer `-p - 1`; `2 ^ (-↑p - 1)` is the unit roundoff `u` |
| `x / h` | real division; Mathlib sets `x / 0 = 0`, which is why lemmas ask for `h ≠ 0` or `0 < h` |
| `case refine_1`, `case hbc` | names Lean gives to the goals a tactic creates |

---

## Part 1 · `roundTo_error`

Statement: for `h > 0`, `|roundTo h x - x| ≤ h / 2`. In words: the error of rounding to the grid is `h`
times the error of rounding `x / h` to an integer, and the latter is at most `1/2`.

Plan: prove `roundTo h x - x = -(h * (x / h - round (x / h)))` (R1, R2, `ring`), rewrite with it, peel the
absolute value (R3, R4, R5), finish with the rounding bound (R6, R7).

**R1 · `unfold D`** changes the **goal**: a defined name is replaced by its body. Placeholders: `D` defined
by `noncomputable def snap (y : ℝ) : ℝ := 3 * round y` (`noncomputable`: ℝ arithmetic cannot be run, only
reasoned about), `(y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (snap y)` | `⊢ P (3 * ↑(round y))` |

**R2 · `field_simp`** changes the **goal**: it multiplies out every division by a quantity it can show is
nonzero (from hypotheses such as `hc : 0 < c` or `hc : c ≠ 0`), leaving an equation without `/`. It may
reorder factors. Follow it with `ring`. Placeholders: `(a b c : ℝ) (hc : 0 < c)`.

| Before | After |
|---|---|
| `⊢ a / c = b` | `⊢ a = c * b` |

**R3 · `rw [abs_neg]`** changes the **goal**. Lemma: `abs_neg (a : α) : |-a| = |a|`. Placeholders:
`{α : Type}`, an ordered field, `(a : α)`.

| Before | After |
|---|---|
| ⊢ P \|(-a)\| | ⊢ P \|a\| |

```lean-goal
⊢ P |(-a)|
⊢ P |a|
```

**R4 · `rw [abs_mul]`** changes the **goal**. Lemma: `abs_mul (a b : α) : |a * b| = |a| * |b|`.
Placeholders: `{α : Type}`, an ordered field, `(a b : α)`.

| Before | After |
|---|---|
| ⊢ P \|a * b\| | ⊢ P (\|a\| * \|b\|) |

```lean-goal
⊢ P |a * b|
⊢ P (|a| * |b|)
```

**R5 · `rw [abs_of_pos ha]`** changes the **goal**. Lemma: `abs_of_pos : 0 < a → |a| = a`. Pass the proof
`ha : 0 < a` so `rw` knows which `|a|` to remove. Placeholders: `{α : Type}`, an ordered field,
`(a : α) (ha : 0 < a)`.

| Before | After |
|---|---|
| ⊢ P \|a\| | ⊢ P a |

```lean-goal
⊢ P |a|
⊢ P a
```

**R6 · `abs_sub_round`** changes the **context** (used with `have`, or as a hint to R7). Lemma:
`abs_sub_round (y : α) : |y - round y| ≤ 1 / 2`. Placeholders: `{α : Type}`, an ordered field with
`[FloorRing α]` (α has `⌊·⌋`, hence `round`; ℚ and ℝ do), `(y : α)`.

| Before | After `have hr := abs_sub_round y` |
|---|---|
| ⊢ G | hr : \|y - ↑(round y)\| ≤ 1 / 2 ⊢ G |

**R7 · `nlinarith [t₁, …]`** **closes** an inequality over an ordered field. It adds the hint terms `tᵢ` to
the hypotheses, multiplies pairs of them, then runs linear arithmetic (`linarith`). Use it when the goal
needs a product of two facts, such as `0 < a` times `b ≤ 1/2`. A hint can be a lemma applied to
arguments (`abs_sub_round y`), so the fact need not be in the context. In the guide:
`(a t : ℝ) (f : ℝ → ℝ) (ha : 0 < a) (hf : ∀ s, f s ≤ 3)`.

| Before | After `nlinarith [hf t]` |
|---|---|
| `⊢ a * f t ≤ 3 * a` | no goals |

---

## Part 2 · `binade_relative_error`

Statement: for `p : ℕ`, `e : ℤ` and `x ≥ 2^e`, some `δ` has `|δ| ≤ 2^(-p-1)` and
`roundTo (2^(e-p)) x = x * (1 + δ)`. In words: rounding to the float grid of the binade has relative error at
most the unit roundoff.

Plan: `0 < x` first (R8, R9); witness `δ := (roundTo (2 ^ (e - p)) x - x) / x` (R10); the equation (the
second goal) by R2 and `ring`, written as a `by …` block in place of its `?_`; the bound: Part 1 at `h = 2^(e-p)` (R11), clear `|·|` and `/ x` (R12, R5, R13), then show
`2^(e-p) / 2 = 2^(-p-1) * 2^e` (R14–R17) and chain (R18, R19).

**R8 · `lt_of_lt_of_le`** **closes** `a < c` as a term. Lemma: `lt_of_lt_of_le : a < b → b ≤ c → a < c`.
Placeholders: `{α : Type} [Preorder α]` (any type with `≤`, `<`), `(a b c : α)`. Arguments may be
`(by tac)`, as in `lt_of_lt_of_le (by positivity) hx`.

| Before | After `exact lt_of_lt_of_le hab hbc` |
|---|---|
| `⊢ a < c` | no goals |

**R9 · `positivity`** **closes** `0 < t`, `0 ≤ t` or `t ≠ 0` when `t` is built from positive pieces:
numerals, powers `2 ^ k` (any exponent `k : ℤ`, since the base `2` is positive), products, quotients and
hypotheses `0 < y`. Placeholders: `(k : ℤ) (y : ℝ) (hy : 0 < y)`.

| Before | After |
|---|---|
| `⊢ 0 < 2 ^ k * y` | no goals |

**R10 · `refine ⟨w, ?_, ?_⟩`** changes the **goal list**: it picks the witness `w` of `∃ δ, A δ ∧ B δ` and
leaves one goal per conjunct. One flat `⟨…⟩` covers both the `∃` and the `∧`. Write a proof instead of a
`?_` to close that part on the spot. Placeholders: `(A B : ℝ → Prop) (w : ℝ)`.

| Before | After |
|---|---|
| `⊢ ∃ δ, A δ ∧ B δ` | `⊢ A w`, `⊢ B w` |

**R11 · `have hk := thm args (by tac)`** changes the **context**: it applies a theorem already proved (here
an assumption `hf`; in the exercise, `roundTo_error`) to arguments, and `(by positivity)` proves its
`0 < _` argument. Placeholders: `(f : ℝ → ℝ) (hf : ∀ s : ℝ, 0 < s → f s ≤ s / 2) (k : ℤ)`.

| Before | After `have hk := hf (2 ^ k) (by positivity)` |
|---|---|
| `⊢ G` | `hk : f (2 ^ k) ≤ 2 ^ k / 2 ⊢ G` |

**R12 · `rw [abs_div]`** changes the **goal**. Lemma: `abs_div (a b : α) : |a / b| = |a| / |b|`.
Placeholders: `{α : Type}`, an ordered field, `(a b : α)`.

| Before | After |
|---|---|
| ⊢ P \|a / b\| | ⊢ P (\|a\| / \|b\|) |

```lean-goal
⊢ P |a / b|
⊢ P (|a| / |b|)
```

**R13 · `rw [div_le_iff₀ hc]`** changes the **goal**: a division on the left of `≤` becomes a
multiplication on the right. Lemma: `div_le_iff₀ : 0 < c → (b / c ≤ a ↔ b ≤ a * c)`; `rw` with an `↔`
replaces the whole goal. Placeholders: `{α : Type}`, an ordered field, `(a b c : α) (hc : 0 < c)`.

| Before | After |
|---|---|
| `⊢ b / c ≤ a` | `⊢ b ≤ a * c` |

**R14 · `rw [show s = t by ring]`** changes the **goal**: it proves the equation `s = t` on the spot and
rewrites with it. Use it to put an exponent into the shape a lemma needs, here `… + 1` for R15 and R17.
Write casts explicitly in `s`: `(n : ℤ)`. Placeholders: `(m : ℤ) (n : ℕ)`.

| Before | After `rw [show m + (n : ℤ) = m - 1 + (n + 1) by ring]` |
|---|---|
| `⊢ P (m + ↑n)` | `⊢ P (m - 1 + (↑n + 1))` |

**R15 · `rw [zpow_add₀ ha]`** changes the **goal**. Lemma:
`zpow_add₀ : a ≠ 0 → ∀ m n : ℤ, a ^ (m + n) = a ^ m * a ^ n`. `+` groups to the left, so `m + n + 1` splits
off the last `1` first; a second `rw` splits again. Placeholders: `{α : Type} [GroupWithZero α]` (α has `*`,
`0`, `⁻¹` with `a * a⁻¹ = 1` for `a ≠ 0`; ℚ, ℝ, ℂ qualify), `(a : α) (ha : a ≠ 0) (m n : ℤ)`.

| Before | After |
|---|---|
| `⊢ P (a ^ (m + n))` | `⊢ P (a ^ m * a ^ n)` |

**R16 · `two_ne_zero`** **closes** `(2 : α) ≠ 0` as a term; it is the argument of R15 for base 2:
`rw [zpow_add₀ two_ne_zero]`.

**R17 · `rw [zpow_one]`** changes the **goal**. Lemma: `zpow_one (a : α) : a ^ (1 : ℤ) = a`. The infoview
prints `a ^ (1 : ℤ)` as `a ^ 1`. Placeholders: `{α : Type} [GroupWithZero α] (a : α)`.

| Before | After |
|---|---|
| `⊢ P (a ^ 1)` | `⊢ P a` |

**R18 · `calc`** **closes** `a ≤ d` from a chain of links `_ ≤ b`, `_ = c`, `_ ≤ d`, each with its own proof
after `:=`. The first `_` is the left side of the goal; each later `_` is the right side of the line above.
Mixing `≤`, `=` and `<` is allowed. Placeholders: `(a b c d : ℝ) (h1 : a ≤ b) (h2 : b = c) (h3 : c ≤ d)`.

| Before | After |
|---|---|
| `⊢ a ≤ d` | no goals |

**R19 · `gcongr`** changes the **goal**: for `c * a ≤ c * b` it proves the side condition `0 ≤ c` itself (by
`positivity`) and leaves `a ≤ b`. If `a ≤ b` is a hypothesis, it closes the goal outright.
Placeholders: `(a b : ℝ) (k : ℤ)`.

| Before | After |
|---|---|
| `⊢ 2 ^ k * a ≤ 2 ^ k * b` | `⊢ a ≤ b` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: a relative-error witness.** For `0 < x`, `y = x * (1 + (y - x) / x)`. R2, then `ring`:

```lean-goal
⊢ y = x * (1 + (y - x) / x)
⊢ y = x + (y - x)
```

**W2: splitting an integer exponent.** `2^(k+1) / 4 = 2^(k-1)`. R14, then R15 twice with R16 and R17, then
`ring`:

```lean-goal
⊢ 2 ^ (k + 1) / 4 = 2 ^ (k - 1)
⊢ 2 ^ (k - 1 + 1 + 1) / 4 = 2 ^ (k - 1)
⊢ 2 ^ (k - 1) * 2 * 2 / 4 = 2 ^ (k - 1)
```

**W3: bounding a quotient by a power of 2.** From `hr : |r| ≤ 2 ^ k / 4` and `hk : 2 ^ k ≤ x`, get
`|r / x| ≤ 1/4`. `rw [abs_div, abs_of_pos hx, div_le_iff₀ hx]` (R12, R5, R13), then a `calc`
`_ ≤ 2 ^ k / 4 = 1 / 4 * 2 ^ k ≤ 1 / 4 * x` with `hr`, `ring`, `gcongr` (R18, R19):

```lean-goal
⊢ |r / x| ≤ 1 / 4
⊢ |r| ≤ 1 / 4 * x
```

---

## Traps

- `rw [div_le_iff₀ hc]` and `field_simp` need the denominator to be nonzero: have `hx0 : 0 < x` in the
  context **before** using them. Prove it first, from `hx : 2 ^ e ≤ x` (R8, R9).
- `2 ^ (e - p)` mixes types: `e : ℤ`, `p : ℕ`, base in `ℝ`. Lean inserts `↑p : ℤ`. In a `show s = t by ring`
  write `(p : ℤ)` explicitly so `s` is an integer expression that matches the goal's `e - ↑p` exactly;
  otherwise `rw` reports that it cannot find the pattern.
- `zpow` lemmas end in `₀` (`zpow_add₀`) and need `a ≠ 0`: `a ^ (m + n) = a ^ m * a ^ n` fails at `a = 0`,
  `m = 1`, `n = -1` (`0 ^ 0 = 1` but `0 ^ 1 * 0 ^ (-1) = 0`).
- `ring` treats `↑(round y)` and `2 ^ (e - ↑p)` as unknowns. It cannot merge `2 ^ m * 2 ^ n`; split
  exponents with R15 first.
- `linarith` cannot multiply two hypotheses; when the bound is `h * |…| ≤ h / 2`, use `nlinarith` with the
  rounding bound as a hint (R7).
- A theorem proved earlier in the file can be used in a later proof by name (R11).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| see a definition's body | `unfold roundTo` | R1 |
| clear `/` in an equation | `field_simp` then `ring` | R2 |
| `\|-a\| → \|a\|`, `\|ab\| → \|a\|\|b\|`, `\|a/b\| → \|a\|/\|b\|` | `rw [abs_neg, abs_mul, abs_div]` | R3, R4, R12 |
| drop `\|·\|` of a positive term | `rw [abs_of_pos ha]` | R5 |
| `\|y - round y\| ≤ 1/2` | `abs_sub_round y` | R6 |
| inequality needing a product of facts | `nlinarith [fact₁, …]` | R7 |
| `a < c` from `a < b` and `b ≤ c` | `lt_of_lt_of_le hab hbc` | R8 |
| `0 < 2 ^ k`, `0 < x * y`, … | `positivity` | R9 |
| `∃ δ, A δ ∧ B δ` | `refine ⟨w, ?_, ?_⟩` | R10 |
| use an earlier theorem | `have hk := thm args (by positivity)` | R11 |
| `b / c ≤ a → b ≤ a * c` | `rw [div_le_iff₀ hc]` | R13 |
| reshape an exponent | `rw [show s = t by ring]` | R14 |
| `a ^ (m + n) → a ^ m * a ^ n` | `rw [zpow_add₀ two_ne_zero]` | R15, R16 |
| `a ^ (1 : ℤ) → a` | `rw [zpow_one]` | R17 |
| chain of `≤` / `=` | `calc _ ≤ b := h1` / `_ = c := h2` … | R18 |
| `c * a ≤ c * b` from `a ≤ b` | `gcongr` | R19 |
| see the state | infoview | |
