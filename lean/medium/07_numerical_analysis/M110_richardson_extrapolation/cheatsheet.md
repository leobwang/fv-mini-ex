# M110 · Richardson extrapolation: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ`, absolute value
`|x|`, natural-number powers `x ^ n`, and the tactics `set`, `field_simp`, `linarith`, `positivity`,
`gcongr`, `calc`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`exact`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
  `∅` means the step closed the goal.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[DivisionCommMonoid α]`
  is a requirement on `α` (a *type class*). Each entry says which familiar types meet it; in this problem
  `α` is always `ℝ`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers. Numerals such as `2`, `1` in a real expression are reals |
| `\|x\|` | `abs x`, the absolute value `max x (-x)` |
| `2 ^ p` with `p : ℕ` | `2 · 2 ⋯ 2` (`p` factors), computed in `ℝ`; the exponent stays a natural number |
| `c * t ^ p`, `K * h ^ q * (2 ^ p - 1)` | `^` binds tighter than `*` and `/`, which bind tighter than `+` and `-`: `c * (t ^ p)`. `*` groups to the left: `(K * h ^ q) * (2 ^ p - 1)` |
| `h / 2`, `x⁻¹` | real division and inverse. In Lean `x / 0 = 0`, so lemmas about `/` need `b ≠ 0` or `0 < b` |
| `(0:ℝ)` | the numeral `0` forced to be a real (a *type ascription*). The infoview drops it: `have hpos : (0:ℝ) < 2 ^ p - 1` shows as `hpos : 0 < 2 ^ p - 1`; hover a term to see its type |
| `∀ (t : ℝ), 0 < t → Q t` | for every real `t`, if `0 < t` then `Q t`; apply it as `hQ t ht` (R4) |
| `u : ℝ := e` | a local definition made by `set` (R6): `u` is a name for `e`, and Lean shows its body |
| `a ≠ b` | `¬ (a = b)` |
| `A ↔ B` | `A` if and only if `B`; `rw` with an `↔` lemma replaces `A` by `B` |
| `case ha`, `case a` | labels of the goals `apply` created (R1) |

---

## Part 1 · `richardson`

Statement: for natural numbers `p ≥ 1`, `q`, reals `A c K h` with `h > 0`, and a function `D : ℝ → ℝ` with
$|D(t) - (A + c\,t^p)| \le K t^q$ for every $t > 0$,

$$\left|\frac{2^p D(h/2) - D(h)}{2^p - 1} - A\right| \le \frac{2^p/2^q + 1}{2^p - 1}\, K\, h^q .$$

Idea: write $u = D(h/2) - (A + c(h/2)^p)$ and $w = D(h) - (A + c h^p)$. Since $2^p (h/2)^p = h^p$, the
left side is $|(2^p u - w)/(2^p - 1)|$; the triangle inequality and the two bounds finish it.

### Facts about `2 ^ p`

**R1 · `apply one_lt_pow₀`** changes the **goal list**. The lemma is `one_lt_pow₀ : 1 < a → n ≠ 0 → 1 < a ^ n`;
`apply` leaves its two hypotheses as goals. In term form, `one_lt_pow₀ (by norm_num) (by omega)` proves
both on the spot. Placeholders: `{α : Type} [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] (a : α) (n : ℕ)`
(α is an ordered ring such as `ℝ`, `ℚ`, `ℤ`).

| Before | After |
|---|---|
| `⊢ 1 < a ^ n` | `⊢ 1 < a`, `⊢ n ≠ 0` |

**R2 · `omega`** **closes** a goal of linear arithmetic over `ℕ` or `ℤ` (`+`, `-`, `≤`, `<`, `=`, `≠`,
numerals), using the hypotheses. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `hn : 1 ≤ n ⊢ n ≠ 0` | ∅ |

**R3 · `linarith`** **closes** a linear equality or inequality over an ordered field such as `ℝ` that
follows from hypotheses by adding them with nonnegative coefficients. Terms such as `2 ^ p` are treated as
unknowns. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `ha : 1 < a ⊢ 0 < a - 1` | ∅ |

### Using the hypothesis `hD`

**R4 · `have e := hQ t ht`** changes the **context**: it applies the `∀` hypothesis to a point `t` and a proof
`ht : 0 < t`, and adds the instance. The goal stays the same. Placeholders:
`(Q : ℝ → Prop) (hQ : ∀ t, 0 < t → Q t) (t : ℝ) (ht : 0 < t)`.

| Before | After |
|---|---|
| `⊢ G` | `e : Q t ⊢ G` |

**R5 · `positivity`** **closes** a goal `0 < e`, `0 ≤ e` or `e ≠ 0` by the syntactic shape of `e`: products,
quotients, powers of positive things are positive. For a variable it looks for a hypothesis `0 < x`. Use it
as `(by positivity)` to supply `0 < h / 2` or `0 < 2 ^ p`. Placeholders: `(t : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `ht : 0 < t ⊢ 0 < 2 ^ n * (t / 2)` | ∅ |

### Naming the remainders

**R6 · `set u := e with hu`** changes the **context and the goal**: it adds a local definition `u := e` and the
equation `hu : u = e`, and replaces every occurrence of `e` in the goal **and in every hypothesis** by `u`.
`rw [hu]` later turns `u` back into `e`. Placeholders: `(f : ℝ → ℝ) (a b : ℝ)`, `e` is `f a - b`.

| Before | After |
|---|---|
| `hb : P (f a - b) ⊢ P (f a - b)` | `u : ℝ := f a - b, hb : P u, hu : u = f a - b ⊢ P u` |

### The cancellation identity

**R7 · `rw [div_pow]`** changes the **goal**. The lemma is `div_pow : (a / b) ^ n = a ^ n / b ^ n`.
Placeholders: `{α : Type} [DivisionCommMonoid α] (a b : α) (n : ℕ)` (α has commutative `*` and `/`; `ℝ`, `ℚ`,
`ℂ` qualify).

| Before | After |
|---|---|
| `⊢ P ((a / b) ^ n)` | `⊢ P (a ^ n / b ^ n)` |

**R8 · `field_simp`** changes the **goal**: it multiplies out every denominator it can prove nonzero, so an
equation of fractions becomes an equation of products. It proves `b ≠ 0` from a hypothesis `b ≠ 0` or
`0 < b` in the context, or by itself for things like `2 ^ p`. The form it produces (factor order, which side
gets what) is its own choice: follow it with `ring` (R9) rather than `exact`. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `hb : b ≠ 0 ⊢ a / b = c` | `⊢ a = b * c` |

**R9 · `ring`** **closes** an equation that holds in every commutative ring: it expands both sides and
compares. It treats `D (h / 2)`, `u`, `2 ^ p` as unknowns and does not use hypotheses. Here the `c` terms
cancel. Placeholders: `(a c x y z : ℝ)`.

| Before | After |
|---|---|
| `⊢ a * (y - c * x) - (z - c * (a * x)) = a * y - z` | ∅ |

### Absolute value of a quotient

**R10 · `rw [abs_div]`** changes the **goal**. The lemma is `abs_div : |a / b| = |a| / |b|`. Placeholders:
`(a b : ℝ)` (any linearly ordered field).

| Before | After |
|---|---|
| ⊢ P \|a / b\| | ⊢ P (\|a\| / \|b\|) |

```lean-goal
⊢ P |a / b|
⊢ P (|a| / |b|)
```

**R11 · `rw [abs_of_pos ha]`** changes the **goal**. The lemma is `abs_of_pos : 0 < a → |a| = a`. Pass the
proof of `0 < a` (a hypothesis, or `(by positivity)`). Placeholders: `(a : ℝ) (ha : 0 < a)`.

| Before | After |
|---|---|
| ha : 0 < a ⊢ P \|a\| | `⊢ P a` |

```lean-goal
⊢ P |a|
⊢ P a
```

**R12 · `rw [div_le_iff₀ hc]`** changes the **goal**: a denominator on the left of `≤` moves to the right as a
factor. The lemma is `div_le_iff₀ : 0 < c → (b / c ≤ a ↔ b ≤ a * c)`. Placeholders: `(a b c : ℝ) (hc : 0 < c)`.

| Before | After |
|---|---|
| `hc : 0 < c ⊢ b / c ≤ a` | `⊢ b ≤ a * c` |

### Chaining inequalities

**R13 · `calc`** changes the **goal list**: it proves `a ≤ c` as a chain `a ≤ b`, `b ≤ c`, … in which each
step has its own proof after `:=`, and `_` stands for the previous right side. A step may be `=`, `≤` or `<`;
the chain's relation is the weakest one. A step proved by `?_` is left as a goal. Indent the `_` lines further
than `calc`. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ≤ c` | `⊢ b ≤ c` |

**R14 · `abs_sub`** **closes** the triangle inequality for a difference. The lemma is
`abs_sub : |a - b| ≤ |a| + |b|` (do not confuse it with `abs_sub_comm : |a - b| = |b - a|`). Use it as the
proof of a `calc` step, `:= abs_sub _ _`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| ⊢ \|a - b\| ≤ \|a\| + \|b\| | ∅ |

```lean-goal
⊢ |a - b| ≤ |a| + |b|
```

**R15 · `rw [abs_mul]`** changes the **goal**. The lemma is `abs_mul : |a * b| = |a| * |b|`. Follow it with
R11 to drop the bars around a positive factor such as `2 ^ p`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| ⊢ P \|a * b\| | ⊢ P (\|a\| * \|b\|) |

```lean-goal
⊢ P |a * b|
⊢ P (|a| * |b|)
```

**R16 · `rw [lemma] at e`** changes the **context**: it rewrites the hypothesis `e` instead of the goal. Use it
to put a bound in the form a later step looks for. Placeholders: `(a b x : ℝ) (n : ℕ)`, here with `div_pow`.

| Before | After |
|---|---|
| `e : x ≤ (a / b) ^ n ⊢ False` | `e : x ≤ a ^ n / b ^ n ⊢ False` |

**R17 · `gcongr`** changes the **goal list**: for two sides of the same shape (`k * □ + □`), it reduces
`≤` to `≤` between the parts that differ. It closes side goals such as `0 ≤ k` with `positivity` (R5) and any
part that a hypothesis states exactly (`assumption`); the rest stay open. Placeholders: `(k a b c d : ℝ)` with
`hk : 0 < k`, `hac : a ≤ c` in the context.

| Before | After |
|---|---|
| `⊢ k * a + b ≤ k * c + d` | `⊢ b ≤ d` |

**R18 · `field_simp`** as a finisher **closes** an identity whose two sides agree once the denominators are
cleared: it brings both sides to its own normal form (one fraction `n / d`, then the denominators
cross-multiplied away, factors such as `2 ^ p * (h ^ q / 2 ^ q)` cancelled) and closes the goal when the two
sides come out identical. It does not call `ring`; if it leaves a goal, finish with `ring` (R9). Placeholders:
`(a b c : ℝ) (hb : 0 < b)`.

| Before | After |
|---|---|
| `⊢ (a / b + c) * b = a + c * b` | ∅ |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: a cancellation with step `t / 3`.** `rw [div_pow]` (R7), then `field_simp` (R8, R18) closes it:

```lean-goal
⊢ 3 ^ n * (y - c * (t / 3) ^ n) = 3 ^ n * y - c * t ^ n
⊢ 3 ^ n * (y - c * (t ^ n / 3 ^ n)) = 3 ^ n * y - c * t ^ n
```

**W2: clearing a positive denominator under `|·|`.** `rw [abs_div, abs_of_pos hk, div_le_iff₀ hk]`
(R10, R11, R12) in one call:

```lean-goal
⊢ |x / k| ≤ 5
⊢ |x| ≤ 5 * k
```

**W3: triangle inequality, then the bounds.** A three-step `calc` (R13): `abs_sub _ _` (R14), then
`rw [abs_mul, abs_of_pos (by positivity)]` (R15, R11), then `gcongr` (R17), which finds `hx`, `hy` itself.

---

## Traps

- `have hpos : 0 < 2 ^ p - 1` with no type is read in `ℕ`, where `-` is truncated (`0 - 1 = 0`). Write
  `(0:ℝ) < 2 ^ p - 1` (and `(1:ℝ) < 2 ^ p`).
- `set` replaces `e` only in what exists at that moment. Instantiate `hD` (R4) **before** the two `set`s, so the
  bounds come out as `|u| ≤ …` and `|w| ≤ …`.
- `field_simp` cannot clear `2 ^ p - 1` unless `hpos : 0 < 2 ^ p - 1` (or `≠ 0`) is already in the context.
- `div_le_iff₀` needs the proof of `0 < c` as its argument; the older name `div_le_iff` is deprecated.
- `gcongr` closes a part only when a hypothesis states it exactly. `|u| ≤ K * (h / 2) ^ q` does not match
  `|u| ≤ K * (h ^ q / 2 ^ q)`: rewrite the hypothesis first (R16).
- `abs_sub` is the triangle inequality `|a - b| ≤ |a| + |b|`, not the symmetry `|a - b| = |b - a|`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `1 < 2 ^ p` from `1 ≤ p` | `one_lt_pow₀ (by norm_num) (by omega)` | R1, R2 |
| `0 < 2 ^ p - 1` from `1 < 2 ^ p` | `by linarith` | R3 |
| use `∀ t, 0 < t → …` at `t₀` | `have e := hD t₀ ht₀` | R4 |
| `0 < h / 2`, `0 < 2 ^ p` | `(by positivity)` | R5 |
| name a subterm everywhere | `set u := e with hu` | R6 |
| `(a / b) ^ n → a ^ n / b ^ n` | `rw [div_pow]` | R7 |
| identity with denominators | `field_simp`, then `ring` | R8, R9, R18 |
| `\|a / b\| → \|a\| / \|b\|` | `rw [abs_div]` | R10 |
| `\|a\| → a` when `0 < a` | `rw [abs_of_pos ha]` | R11 |
| `b / c ≤ a → b ≤ a * c` | `rw [div_le_iff₀ hc]` | R12 |
| chain of `≤` / `=` | `calc a ≤ b := p₁`, next line `_ ≤ c := p₂` | R13 |
| `\|a - b\| ≤ \|a\| + \|b\|` | `abs_sub _ _` | R14 |
| `\|a * b\| → \|a\| * \|b\|` | `rw [abs_mul]` | R15 |
| rewrite a hypothesis | `rw [lemma] at e` | R16 |
| monotone step `k * a + b ≤ k * c + d` | `gcongr` | R17 |
| see the state | infoview | |
