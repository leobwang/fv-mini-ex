# M119 · Discrete Gronwall inequality: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), including `induction … with` and `have`.
**New here:** Mathlib's real numbers `ℝ`, the cast `ℕ → ℝ`, `Real.exp`, and the order tactics
`gcongr`, `linarith`, `nlinarith`, `positivity`, `push_cast`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal that the step leaves alone.
- Placeholders are written as Lean binders. `{M : Type}` is any type. A bracket such as `[Monoid M]` is a
  requirement on `M` (a *type class*); each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `e : ℕ → ℝ` | a real sequence; `e n` is its `n`-th term $e_n$ |
| `↑n` | the natural number `n` cast into `ℝ` (`Nat.cast n`); `↑(n + 1)` is the cast of the sum |
| `x ^ n` | `x` to the natural power `n` (`Monoid.npow`), with `x ^ 0 = 1` |
| `Real.exp x` | the real exponential $e^x$ |
| `case zero`, `case succ` | the two goals of an induction on `n : ℕ` |
| `ih : …` | the induction hypothesis: the claim for `n`, available in the `succ` case |
| `n✝ n : ℕ` | an outer `n` shadowed by a new `n` (from `intro n`); `n✝` can no longer be named |
| `case hab`, `case hbc`, `case ha` | goals left by `gcongr` (`ha` is a side goal such as `0 ≤ x`) |
| `case calc.step` | a goal `calc` adds when its last right-hand side differs from the goal's (Traps) |

---

## Part 1 · `discrete_gronwall`

Statement: if $e_{n+1} \le (1+a)\,e_n + b$ for all $n$, with $a, b, e_0 \ge 0$, then
$e_n \le e^{na}\,(e_0 + n b)$ for every $n$.

Plan: induction on the claim as stated fails (the step needs $e^{(n+1)a} = e^{a} e^{na}$ *and* a bound on
$1+a$ at once). Prove the sharper milestone $e_n \le (1+a)^n (e_0 + n b)$ by induction, then
$(1+a)^n \le (e^a)^n = e^{na}$ because $1 + a \le e^a$.

### Induction on a strengthened claim

**R1 · `induction n with | zero => … | succ k ih => …`** changes the **goal list**: one goal per
constructor of `ℕ`. The `succ` goal gains `k : ℕ` and `ih : P k`. Write it inside
`have key : ∀ n : ℕ, Q n := by intro n; induction n with …` to prove a claim `Q` of your choice, then use
`key n`. Placeholders: `(P : ℕ → Prop) (n : ℕ)`. Indent the `|` alternatives under `induction`.
The table's states are from the guide's second R1 example, Mathlib's `induction' n with k ih`, which
opens the same two goals without the `|` alternatives (in the infoview they appear as `case zero`, `case succ`).

| Before | After |
|---|---|
| `n : ℕ ⊢ P n` | `⊢ P 0`, `k : ℕ, ih : P k ⊢ P (k + 1)` |

**R2 · `simp` on the base case** changes the **goal**: `pow_zero` (`c ^ 0 = 1`), `Nat.cast_zero`
(`↑(0 : ℕ) = 0`), `zero_mul`, `add_zero`, `one_mul` clean it up; a goal `x ≤ x` is then closed.
Placeholders: `(x c b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (c ^ 0 * (x + ↑0 * b))` | `⊢ P x` |

### Facts for the induction step

**R3 · `one_le_pow₀`** changes the **context** (used in `have`). Statement:
`one_le_pow₀ : 1 ≤ a → 1 ≤ a ^ n` (`n` implicit). Placeholders: `(x : ℝ) (n : ℕ) (hx : 1 ≤ x)`; the type
must be an ordered semiring (`ℝ`, `ℚ`, `ℕ` qualify).

| Before | After |
|---|---|
| `hx : 1 ≤ x ⊢ G` | `h1 : 1 ≤ x ^ n ⊢ G` |

**R4 · `linarith`** **closes** a goal (`≤`, `<`, `=`, or `False`) that is a linear combination of hypotheses.
Extra facts go in brackets: `linarith [t]`. To prove a side condition inline, write a typed proof term:
`(by linarith : (0 : ℝ) ≤ 1 + a)`.

| Before | After |
|---|---|
| `hx : 0 ≤ x ⊢ 1 ≤ 1 + x` | closed |

**R5 · `calc`** changes the **goal list**: a chain `x ≤ y`, `_ ≤ z` proves `x ≤ z`, one proof per step. `_`
stands for the previous right-hand side; `=` and `≤` steps may be mixed. Each step is `_ ≤ rhs := proof`
(a term such as `hstep n`, or `by tactics`). Placeholders: `(x y z : ℝ)`.

| Before | After |
|---|---|
| `⊢ x ≤ z` | `⊢ x ≤ y`, `⊢ y ≤ z` |

**R6 · `gcongr`** changes the **goal**: it matches both sides of `≤`, removes the common shape, and leaves
the inequality between the parts that differ. Side goals such as `0 ≤ c` (needed to multiply an
inequality) are proved from a hypothesis or by `positivity`; if neither works they stay as goals. If a
hypothesis states the remaining goal exactly (the induction hypothesis), `gcongr` closes it too.
Placeholders: `(c d x y : ℝ) (hc : 0 ≤ c)`.

| Before | After |
|---|---|
| `hc : 0 ≤ c ⊢ c * x + d ≤ c * y + d` | `hc : 0 ≤ c ⊢ x ≤ y` |

**R7 · `push_cast`** changes the **goal**: it pushes casts inward, `↑(n + 1)` → `↑n + 1`
(`Nat.cast_add`, `Nat.cast_one`). Placeholders: `(n : ℕ) (b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (↑(n + 1) * b)` | `⊢ P ((↑n + 1) * b)` |

**R8 · `rw [pow_succ]`** changes the **goal**. Statement: `pow_succ : a ^ (n + 1) = a ^ n * a`.
Placeholders: `{M : Type} [Monoid M] (a : M) (n : ℕ)` (a monoid has an associative `*` with `1`; `ℝ`
qualifies).

| Before | After |
|---|---|
| `⊢ P (a ^ (n + 1))` | `⊢ P (a ^ n * a)` |

**R9 · `mul_le_mul_of_nonneg_left`** changes the **context** (used in `have` or inside `nlinarith [...]`).
Statement: `b ≤ c → 0 ≤ a → a * b ≤ a * c`. Placeholders: `(a b c : ℝ) (hbc : b ≤ c) (ha : 0 ≤ a)`.

| Before | After |
|---|---|
| `ha : 0 ≤ a ⊢ G` | `h : a * b ≤ a * c ⊢ G` |

**R10 · `nlinarith [t₁, …]`** **closes** a polynomial inequality. It multiplies pairs of hypotheses and
listed facts, then runs `linarith`. It rarely guesses the right product of three factors, so hand it the
product fact (R9). Placeholders: `(x y : ℝ) (hx : 0 ≤ x) (hy : 1 ≤ y)`.

| Before | After |
|---|---|
| `hx : 0 ≤ x, hy : 1 ≤ y ⊢ x ≤ x * y` | closed by `nlinarith [mul_le_mul_of_nonneg_left hy hx]` |

### From `(1 + a) ^ n` to `exp`

**R11 · `gcongr` on a right factor** changes the **goal**: `x * s ≤ y * s` → `x ≤ y`. The side goal `0 ≤ s`
is proved by `positivity`, which uses hypotheses `0 ≤ u` for atoms and knows `0 ≤ ↑n`.
Placeholders: `(x y u v : ℝ) (n : ℕ) (hu : 0 ≤ u) (hv : 0 ≤ v)`.

| Before | After |
|---|---|
| `hu : 0 ≤ u ⊢ x * (u + ↑n * v) ≤ y * (u + ↑n * v)` | `hu : 0 ≤ u ⊢ x ≤ y` |

**R12 · `gcongr` on powers** changes the **goal**: `x ^ n ≤ y ^ n` → `x ≤ y`, with side goal `0 ≤ x`.
Placeholders: `(x y : ℝ) (n : ℕ) (hx : 0 ≤ x)`.

| Before | After |
|---|---|
| `hx : 0 ≤ x ⊢ x ^ n ≤ y ^ n` | `hx : 0 ≤ x ⊢ x ≤ y` |

**R13 · `Real.add_one_le_exp`** changes the **context**. Statement: `∀ x : ℝ, x + 1 ≤ Real.exp x`. Note the
order `x + 1`, not `1 + x`: `rw`/`exact` will not match `1 + x`, so pass it to `linarith`.
Placeholders: `(t : ℝ)`.

| Before | After |
|---|---|
| `⊢ t ≤ Real.exp t - 1` | `h : t + 1 ≤ Real.exp t ⊢ t ≤ Real.exp t - 1` |

**R14 · `rw [← Real.exp_nat_mul]`** changes the **goal**. Statement:
`Real.exp_nat_mul : Real.exp (↑n * x) = Real.exp x ^ n`; `←` uses it right to left. When the goal becomes
`a = a`, `rw` closes it. Placeholders: `(x : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (Real.exp x ^ n)` | `⊢ P (Real.exp (↑n * x))` |

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: a strengthened claim by induction.** For `u (n + 1) ≤ 3 * u n`, the claim `u n ≤ 3 ^ n * u 0`
goes by R1: the base case by `simp` (R2), the step by a three-line `calc` (R5): the recursion, then
`gcongr` (R6, which uses `ih`), then `rw [pow_succ]; ring` (R8). The goal before `induction`:

```lean-goal
⊢ u n ≤ 3 ^ n * u 0
```

**W2: replace a factor by a larger one.** `gcongr` (R11) reduces `(1 + t) * s ≤ Real.exp t * s` to

```lean-goal
⊢ 1 + t ≤ Real.exp t
```

and `linarith [Real.add_one_le_exp t]` (R13, R4) closes it.

---

## Traps

- Induction on the stated bound with `Real.exp` gets stuck: prove the `(1 + a) ^ n` milestone first.
- `intro n` inside `have key : ∀ n : ℕ, …` shadows the theorem's own `n`, which then shows as `n✝`. Use
  `key n` at the end, not the shadowed name.
- After `induction n`, the `succ` goal has `↑(n + 1)`, not `↑n + 1`; `push_cast` (R7) first, or the
  arithmetic tactics see `↑(n + 1)` as an unrelated atom.
- The last `calc` line must match the goal. Write `(e 0 + (n + 1 : ℕ) * b)`: it elaborates to `↑(n + 1)`. Plain
  `(n + 1) * b` elaborates to `(↑n + 1) * b`, and `calc` leaves an extra goal `case calc.step` comparing the two.
- `gcongr` leaves a side goal like `0 ≤ x` open when neither a hypothesis nor `positivity` proves it; have
  `ha : 0 ≤ a` around so `positivity` gets `0 ≤ 1 + a`.
- `nlinarith` needs the product `(1 + a) * 1 ≤ (1 + a) * (1 + a) ^ n` handed to it (R9); `1 ≤ (1 + a) ^ n` alone
  is not enough.
- `Real.add_one_le_exp a : a + 1 ≤ Real.exp a` has `a + 1`, not `1 + a`: use it through `linarith`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| prove a stronger claim first | `have key : ∀ n : ℕ, Q n := by intro n; induction n with …` | R1 |
| base case with `^ 0`, `↑0` | `simp` | R2 |
| `1 ≤ a ^ n` from `1 ≤ a` | `one_le_pow₀ h` | R3 |
| linear goal from hypotheses | `linarith`, `linarith [t]`, `(by linarith : T)` | R4 |
| chain of `≤` / `=` | `calc x ≤ y := p₁` / `_ ≤ z := p₂` | R5 |
| same shape both sides of `≤` | `gcongr` | R6, R11, R12 |
| `↑(n + 1)` → `↑n + 1` | `push_cast` | R7 |
| `a ^ (n + 1)` → `a ^ n * a` | `rw [pow_succ]` | R8 |
| multiply `b ≤ c` by `0 ≤ a` | `mul_le_mul_of_nonneg_left hbc ha` | R9 |
| polynomial inequality | `nlinarith [product fact]` | R10 |
| `x + 1 ≤ exp x` | `Real.add_one_le_exp x` | R13 |
| `exp x ^ n` → `exp (↑n * x)` | `rw [← Real.exp_nat_mul]` | R14 |
| see the state | infoview | |
