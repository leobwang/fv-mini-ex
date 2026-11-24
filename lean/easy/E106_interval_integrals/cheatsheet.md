# E106 · Interval integrals: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's interval integral
`∫ x in a..b, f x`, integrability on an interval (`IntervalIntegrable`), the Lebesgue measure
`MeasureTheory.volume`, the closed-form lemmas for `x ^ n`, `x` and constants, linearity of the integral,
and the tactic `fun_prop` for continuity.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`apply`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders: `(f g u : ℝ → ℝ)` are arbitrary real functions, `(a b c r : ℝ)`
  real numbers, `(n : ℕ)` a natural number. `{α : Type} [Mul α]` is any type with a `*` (`ℝ`, `ℕ`, `ℂ`, …).
- The lemmas hold for functions into any real Banach space `E` and any measure `μ`; this sheet states them
  for `ℝ → ℝ` and `volume`, the only case the exercise needs.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `∫ (x : ℝ) in a..b, f x` | `intervalIntegral (fun x => f x) a b volume`: the integral of `f` from `a` to `b`. You type it as `∫ x in a..b, f x` (`\int`) |
| `∫ (x : ℝ) in a..b, f x + g x` | the integral of the **sum**: the body after `,` extends as far right as it can. So the sum of two integrals prints as `(∫ (x : ℝ) in a..b, f x) + ∫ (x : ℝ) in a..b, g x` |
| `a..b` with `b < a` | allowed: by definition `∫ x in a..b, f x = -∫ x in b..a, f x` (a signed integral). That is why no lemma here needs `a ≤ b` |
| `MeasureTheory.volume` | the Lebesgue measure on `ℝ` (length of intervals); the default measure in `∫ x in a..b, f x` |
| `IntervalIntegrable f MeasureTheory.volume a b` | `f` is Lebesgue-integrable on the interval between `a` and `b` (a `Prop`) |
| `Continuous u` | `u : ℝ → ℝ` is continuous everywhere (a `Prop`) |
| `fun x => c` | the constant function with value `c` |
| `HMul.hMul m` | the function `fun x => m * x`, printed without `fun` (Lean drops `fun x => … x` when `x` is the last argument). You meet it in `case hf` after a bare `rw [intervalIntegral.integral_add]` on `∫ (m * x + c)` (R5) |
| `↑n` with `n : ℕ` | the natural number `n` cast into `ℝ`, e.g. `↑2 + 1` in the power rule |
| `(b - a) • c` | `•` (`\smul`) is scalar multiplication `HSMul.hSMul`; for `c : ℝ` it is plain `(b - a) * c` (R10) |
| `case hf`, `case hg` | the integrability side goals left by a bare `rw [intervalIntegral.integral_add]` (W2) |

Mathlib makes the integral of a non-integrable function `0` (a junk value, E069). So linearity
`∫ (f + g) = ∫ f + ∫ g` is false in general and `intervalIntegral.integral_add` asks for both
integrability proofs.

---

## Part 1 · `integral_sq`

Statement: `∫ x in (0 : ℝ)..1, x ^ 2 = 1 / 3`. Apply the power rule, then compute the numbers.

**R1 · `rw [integral_pow]`** changes the **goal**. The lemma is
`integral_pow : ∫ x in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (↑n + 1)` (no namespace prefix; `a b`
and `n` are found by matching). Placeholders: `(a b : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ) in a..b, x ^ n)` | `⊢ P ((b ^ (n + 1) - a ^ (n + 1)) / (↑n + 1))` |

**R2 · `norm_num`** **closes** a goal made of numerals: powers with numeral exponents such as `2 ^ (3 + 1)`,
`0 ^ k`, `/`, and casts `↑3` of numerals (W1).

---

## Part 2 · `trapezoid_exact_linear`

Statement: for all real `m c a b`, `∫ x in a..b, (m * x + c) = (b - a) * ((m * a + c) + (m * b + c)) / 2`:
the trapezoid rule (width times the mean of the endpoint values) is exact for a linear function. Split the
integral of the sum (R3, which needs R4 → R5 and R6), pull `m` out (R7), use the closed forms (R8, R9, R10),
and close the polynomial identity (R11).

**R3 · `rw [intervalIntegral.integral_add hf hg]`** changes the **goal**: the integral of a sum becomes a sum of
integrals. The lemma is `IntervalIntegrable f μ a b → IntervalIntegrable g μ a b →
∫ x in a..b, f x + g x ∂μ = (∫ x in a..b, f x ∂μ) + ∫ x in a..b, g x ∂μ` (`∂μ` is omitted when `μ = volume`).
Placeholders: `(f g : ℝ → ℝ) (a b : ℝ) (hf : IntervalIntegrable f MeasureTheory.volume a b)
(hg : IntervalIntegrable g MeasureTheory.volume a b)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ) in a..b, f x + g x)` | `⊢ P ((∫ (x : ℝ) in a..b, f x) + ∫ (x : ℝ) in a..b, g x)` |

The arguments `hf`, `hg` may be proof **terms** written inline (R4, R6, R12): Lean first matches the pattern
against the goal, so `f` and `g` are known when those terms are checked. Without arguments,
`rw [intervalIntegral.integral_add]` rewrites anyway and leaves `case hf`, `case hg` as extra goals (W2).

**R4 · `Continuous.intervalIntegrable`** changes the **goal**: a continuous function is integrable on every
bounded interval. The lemma is `Continuous u → ∀ (a b : ℝ), IntervalIntegrable u μ a b`. Used with `apply`,
the goal becomes the continuity. As a term it takes `a b` **explicitly**: `Continuous.intervalIntegrable hu a b`,
or `Continuous.intervalIntegrable hu _ _` to let Lean fill them in. Placeholders: `(u : ℝ → ℝ) (a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ IntervalIntegrable u MeasureTheory.volume a b` | `⊢ Continuous u` |

**R5 · `fun_prop`** **closes** `Continuous (fun x => …)` when the body is built from `x`, constants, `+`, `-`,
`*`, `^` (and other functions Mathlib knows to be continuous). Inside a term write `(by fun_prop)`:
`Continuous.intervalIntegrable (by fun_prop) _ _` proves integrability of `fun x => m * x`.
It also closes the same goal printed as `HMul.hMul k` (Reading the goals). Placeholders: `(k a b : ℝ)`.

| Before | After `apply Continuous.intervalIntegrable` (R4) | After `fun_prop` |
|---|---|---|
| `⊢ IntervalIntegrable (HMul.hMul k) MeasureTheory.volume a b` | `⊢ Continuous (HMul.hMul k)` | no goals |

**R6 · `intervalIntegrable_const`** **closes** `IntervalIntegrable (fun x => c) MeasureTheory.volume a b`:
a constant is integrable on every bounded interval. It takes no explicit arguments; `c`, `a`, `b` are found by
matching. Placeholders: `(c a b : ℝ)`.

**R7 · `rw [intervalIntegral.integral_const_mul]`** changes the **goal**: a constant factor moves out of the
integral. The lemma is `∫ x in a..b, r * f x = r * ∫ x in a..b, f x`. Placeholders:
`(r : ℝ) (f : ℝ → ℝ) (a b : ℝ)`. It only matches a factor on the **left** of `f x`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ) in a..b, r * f x)` | `⊢ P (r * ∫ (x : ℝ) in a..b, f x)` |

**R8 · `rw [integral_id]`** changes the **goal**. The lemma is `integral_id : ∫ x in a..b, x = (b ^ 2 - a ^ 2) / 2`
(no namespace prefix). Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ) in a..b, x)` | `⊢ P ((b ^ 2 - a ^ 2) / 2)` |

**R9 · `rw [intervalIntegral.integral_const]`** changes the **goal**. The lemma is
`∫ x in a..b, c = (b - a) • c`: the integrand does not mention `x`. Placeholders: `(c a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ) in a..b, c)` | `⊢ P ((b - a) • c)` |

**R10 · `rw [smul_eq_mul]`** changes the **goal**. The lemma is `smul_eq_mul : a • b = a * b`, valid when a type
acts on itself by its own multiplication. Placeholders: `{α : Type} [Mul α] (a b : α)`; `ℝ` qualifies.

| Before | After |
|---|---|
| `⊢ P (a • b)` | `⊢ P (a * b)` |

**R11 · `ring`** **closes** an identity that holds in every commutative ring, such as
`k * ((b ^ 2 - a ^ 2) / 2) = k * (b - a) * (a + b) / 2`. Division by a numeral is fine (`/ 2` is `* 2⁻¹`).
It does not use hypotheses.

---

## Part 3 · `integral_linear_comb`

Statement: for `f : ℝ → ℝ` with `hf : IntervalIntegrable f MeasureTheory.volume a b` and
`h : ∫ x in a..b, f x = 3`, prove `∫ x in a..b, (2 * f x + 1) = 6 + (b - a)`. Same route as Part 2, except that
`f` is unknown: its integrability comes from `hf` (R12) and its integral from `h` (`rw [h]`).

**R12 · `IntervalIntegrable.const_mul`** changes the **goal**: a constant multiple of an integrable function is
integrable. The lemma is `IntervalIntegrable f μ a b → ∀ (c : ℝ), IntervalIntegrable (fun x => c * f x) μ a b`.
As a term use dot notation: `hf.const_mul c`. Placeholders: `(f : ℝ → ℝ) (a b c : ℝ)
(hf : IntervalIntegrable f MeasureTheory.volume a b)`.

| Before | After |
|---|---|
| `⊢ IntervalIntegrable (fun x => c * f x) MeasureTheory.volume a b` | `⊢ IntervalIntegrable f MeasureTheory.volume a b` |

Then R3 (with R12 and R6 as its arguments), R7, `rw [h]` (TACTIC_STATES, "Rewriting"), R9, R10, R11.

---

### Worked combinations (W1–W3, on integrands that are not the exercise's)

**W1: `∫ x in (0 : ℝ)..2, x ^ 3 = 4`.** R1 leaves the numeral goal below, and R2 closes it:

```lean-goal
⊢ (2 ^ (3 + 1) - 0 ^ (3 + 1)) / (↑3 + 1) = 4
```

**W2: bare `rw [intervalIntegral.integral_add]`** on `∫ x in a..b, (k * x ^ 2 + c)`. The main goal comes first,
then the two integrability goals (`case hf`, `case hg`); handle each with `·` (R7, R1, R9, R10, then
`norm_num` and R11; R4 → R5; R6):

```lean-goal
⊢ (∫ (x : ℝ) in a..b, k * x ^ 2) + ∫ (x : ℝ) in a..b, c = k * (b ^ 3 - a ^ 3) / 3 + (b - a) * c
⊢ IntervalIntegrable (fun x => k * x ^ 2) MeasureTheory.volume a b
⊢ IntervalIntegrable (fun x => c) MeasureTheory.volume a b
```

**W3: a known integral as a hypothesis.** With `hg : IntervalIntegrable g MeasureTheory.volume a b` and
`hI : ∫ x in a..b, g x = 5`, R3 (arguments R4 → R5 and `hg`) gives the goal below; `rw [integral_id, hI]`
(R8, then the hypothesis) closes it, because `rw` tries `rfl` at the end:

```lean-goal
⊢ (∫ (x : ℝ) in a..b, x) + ∫ (x : ℝ) in a..b, g x = (b ^ 2 - a ^ 2) / 2 + 5
```

---

## Traps

- `simp` makes no progress on `∫ x in a..b, m * x`: it does not integrate. Pull `m` out with R7 first, then
  use R8.
- Names: `integral_pow` and `integral_id` have no prefix; `integral_add`, `integral_const_mul` and
  `integral_const` need `intervalIntegral.`. A bare `integral_add` is an unknown identifier here
  (`MeasureTheory.integral_add` is for the integral over a whole space, `∫ x, f x ∂μ`).
- `Continuous.intervalIntegrable (by fun_prop)` without `_ _` is a function of `a b`, not a proof of
  integrability; `rw` then fails to elaborate the argument.
- The order of the two arguments of R3 follows the summands: the first proves integrability of the left
  summand. With the pair swapped, `rw` reports that it did not find the pattern.
- R7 needs the constant on the left (`r * f x`). `f x * r` needs `intervalIntegral.integral_mul_const`.
- R9 leaves `•`, not `*`. `ring` happens to accept `(b - a) • c` for `c : ℝ`, but `rw [smul_eq_mul]` (R10)
  makes the goal plain arithmetic that every tactic reads the same way.
- After `rw [h]` the left side of `h` must appear literally: rewrite with R3 and R7 first so that
  `∫ (x : ℝ) in a..b, f x` stands alone.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `∫ x ^ n` | `rw [integral_pow]` | R1 |
| numeral goal with `↑k`, `^`, `/` | `norm_num` | R2 |
| `∫ (f + g)` → `∫ f + ∫ g` | `rw [intervalIntegral.integral_add hf hg]` | R3 |
| integrable from continuous | `Continuous.intervalIntegrable (by fun_prop) _ _` | R4, R5 |
| continuity of a polynomial expression | `fun_prop` | R5 |
| constant is integrable | `intervalIntegrable_const` | R6 |
| `∫ r * f x` → `r * ∫ f x` | `rw [intervalIntegral.integral_const_mul]` | R7 |
| `∫ x` | `rw [integral_id]` | R8 |
| `∫ c` → `(b - a) • c` | `rw [intervalIntegral.integral_const]` | R9 |
| `•` → `*` | `rw [smul_eq_mul]` | R10 |
| polynomial identity | `ring` | R11 |
| `c * f` integrable from `hf` | `hf.const_mul c` | R12 |
| use a known integral `h` | `rw [h]` | |
| see the state | infoview | |
