# M090 · Cauchy–Schwarz for expectations: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's Lebesgue integral
`∫ x, f x ∂μ` against a measure `μ`, the predicate `Integrable`, the expectation notation `μ[f]`,
the discriminant `discrim`, and the arithmetic deciders `linarith` / `nlinarith`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`exact`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. The measure-theory ones are always
  `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ)`: `Ω` is the sample space,
  `[MeasurableSpace Ω]` equips it with a σ-algebra (a *type class*: Lean finds it automatically),
  `μ` is a measure on it (a probability measure in the application, but nothing here needs total
  mass 1), and `f g` are real functions on `Ω` (random variables).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers (`Real`) |
| `{Ω : Type*}` | `Ω` is a type in any universe (`Type u` for some `u`); for this problem read it as `Ω : Type` |
| `open MeasureTheory ProbabilityTheory` | makes `Measure`, `Integrable`, `integral_add`, … usable without the `MeasureTheory.` prefix, and turns on the notation `μ[f]` |
| `Measure Ω` | a measure on `Ω` (`MeasureTheory.Measure`); `μ` in the statement |
| `∫ (x : Ω), f x ∂μ` | the Lebesgue integral of `f` against `μ`; for a probability measure, `E[f]` |
| `μ[fun ω => F ω]` | notation (from `open ProbabilityTheory`) for `∫ x, (fun ω => F ω) x ∂μ`. Write it with no space between `μ` and `[` |
| `r * ∫ (a : Ω), f a ∂μ + ∫ (a : Ω), g a ∂μ` | `(r * (∫ f)) + (∫ g)`: an integral runs from `∫` to its `∂μ`, so each `∫ … ∂μ` is one bracketed term |
| `∫ (x : Ω), (fun ω => X ω * Y ω) x ∂μ` | how the infoview prints `μ[fun ω => X ω * Y ω]`: the integrand is a lambda applied to the bound `x`, not yet beta-reduced |
| `∫ (a : Ω), X a ^ 2 ∂μ` | the same kind of integral after a `rw`: Lean beta-reduces the integrand; the bound name (`x`, `a`, `ω`) is irrelevant |
| `Integrable f μ` | `f` is measurable (a.e.-strongly measurable) and `∫ ‖f‖ ∂μ < ∞`. Hypotheses `hX2`, `hY2`, `hXY` give it for `X²`, `Y²`, `XY` |
| `0 ≤ f` for a function `f` | pointwise: `∀ ω, 0 ≤ f ω`. After `intro ω` it shows as `0 ω ≤ f ω`, where `0 ω` is the zero function at `ω`, i.e. `0` |
| `f + g` for functions | the pointwise sum, `(f + g) ω = f ω + g ω` |
| `discrim a b c` | Mathlib's discriminant `b ^ 2 - 4 * a * c` (a definition, unfold it with `rw [discrim]`) |
| `this` | the name `have := …` gives a fact when you do not name it |
| `-2 * t * (X ω * Y ω)` | `(-2 * t) * (X ω * Y ω)`: `*` groups to the left, so Lean drops your parentheses around `-2 * t` |

---

## Part 1 · `cauchy_schwarz`

Statement: for integrable `X²`, `Y²`, `XY`, `(E[XY])² ≤ E[X²] · E[Y²]`, with `E[F] = ∫ F dμ`. The
argument: for every real `t`, `0 ≤ E[(X − tY)²] = E[Y²]·t² + (−2·E[XY])·t + E[X²]`. A quadratic
`a t² + b t + c` that is nonnegative for all `t` has discriminant `b² − 4ac ≤ 0`. With
`a = E[Y²]`, `b = −2 E[XY]`, `c = E[X²]` that is `4 E[XY]² − 4 E[Y²] E[X²] ≤ 0`.

### The milestone `∀ t, …`

**R1 · `intro t`** changes the **goal and the context**: a goal `∀ t, P t` loses its `∀`, and `t`
becomes a hypothesis. Placeholders: `(P : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ (t : ℝ), P t` | `t : ℝ ⊢ P t` |

### Nonnegativity of an integral

**R2 · `integral_nonneg`** changes the **goal**. The lemma is
`integral_nonneg : 0 ≤ f → 0 ≤ ∫ x, f x ∂μ`: the integral of a pointwise nonnegative function is
nonnegative (no integrability needed: a non-integrable function integrates to `0`). `apply` leaves the
pointwise goal `0 ≤ f`; `intro ω` opens it. Placeholders: `{Ω} [MeasurableSpace Ω] (μ : Measure Ω)
(f : Ω → ℝ)`. In term mode, `integral_nonneg fun ω => (proof of 0 ≤ f ω)` does it in one go (W1).

| Before | After `apply integral_nonneg` | After `intro ω` |
|---|---|---|
| `⊢ 0 ≤ ∫ (ω : Ω), f ω ∂μ` | `⊢ 0 ≤ f` | `ω : Ω ⊢ 0 ω ≤ f ω` |

**R3 · `sq_nonneg`** **closes** a goal `0 ≤ a ^ 2`. The lemma is `sq_nonneg a : 0 ≤ a ^ 2` (in any
linearly ordered ring, `ℝ` included). Placeholders: `(a : ℝ)`. With `_` for `a`, Lean infers it from the goal.

| Before | After |
|---|---|
| `⊢ 0 ≤ a ^ 2` | no goals |

### Rewriting the integrand

**R4 · `funext ω`** changes the **goal and the context**: an equation of functions becomes an equation of
their values at a fresh `ω` (function extensionality). Then `ring` closes a polynomial identity (W2).
Placeholders: `{Ω : Type} (f g : Ω → ℝ)`.

| Before | After |
|---|---|
| `⊢ (fun ω => 2 * f ω) = fun ω => 2 * g ω` | `ω : Ω ⊢ 2 * f ω = 2 * g ω` |

**R5 · `rw [e] at h`** changes the **context**: it rewrites the hypothesis `h` instead of the goal. With
`e : (fun ω => F ω) = fun ω => G ω`, it replaces the integrand of `∫ … ∂μ` inside `h`, because the integral
`∫ x, F x ∂μ` is `integral μ (fun x => F x)` and the lambda occurs literally. After the rewrite Lean
beta-reduces, so the integrand is written out. Placeholders: `(f g : Ω → ℝ) (P : ℝ → Prop)`,
`e : (fun ω => f ω * g ω) = fun ω => g ω * f ω`. The goal does not change.

| `h` before | `h` after |
|---|---|
| `h : P (∫ (x : Ω), (fun ω => f ω * g ω) x ∂μ)` | `h : P (∫ (ω : Ω), g ω * f ω ∂μ)` |

### Integrability facts

`integral_add` (R8) needs one `Integrable` proof per summand. Build them first, each as a named `have`.

**R6 · `hf.const_mul c`** **closes** an integrability goal for a constant multiple. The lemma is
`Integrable.const_mul : Integrable f μ → ∀ c, Integrable (fun x => c * f x) μ`; dot notation `hf.const_mul c`
means `Integrable.const_mul hf c`. Placeholders: `(f : Ω → ℝ) (c : ℝ) (hf : Integrable f μ)`. It also works
when `f` is itself a lambda: from `hY : Integrable (fun ω => Y ω ^ 2) μ`, `hY.const_mul c` proves
`Integrable (fun ω => c * Y ω ^ 2) μ`.

| Before | After |
|---|---|
| `⊢ Integrable (fun ω => c * f ω) μ` | no goals |

**R7 · `hf.add hg`** **closes** an integrability goal for a sum. The lemma is
`Integrable.add : Integrable f μ → Integrable g μ → Integrable (f + g) μ`, where `f + g` is the pointwise sum;
Lean accepts it for `fun ω => f ω + g ω` because the two unfold to the same thing. Placeholders:
`(f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)`.

| Before | After |
|---|---|
| `⊢ Integrable (fun ω => f ω + g ω) μ` | no goals |

### Splitting an integral

**R8 · `rw [integral_add hf hg]`** changes the **goal** (or, with `at h`, the context). The lemma is
`integral_add (hf : Integrable f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ`.
`f` and `g` are read off the *types* of `hf` and `hg`, so these must be stated with the exact summands
(see Traps). Placeholders: `(f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)`. For
`∫ (A + B + C)`, `+` groups to the left: split `(A + B) + C` first (with a proof for `A + B`), then `A + B`.

| Before | After |
|---|---|
| `⊢ P (∫ (ω : Ω), f ω + g ω ∂μ)` | `⊢ P (∫ (a : Ω), f a ∂μ + ∫ (a : Ω), g a ∂μ)` |

**R9 · `rw [integral_const_mul]`** changes the **goal** (or, with `at h`, the context). The lemma is
`integral_const_mul (r : ℝ) (f : Ω → ℝ) : ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ`, valid for `ℝ` and `ℂ`
(any `RCLike` field). It needs no integrability. Each `rw [integral_const_mul]` pulls out one constant, so
write it once per integral that has one. Placeholders: `(r : ℝ) (f : Ω → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (ω : Ω), r * f ω ∂μ)` | `⊢ P (r * ∫ (a : Ω), f a ∂μ)` |

### Closing the milestone

**R10 · `linarith`** **closes** a goal that is a linear combination of hypotheses (`≤`, `<`, `=` over an
ordered field such as `ℝ`). It first normalizes with ring arithmetic, so a product such as `t * t * A` is one
unknown that also matches `A * (t * t)`; integrals count as unknowns too, whatever their bound-variable
name or beta form. It cannot multiply two hypotheses together. Placeholders: `(A B t : ℝ)`.

| Before | After |
|---|---|
| `h : 0 ≤ t * t * A + B ⊢ 0 ≤ A * (t * t) + B` | no goals |

### The discriminant

**R11 · `have := discrim_le_zero h`** changes the **context**: it adds `this : discrim a b c ≤ 0`. The lemma is
`discrim_le_zero : (∀ x, 0 ≤ a * (x * x) + b * x + c) → discrim a b c ≤ 0` (over an ordered field; `ℝ`
qualifies). Lean reads `a`, `b`, `c` off `h`, so `h` must have *exactly* the shape `a * (x * x) + b * x + c`:
`x * x`, not `x ^ 2`, the `x * x` on the right of `a`, and `+ c` last. Placeholders: `(a b c : ℝ)`,
`h : ∀ x : ℝ, 0 ≤ a * (x * x) + b * x + c`.

| Before | After |
|---|---|
| `⊢ G` | `this : discrim a b c ≤ 0 ⊢ G` |

**R12 · `rw [discrim] at h`** changes the **context**: it unfolds the definition
`discrim a b c = b ^ 2 - 4 * a * c` inside `h`. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `h : discrim a b c ≤ 0 ⊢ b ^ 2 - 4 * a * c ≤ 0` | `h : b ^ 2 - 4 * a * c ≤ 0 ⊢ b ^ 2 - 4 * a * c ≤ 0` |

**R13 · `nlinarith`** **closes** a polynomial (in)equality from hypotheses. It is `linarith` plus products
of pairs of hypotheses and squares, after ring normalization, so `(2 * b) ^ 2` becomes `4 * b ^ 2` on its own.
Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `h : (2 * b) ^ 2 - 4 * a * c ≤ 0 ⊢ b ^ 2 ≤ a * c` | no goals |

### Worked combinations (W1–W4, on objects that are not the exercise's)

**W1: a square integrates to something nonnegative**, R2 with R3 in term mode:
`integral_nonneg fun _ => sq_nonneg _ : 0 ≤ ∫ ω, (f ω + g ω) ^ 2 ∂μ`. Use it as the body of a `have`.

**W2: expand an integrand**, R4 then `ring`:

```lean-goal
⊢ (fun ω => (f ω + g ω) ^ 2) = fun ω => f ω ^ 2 + 2 * (f ω * g ω) + g ω ^ 2
⊢ (f ω + g ω) ^ 2 = f ω ^ 2 + 2 * (f ω * g ω) + g ω ^ 2
```

**W3: split `∫ (3f + g)`.** First `have i1 : Integrable (fun ω => 3 * f ω) μ := hf.const_mul 3` (R6),
stated with the summand exactly as it appears in the integrand. Then R8, then R9 (which closes the goal by `rfl`):

```lean-goal
⊢ ∫ (ω : Ω), 3 * f ω + g ω ∂μ = 3 * ∫ (ω : Ω), f ω ∂μ + ∫ (ω : Ω), g ω ∂μ
⊢ ∫ (a : Ω), 3 * f a ∂μ + ∫ (a : Ω), g a ∂μ = 3 * ∫ (ω : Ω), f ω ∂μ + ∫ (ω : Ω), g ω ∂μ
```

**W4: the discriminant argument on numbers.** From `h : ∀ x : ℝ, 0 ≤ 1 * (x * x) + b * x + 1`, R11, R12, R13
prove `b ^ 2 ≤ 4`:

| Step | State |
|---|---|
| start | `⊢ b ^ 2 ≤ 4` |
| `have := discrim_le_zero h` | `this : discrim 1 b 1 ≤ 0 ⊢ b ^ 2 ≤ 4` |
| `rw [discrim] at this` | `this : b ^ 2 - 4 * 1 * 1 ≤ 0 ⊢ b ^ 2 ≤ 4` |
| `nlinarith` | no goals |

---

## Traps

- **`integral_add` matches the integrand through the types of its arguments.** If `i3 : Integrable (fun ω => A ω + B ω) μ`
  is given as the term `i1.add i2`, its type is `Integrable ((fun ω => A ω) + fun ω => B ω) μ`, and
  `rw [integral_add (i1.add i2) h]` fails with "did not find an occurrence of the pattern
  `∫ a, ((fun x => …) + …) a + … ∂μ`". State every integrability fact with a `have` and an explicit
  `Integrable (fun ω => …) μ` type matching the integrand, then pass the names.
- **Rewrite the integrand before splitting.** `h0 : 0 ≤ ∫ (X ω - t * Y ω) ^ 2` has no `+` at the top; prove
  `e : (fun ω => (X ω - t * Y ω) ^ 2) = fun ω => … + … + …` with `funext ω; ring` and `rw [e] at h0` first
  (R4, R5). Choose the summands of `e` so that each is `constant * (a function you have an Integrable for)`:
  `t * t * Y ω ^ 2`, `-2 * t * (X ω * Y ω)`, `X ω ^ 2`.
- **Match `discrim_le_zero`'s shape.** The milestone must read `a * (t * t) + b * t + c` with
  `a = μ[fun ω => Y ω ^ 2]`, `b = -2 * μ[fun ω => X ω * Y ω]`, `c = μ[fun ω => X ω ^ 2]`. After the rewrites
  `h0` reads `t * t * a + -2 * t * E[XY] + c`, which is not the same text: close the milestone with `linarith`
  (R10), not `exact`.
- `have h : T := by …`: indent the proof further than `have`, or its lines run against the outer goal.
- `rw [e] at h` rewrites only `h`; `rw [e]` alone rewrites the goal and leaves `h` untouched.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| prove `∀ t, …` | `intro t` | R1 |
| `0 ≤ ∫ F ∂μ` from `F ≥ 0` | `integral_nonneg fun ω => …` or `apply integral_nonneg; intro ω` | R2 |
| `0 ≤ a ^ 2` | `sq_nonneg _` | R3 |
| equation of functions → values | `funext ω; ring` | R4 |
| rewrite a hypothesis | `rw [e] at h` | R5 |
| `Integrable (fun ω => c * F ω) μ` | `hF.const_mul c` | R6 |
| `Integrable (fun ω => F ω + G ω) μ` | `hF.add hG` (inside a `have` with that explicit type) | R7 |
| `∫ (F + G) = ∫ F + ∫ G` | `rw [integral_add hF hG]` | R8 |
| `∫ r * F = r * ∫ F` | `rw [integral_const_mul]` (once per constant) | R9 |
| linear arithmetic over atoms | `linarith` | R10 |
| `∀ x, 0 ≤ a x² + b x + c` → `discrim a b c ≤ 0` | `have := discrim_le_zero key` | R11 |
| unfold `discrim` | `rw [discrim] at this` | R12 |
| polynomial inequality from hypotheses | `nlinarith` | R13 |
| see the state | infoview | |
