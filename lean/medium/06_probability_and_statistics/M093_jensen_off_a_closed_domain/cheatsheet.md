# M093 · Jensen off a closed domain: E[1/X] ≥ 1/E[X]: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `have`, `exact`, `intro`, `rw`, `simp`,
`ring`, `linarith`, `∀`/`∃`/`∧`, anonymous functions `fun ω => …`. Helpful but not required: M084
(Markov) and M087 (Cantelli), which use the same integral lemmas. **New here:** Mathlib's measure theory
and probability: probability measures, the integral `∫ ω, f ω ∂μ` and `μ[f]`, `Integrable`,
`Function.support`, `μ.real`; the tactics `set`, `calc`, `field_simp`, `positivity`, `nlinarith`.

**The maths.** Let `(Ω, μ)` be a probability space (`μ Ω = 1`) and `X : Ω → ℝ` with `X ω > 0` for every
`ω`, `X` and `1/X` integrable. Write `m = E X = ∫ X dμ`.

1. **`m > 0`.** `X ≥ 0`, so `∫ X dμ > 0` iff the set where `X ≠ 0` (the *support* of `X`) has positive
   measure. Since `X > 0` everywhere, the support is all of `Ω`, of measure `1 > 0`.
2. **Tangent line.** For `φ(x) = 1/x` the tangent at `m` is `ℓ(x) = φ(m) + φ'(m)(x - m) = 2/m - x/m²`.
   For `x > 0`, `1/x - ℓ(x) = (x - m)² / (x m²) ≥ 0`, so `ℓ(x) ≤ 1/x`. Multiplied by `x m² > 0` this is
   `x (2m - x) ≤ m²`, i.e. `(x - m)² ≥ 0`.
3. **Integrate.** `E ℓ(X) = 2/m - E X / m² = 2/m - 1/m = 1/m` (linearity, `E[c] = c`). Monotonicity of the
   integral turns `ℓ(X) ≤ 1/X` into `1/m = E ℓ(X) ≤ E[1/X]`.

Why not Mathlib's Jensen `ConvexOn.map_integral_le` (used in E102)? It needs the convex set to be
**closed**, and `(0, ∞)` is not. Nor can you use `[0, ∞)`: Lean defines `0⁻¹ = 0`, so `x ↦ x⁻¹` is not
convex on `[0, ∞)`. The tangent-line argument above is Jensen's proof specialised to `1/x`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`refine`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. `G : Prop` with `k : T → G` is a goal the entry does not touch; `k` only shows
  which fact `T` the step added.
- Placeholders are written as Lean binders. `{Ω : Type}` is any type (the sample space).
  `[MeasurableSpace Ω]` says `Ω` carries a σ-algebra (the events); `(μ : Measure Ω)` is a measure on it;
  `[IsProbabilityMeasure μ]` says `μ Set.univ = 1` (it implies `IsFiniteMeasure μ`, which `integrable_const`
  asks for). A bracket `[…]` is a requirement Lean finds by itself (a *type class*).
- When a new hypothesis contains `, ` (every integral does), the cell says "context gains" in words.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `{Ω : Type*}` (in the spec) | `Ω` is a type in any universe; the guide uses `{Ω : Type}`, which works the same way for every lemma here |
| `[MeasurableSpace Ω]`, `Measure Ω` | `Ω` carries a σ-algebra of events; `μ : Measure Ω` is a (countably additive) measure on it |
| `[IsProbabilityMeasure μ]` | `μ Set.univ = 1`; Lean finds this fact by itself wherever a lemma needs it (R6, R14, R21) |
| `μ[X]` (in the source) | the expectation `E X = ∫ ω, X ω ∂μ`; the infoview prints it as `∫ (x : Ω), X x ∂μ` |
| `∫ (x : Ω), f x ∂μ` | the (Bochner) integral of `f : Ω → ℝ` against `μ`; Lean defines it as `0` when `f` is not integrable |
| `∫ (x : Ω), (fun ω => (X ω)⁻¹) x ∂μ` | `μ[fun ω => (X ω)⁻¹]` printed without β-reducing: the integrand is `(X x)⁻¹`. `rw` and `simp` still match it |
| `∫ (a : Ω), 2 / m ∂μ`, `∫ (_ω : Ω), c ∂μ` | the integral of a constant: the integrand does not mention the bound variable (a leading `_` in its name says it is unused); R20 evaluates it |
| `x⁻¹` | `1 / x`; Lean sets `0⁻¹ = 0` |
| `Integrable f μ` | `f` is a.e. strongly measurable and `∫ ‖f‖ dμ < ∞`, i.e. `f ∈ L¹(μ)` |
| `0 ≤ f` (functions) | pointwise: `∀ ω, 0 ≤ f ω` (R2); `f ≤ g` likewise (R22) |
| `Function.support f` | the set `{ω \| f ω ≠ 0}` (R4) |
| `Set.univ` | the whole type `Ω` as a set |
| `μ s` | the measure of the set `s`, a value in `ℝ≥0∞ = [0, ∞]`; `μ Set.univ = 1` for a probability measure (R6) |
| `μ.real s` | `μ s` converted to a real number: `P(s)` (R20, R21) |
| `c • x` | scalar multiplication; for `c x : ℝ` it is `c * x`, and `1 • x = x` (R21) |
| `m : ℝ := ∫ (x : Ω), X x ∂μ` | a local definition made by `set` (R7): `m` is that integral, by definition |
| `inst✝ : …` | an unnamed type-class hypothesis (`[MeasurableSpace Ω]` etc.) |

---

## Part 1 · `jensen_inv`

Statement: if `X ω > 0` for all `ω`, and `X`, `fun ω => (X ω)⁻¹` are integrable, then
`(μ[X])⁻¹ ≤ μ[fun ω => (X ω)⁻¹]`. Plan: prove `0 < μ[X]` (R1–R6), name the mean `m` (R7), prove the
tangent-line bound pointwise (R8–R13), prove the line integrable (R14–R16), then a two-step `calc`:
compute `E ℓ(X) = 1/m` (R17–R21, R11) and integrate the bound (R22).

### A positive integrand has a positive integral

**R1 · `rw [integral_pos_iff_support_of_nonneg hf hi]`** changes the **goal**. The lemma is
`0 ≤ f → Integrable f μ → (0 < ∫ x, f x ∂μ ↔ 0 < μ (Function.support f))`: for a nonnegative integrable `f`,
the integral is positive exactly when `f` is nonzero on a set of positive measure. Placeholders:
`(f : Ω → ℝ) (hf : 0 ≤ f) (hi : Integrable f μ)`. In the exercise the goal becomes
`0 < μ (Function.support X)`.

| Before | After |
|---|---|
| `⊢ 0 < ∫ (ω : Ω), f ω ∂μ` | `⊢ 0 < μ (Function.support f)` |

**R2 · `fun ω => (h ω).le`** changes the **context** (written as a `have`, or passed straight to R1 as its
first argument). `0 ≤ f` for a function means `∀ ω, 0 ≤ f ω`, so a function proves it. `LT.lt.le` turns
`0 < f ω` into `0 ≤ f ω`; `(h ω).le` is the dot-notation call. Placeholders:
`(f : Ω → ℝ) (h : ∀ ω, 0 < f ω)`.

| Before | After |
|---|---|
| `⊢ G` | `hf : 0 ≤ f ⊢ G` |

**R3 · `ext ω`** on an equation of sets changes the **goal and the context**. It uses `Set.ext`: two sets
are equal when they have the same members. Placeholders: `(s t : Set Ω)`. In the exercise you prove
`Function.support X = Set.univ` this way.

| Before | After |
|---|---|
| `⊢ s = t` | `ω : Ω ⊢ ω ∈ s ↔ ω ∈ t` |

**R4 · `simp only [Function.mem_support, Set.mem_univ, iff_true]`** changes the **goal**.
`Function.mem_support : x ∈ Function.support f ↔ f x ≠ 0`; `Set.mem_univ : x ∈ Set.univ` (it is `True`);
`iff_true : (p ↔ True) = p`. Placeholders: `(f : Ω → ℝ) (ω : Ω)`. Plain `simp [hne]` (with
`hne : f ω ≠ 0` from R5) does this and closes the goal in one go.

| Before | After |
|---|---|
| `⊢ ω ∈ Function.support f ↔ ω ∈ Set.univ` | `⊢ f ω ≠ 0` |

**R5 · `ha.ne'`** (`LT.lt.ne'`) changes the **context**: from `ha : 0 < a` it gives `a ≠ 0` (the `'` means the
sides are swapped: plain `ha.ne` is `0 ≠ a`). Placeholders: `(a : ℝ) (ha : 0 < a)`. Used twice: `(hpos ω).ne'`
for the support, `hm.ne'` for R8.

| Before | After |
|---|---|
| `⊢ G` | `hne : a ≠ 0 ⊢ G` |

**R6 · `rw [measure_univ]`** changes the **goal**: `measure_univ : μ Set.univ = 1` for a probability measure.
The `1` and `0` here live in `ℝ≥0∞`; `exact zero_lt_one` closes `0 < 1`. Placeholders:
`(μ : Measure Ω) [IsProbabilityMeasure μ]`. In the exercise `simp [hs]` (with `hs : Function.support X = Set.univ`)
rewrites `hs`, applies `measure_univ` and closes `0 < 1` by itself (W1).

| Before | After |
|---|---|
| `⊢ 0 < μ Set.univ` | `⊢ 0 < 1` |

### Naming the mean

**R7 · `set m := e`** changes the **context and the goal**: it adds a local definition `m : ℝ := e` and replaces
every `e` in the goal **and in the hypotheses** by `m`. Placeholders: `(f : Ω → ℝ)`, `e := μ[f]`,
`(h0 : 0 < μ[f])`. After the step the context gains `m : ℝ := ∫ (x : Ω), f x ∂μ`, and `h0` reads `0 < m`.
`m` is still that integral by definition, so lemmas about `μ[X]` keep working on `m`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : Ω), f x ∂μ)` | `h0 : 0 < m ⊢ P m` |

### Clearing denominators in a real inequality

**R8 · `rw [div_sub_div a c hb hd]`** changes the **goal**. The lemma is
`div_sub_div (a c : K) (hb : b ≠ 0) (hd : d ≠ 0) : a / b - c / d = (a * d - b * c) / (b * d)` for a field `K`
(`ℝ` here). Write `div_sub_div _ _ hb hd` to let Lean find `a`, `c`. Placeholders: `(a b c d : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a / b - c / d)` | `⊢ P ((a * d - b * c) / (b * d))` |

**R9 · `positivity`** **closes** a goal `0 < e`, `0 ≤ e` or `e ≠ 0` where `e` is built from `+`, `*`, `^`, `/`
and atoms it knows are positive (hypotheses `0 < a` in the context, numerals). Use it as `(by positivity)`
for the side conditions of R8 and R10, e.g. `m ^ 2 ≠ 0`, `0 < m * m ^ 2`.

**R10 · `rw [div_le_iff₀ hc]`** changes the **goal**. The lemma is `0 < c → (b / c ≤ a ↔ b ≤ a * c)`.
Placeholders: `(a b c : ℝ) (hc : 0 < c)`.

| Before | After |
|---|---|
| `⊢ b / c ≤ a` | `⊢ b ≤ a * c` |

**R11 · `field_simp`** changes the **goal**: it multiplies out every denominator (and `⁻¹`) it can prove
nonzero, using hypotheses such as `0 < a` or `a ≠ 0` in the context, and then normalises. Its output shape
is hard to predict: look at the infoview before the next step. Placeholders: `(a b c : ℝ) (ha : 0 < a)`.
In the exercise it is used twice: on the tangent-line goal (with `hx : 0 < X ω` in the context: run
`have hx := hpos ω` first) and on the final `m⁻¹ = 2 / m - m / m ^ 2`.

| Before | After |
|---|---|
| `⊢ c ≤ a⁻¹ * b` | `⊢ c * a ≤ b` |

**R12 · `sq_nonneg a`** changes the **context** (or serves as a hint to R13): `sq_nonneg a : 0 ≤ a ^ 2`.
Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hsq : 0 ≤ a ^ 2 ⊢ G` |

**R13 · `nlinarith [t₁, …]`** **closes** a goal that is a linear consequence of the hypotheses, the hints `tᵢ`
and their pairwise products. It does not expand `(x - m) ^ 2` from nothing: give it `sq_nonneg (x - m)`.
Example: `2 * a * b ≤ a ^ 2 + b ^ 2` from `sq_nonneg (a - b)`.

### Integrability facts

**R14 · `integrable_const c`** changes the **context**: a constant is integrable for a finite measure.
Placeholders: `(c : ℝ)`, `[IsProbabilityMeasure μ]`. Write `integrable_const _` and Lean finds `c`.

| Before | After |
|---|---|
| `⊢ G` | `hc : Integrable (fun x => c) μ ⊢ G` |

**R15 · `hf.sub hg`** (`Integrable.sub`) changes the **context**: a difference of integrable functions is
integrable. Placeholders: `(f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)`. Stated with a type,
it gives the lambda form you need: `have hl : Integrable (fun ω => … - …) μ := (integrable_const _).sub …`.

| Before | After |
|---|---|
| `⊢ G` | `hs : Integrable (fun ω => f ω - g ω) μ ⊢ G` |

**R16 · `hf.div_const c`** (`Integrable.div_const`) changes the **context**: `f / c` is integrable when `f` is.
Placeholders: `(f : Ω → ℝ) (hf : Integrable f μ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hd : Integrable (fun x => f x / c) μ ⊢ G` |

### Computing and comparing integrals

**R17 · `calc`** changes the **goal list**: a chain `a = b`, `b ≤ c` proves `a ≤ c`, and each step is its own
goal. Write each step as `_ rel rhs := proof`, where `_` stands for the previous right-hand side; a step
proved by `by …` is indented under it. `?_` leaves a step open as a goal. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ≤ c` | `⊢ a = b`, `⊢ b ≤ c` |

**R18 · `integral_div`** changes the **context** when used as a `have`. The lemma is
`integral_div (r : ℝ) (f : Ω → ℝ) : ∫ a, f a / r ∂μ = (∫ a, f a ∂μ) / r`. Placeholders: `(f : Ω → ℝ) (r : ℝ)`.
`have h2 : ∫ ω, f ω / r ∂μ = (∫ ω, f ω ∂μ) / r := integral_div r f` adds that equation; then `rw [h2]`.
A bare `rw [integral_div]` rewrites the **first** integral of the shape `∫ … / r`, and a constant `2 / m`
has that shape too (second example in the guide):

| Before | After `rw [integral_div]` |
|---|---|
| `⊢ P (∫ (_ω : Ω), c / r ∂μ - ∫ (ω : Ω), f ω / r ∂μ)` | `⊢ P ((∫ (a : Ω), c ∂μ) / r - ∫ (ω : Ω), f ω / r ∂μ)` |

So state `h2` with the integrand you want (in the exercise `X ω / m ^ 2`, giving `m / m ^ 2` because
`μ[X]` is `m` by definition).

**R19 · `rw [integral_sub hf hg]`** changes the **goal**: the integral of a difference splits. The lemma is
`Integrable f μ → Integrable g μ → ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ`. Placeholders:
`(f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)`. In the exercise `f` is the constant `2 / m`
(R14) and `g` is `X ω / m ^ 2` (R16).

| Before | After |
|---|---|
| `⊢ P (∫ (ω : Ω), f ω - g ω ∂μ)` | `⊢ P (∫ (a : Ω), f a ∂μ - ∫ (a : Ω), g a ∂μ)` |

**R20 · `rw [integral_const]`** changes the **goal**: `integral_const c : ∫ x, c ∂μ = μ.real Set.univ • c`
(the measure of the whole space times `c`). Placeholders: `(c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (_ω : Ω), c ∂μ)` | `⊢ P (μ.real Set.univ • c)` |

**R21 · `probReal_univ`, then `one_smul`** change the **goal**. `probReal_univ : μ.real Set.univ = 1` for a
probability measure; `one_smul : 1 • c = c`. Write both at once: `simp only [probReal_univ, one_smul]`.
Placeholders: `(c : ℝ)`, `[IsProbabilityMeasure μ]`.

| Before | After `rw [probReal_univ]` | After `rw [one_smul]` |
|---|---|---|
| `⊢ P (μ.real Set.univ • c)` | `⊢ P (1 • c)` | `⊢ P c` |

**R22 · `integral_mono hf hg hle`** changes the **goal** (with `refine … ?_`) or closes it. The lemma is
`Integrable f μ → Integrable g μ → f ≤ g → ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ`, and `f ≤ g` is `∀ ω, f ω ≤ g ω` by
definition, so a hypothesis `hle : ∀ ω, f ω ≤ g ω` fits as the third argument. Placeholders:
`(f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)`. In the exercise's last `calc` step Lean fails
with ``don't know how to synthesize implicit argument `f` ``: name it,
`integral_mono (f := fun ω => …) hl hinv hpt` (W3).

| Before | After `refine integral_mono hf hg ?_` |
|---|---|
| `⊢ ∫ (ω : Ω), f ω ∂μ ≤ ∫ (ω : Ω), g ω ∂μ` | `⊢ f ≤ g` |

### Worked combinations (W1–W4, on statements that are not the exercise's)

**W1: the mean of `exp f` is positive.** R1 with `fun ω => (hp ω).le` (R2), then R3 and `simp [(hp ω).ne']`
(R4, R5) for the support, then `simp [hs]` (R6):

```lean-goal
⊢ 0 < ∫ (ω : Ω), Real.exp (f ω) ∂μ
⊢ 0 < μ (Function.support fun ω => Real.exp (f ω))
```

**W2: the mean of the line `3 - f / 2`.** `have h2 := integral_div 2 f` first (R18), then R19 with R14, R16,
then `rw [h2, integral_const]` (R20) and `simp only [probReal_univ, one_smul]` (R21):

```lean-goal
⊢ ∫ (ω : Ω), 3 - f ω / 2 ∂μ = 3 - (∫ (ω : Ω), f ω ∂μ) / 2
⊢ ∫ (a : Ω), 3 ∂μ - ∫ (a : Ω), f a / 2 ∂μ = 3 - (∫ (ω : Ω), f ω ∂μ) / 2
⊢ μ.real Set.univ • 3 - (∫ (ω : Ω), f ω ∂μ) / 2 = 3 - (∫ (ω : Ω), f ω ∂μ) / 2
```

**W3: the two-step `calc`.** Goal `∫ f - 1 ≤ ∫ g` from `∀ ω, f ω - 1 ≤ g ω`: the `=` step computes the mean of
`f - 1` (R19, R20, R21), the `≤` step is `integral_mono (f := fun ω => f ω - 1) …` (R22). This is the shape of
the exercise's final `calc`.

**W4: `3 / x - 2 / x ^ 2 ≤ 9 / 8` for `x > 0`.** R8 with `hx.ne'` (R5) and `(by positivity)` (R9), then R10,
then R13 with the hint `mul_nonneg hx.le (sq_nonneg (3 * x - 4))` (multiplied out the claim is
`x (3x - 4)² ≥ 0`):

```lean-goal
⊢ 3 / x - 2 / x ^ 2 ≤ 9 / 8
⊢ (3 * x ^ 2 - x * 2) / (x * x ^ 2) ≤ 9 / 8
⊢ 3 * x ^ 2 - x * 2 ≤ 9 / 8 * (x * x ^ 2)
```

---

## Traps

- Library Jensen (`ConvexOn.map_integral_le`) does not apply: `(0, ∞)` is not closed, and `x⁻¹` is not convex
  on `[0, ∞)` because `0⁻¹ = 0` in Lean. Use the tangent line.
- In the last `calc` step, `integral_mono hl hinv hpt` fails with "don't know how to synthesize implicit
  argument `f`". Pass the function explicitly: `integral_mono (f := fun ω => 2 / m - X ω / m ^ 2) hl hinv hpt`.
- A bare `rw [integral_div]` may rewrite `∫ 2 / m` (a constant over `m`) instead of `∫ X ω / m ^ 2` (R18).
  State `h2` with `have … := integral_div _ _` and `rw [h2]`.
- Prove `hm : 0 < μ[X]` **before** `set m := μ[X]`: `set` then turns it into `hm : 0 < m`, which `field_simp`,
  `positivity` and `hm.ne'` need.
- `field_simp` only clears `X ω` from a denominator if it can see `X ω ≠ 0`: put `hx : 0 < X ω` in the context
  first (`have hx := hpos ω`).
- `nlinarith` needs the square as a hint: `nlinarith [sq_nonneg (X ω - m)]`.
- `have h : T` with no `:= …` makes `T` your next goal instead of adding `h` (TACTIC_STATES, "Adding facts").

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `0 < ∫ f` for `f ≥ 0` → positive measure of the support | `rw [integral_pos_iff_support_of_nonneg hf hi]` | R1 |
| `0 ≤ f` from `∀ ω, 0 < f ω` | `fun ω => (h ω).le` | R2 |
| set equation → membership | `ext ω` | R3 |
| `ω ∈ support f` → `f ω ≠ 0` | `simp [Function.mem_support]`, or `simp [hne]` | R4 |
| `a ≠ 0` from `0 < a` | `ha.ne'` | R5 |
| `μ Set.univ = 1` | `measure_univ` (`simp` uses it) | R6 |
| name a big term everywhere | `set m := μ[X]` | R7 |
| `a / b - c / d` → one fraction | `rw [div_sub_div _ _ hb hd]` | R8 |
| side goals `0 < e`, `e ≠ 0` | `(by positivity)` | R9 |
| `b / c ≤ a` → `b ≤ a * c` | `rw [div_le_iff₀ hc]` | R10 |
| clear all denominators | `field_simp` | R11 |
| `0 ≤ a ^ 2` | `sq_nonneg a` | R12 |
| polynomial inequality | `nlinarith [sq_nonneg (x - m)]` | R13 |
| integrable constant / difference / quotient | `integrable_const _`, `hf.sub hg`, `hf.div_const c` | R14–R16 |
| chain `=` then `≤` | `calc a = b := … ` / `_ ≤ c := …` | R17 |
| `∫ f / r = (∫ f) / r` | `have h2 : … := integral_div _ _` | R18 |
| `∫ (f - g) = ∫ f - ∫ g` | `rw [integral_sub hf hg]` | R19 |
| `∫ c = c` (probability measure) | `rw [integral_const]; simp only [probReal_univ, one_smul]` | R20, R21 |
| integrate a pointwise bound | `integral_mono (f := fun ω => …) hf hg hle` | R22 |
| see the state | infoview | |
