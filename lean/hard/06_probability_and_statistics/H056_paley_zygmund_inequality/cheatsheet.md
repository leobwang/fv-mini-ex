# H056 · Paley–Zygmund inequality: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `have`, `exact`, `intro`, `rw`, `funext`,
`ring`, `∀`/`∧`/`¬`. Helpful but not required: M090 (Cauchy–Schwarz for expectations), whose
discriminant argument Part 2 repeats with `Y = 1_A`. **New here:** Mathlib's measure theory and
probability: measures and probability measures, the Bochner integral `∫ ω, f ω ∂μ`, `Integrable`,
`MemLp` (finite p-th moment), `Measurable`/`MeasurableSet`, "almost everywhere" (`∀ᵐ`), indicator
functions `Set.indicator`, `μ.real`, and the tactics `linarith`, `nlinarith`, `linear_combination`.

**The maths.** Let `(Ω, μ)` be a probability space, `X ≥ 0` a random variable with `E[X²] < ∞`,
`m = E X`, `0 ≤ θ ≤ 1`, and `A = {ω | θ m < X ω}` (the event "X exceeds a θ-fraction of its mean").
`1_A` is the indicator of `A` (1 on `A`, 0 off it).

1. **Split the mean** (`split_mean`). Pointwise `X ≤ θ m + X·1_A`: on `A` the right side is `θ m + X ≥ X`
   (as `θ m ≥ 0`); off `A`, `X ≤ θ m`. Integrate: `m ≤ θ m + E[X 1_A]`, so `(1 - θ) m ≤ E[X 1_A]`.
2. **Cauchy–Schwarz** (`cs_indicator`). For every real `t`,
   `0 ≤ E[(X - t 1_A)²] = E[X²] - 2t E[X 1_A] + t² P(A)` (using `1_A² = 1_A`). A quadratic
   `a t² + b t + c` that is never negative has discriminant `b² - 4ac ≤ 0`, so
   `4 E[X 1_A]² ≤ 4 E[X²] P(A)`.
3. **Combine** (`paley_zygmund`). `0 ≤ (1 - θ) m ≤ E[X 1_A]`, square (squaring is monotone on `[0, ∞)`),
   then apply step 2: `(1 - θ)² m² ≤ E[X 1_A]² ≤ E[X²] P(A)`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`apply`/`refine`. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the proof
state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. `G : Prop` with `h : T → G` is a goal the entry does not touch; `h` only shows
  which fact `T` the step added.
- Placeholders are written as Lean binders. `{Ω : Type}` is any type (the sample space). `[MeasurableSpace Ω]`
  says `Ω` carries a σ-algebra (the events); `(μ : Measure Ω)` is a measure on it;
  `[IsProbabilityMeasure μ]` says `μ Ω = 1`. A bracket `[…]` is a requirement Lean finds by itself (a
  *type class*).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Ω : Type u_1` | `{Ω : Type*}` in the statement: `Ω` is a type in some universe `u_1` (ignore the universe) |
| `μ[X]` (in the source) | the expectation `E X = ∫ ω, X ω ∂μ`; the infoview prints it as `∫ (x : Ω), X x ∂μ` |
| `μ[fun ω => X ω ^ 2]` | `E[X²]`; printed as `∫ (x : Ω), (fun ω => X ω ^ 2) x ∂μ` (an unreduced `fun`, same value) |
| `∫ (ω : Ω), f ω ∂μ` | the (Bochner) integral of `f : Ω → ℝ` against `μ`; it is `0` if `f` is not integrable |
| `θ * ∫ (x : Ω), X x ∂μ < X ω` | the integral's body runs up to `∂μ`, so this is `θ * (E X) < X ω` |
| `∫ (a : Ω), X a ∂μ` vs `∫ (x : Ω), X x ∂μ` | the same integral: the bound variable's name is irrelevant, and `rw` may rename it |
| `μ.real A` | `μ A` as a real number: `P(A)` for a probability measure (`μ A` itself lives in `[0, ∞]`) |
| `{ω \| Q ω}` | the set (event) of `ω` with `Q ω`; `ω ∈ {ω \| Q ω}` simplifies to `Q ω` |
| `A.indicator f ω` | `Set.indicator A f ω = if ω ∈ A then f ω else 0`; with `f = 1` it is `1_A(ω)` |
| `1 : Ω → ℝ` | the constant function `fun _ => 1`; `A.indicator 1` prints without the type |
| `Integrable f μ` | `f` is measurable (a.e. strongly) and `∫ ‖f‖ ∂μ < ∞`, i.e. `f ∈ L¹(μ)` |
| `MemLp f 2 μ` | `f ∈ L²(μ)`: `E[f²] < ∞` (the `2` is an extended real `ℝ≥0∞`) |
| `Measurable f`, `MeasurableSet A` | preimages of measurable sets are events; `A` is an event |
| `AEStronglyMeasurable g μ` | `g` agrees a.e. with a limit of simple functions; follows from `Measurable g` (R4) |
| `∀ᵐ (x : Ω) ∂μ, p x` | `p x` holds for `μ`-almost every `x` (outside a null set) |
| `‖g x‖` | the norm; for a real number, `|g x|` |
| `f ≤ g`, `0 ≤ f` (functions) | pointwise: `∀ ω, f ω ≤ g ω`, `∀ ω, 0 ≤ f ω` |
| `Set.univ` | the whole space `Ω` as a set; `μ.real Set.univ = 1` for a probability measure |
| `r • c` | scalar multiplication; for two reals it is `r * c` (R16) |
| `-2 * t * f` | `(-2 * t) * f`: `*` groups to the left, so Lean drops those brackets |
| `discrim a b c` | `b ^ 2 - 4 * a * c` (R26) |
| `case pos`, `case neg` | the two goals after `by_cases`: `h : Q` and `h : ¬Q` |
| `inst✝ : …` | an unnamed type-class hypothesis (`[MeasurableSpace Ω]` etc.) |

---

## Part 1 · `split_mean` (milestone)

Statement: with `m = μ[X]` and `A = {ω | θ * m < X ω}`, `m ≤ θ * m + ∫ ω, X ω * A.indicator 1 ω ∂μ`. Prove
it first: `paley_zygmund` uses it in its `calc` (Part 3). Plan: name three facts (R1, R2, R3–R6), then a
`calc` (R9) with an `integral_mono` step (R10–R14) and an `integral_add` step (R15, R16).

### Integrability and measurability facts

**R1 · `MemLp.integrable`** changes the **context**. `hf.integrable one_le_two : Integrable f μ` from
`hf : MemLp f 2 μ` on a finite measure (`1 ≤ 2`: L² ⊆ L¹ when `μ Ω < ∞`). Placeholders:
`{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : MemLp f 2 μ)`.

| Before | After |
|---|---|
| `⊢ G` | `hi : Integrable f μ ⊢ G` |

**R2 · `measurableSet_lt`** changes the **context**. Lemma: `Measurable f → Measurable g → MeasurableSet
{a | f a < g a}`; the constant side is `measurable_const`. Placeholders: `(f : Ω → ℝ) (hf : Measurable f)
(c : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G` (goal unchanged); the context gains `hA : MeasurableSet {ω \| c < f ω}` |

**R3 · `refine hf.mul_bdd (c := 1) ?_ ?_`** changes the **goal list**. Lemma `Integrable.mul_bdd`:
`Integrable f μ → AEStronglyMeasurable g μ → (∀ᵐ x ∂μ, ‖g x‖ ≤ c) → Integrable (fun x => f x * g x) μ`
(integrable times a.e.-bounded is integrable). `(c := 1)` fixes the bound. Placeholders:
`(f g : Ω → ℝ) (hf : Integrable f μ)`. For `g = A.indicator 1` the first new goal is R4 + R5, the second
R6 + R7 + R8.

| Before | After |
|---|---|
| `⊢ Integrable (fun ω => f ω * g ω) μ` | `⊢ AEStronglyMeasurable g μ`, `⊢ ∀ᵐ (x : Ω) ∂μ, ‖g x‖ ≤ 1` |

**R4 · `Measurable.aestronglyMeasurable`** changes the **goal**: for real-valued `g`, measurable is
enough. As a term: `hg.aestronglyMeasurable`. Placeholders: `(g : Ω → ℝ)`.

| Before | After |
|---|---|
| `⊢ AEStronglyMeasurable g μ` | `⊢ Measurable g` |

**R5 · `Measurable.indicator`** changes the **goal list**. Lemma: `Measurable f → MeasurableSet s →
Measurable (s.indicator f)`. The constant `1` is closed by `measurable_const`. As a term:
`(measurable_const.indicator hA).aestronglyMeasurable` does R4 and R5 at once. Placeholders: `(A : Set Ω)
(hA : MeasurableSet A)`.

| Before | After |
|---|---|
| `⊢ Measurable (A.indicator 1)` | `⊢ Measurable 1`, `⊢ MeasurableSet A` |

**R6 · `ae_of_all`** changes the **goal**: what holds everywhere holds almost everywhere. Lemma:
`(∀ a, p a) → ∀ᵐ a ∂μ, p a`; as a term `ae_of_all _ fun ω => ?_` leaves the goal for one `ω`. Placeholders:
`(p : Ω → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ᵐ (ω : Ω) ∂μ, p ω` | `⊢ ∀ (a : Ω), p a` |

### Indicators, case splits, integrating inequalities

**R7 · `by_cases h : Q`** changes the **goal list and the context**: two goals, one with `h : Q`, one with
`h : ¬Q`. Placeholders: `(Q G : Prop)`. Lean's default logic is classical here, so any `Q` works.

| Before | After |
|---|---|
| `⊢ G` | `h : Q ⊢ G`, `h : ¬Q ⊢ G` |

**R8 · `simp [Set.indicator, h]`** changes the **goal**: it unfolds `Set.indicator` to the `if`, simplifies
`ω ∈ {x | Q x}` to `Q ω`, and uses `h` to pick the branch. `(1 : Ω → ℝ) ω` simplifies to `1`, and
`‖1‖ ≤ 1`, `‖0‖ ≤ 1` are closed. Placeholders: `(Q : Ω → Prop) (f : Ω → ℝ) (ω : Ω)`.

Before, in both examples:

```lean-goal
⊢ P ({x | Q x}.indicator f ω)
```

After, with `h : Q ω` and with `h : ¬Q ω`:

```lean-goal
⊢ P (f ω)
⊢ P 0
```

In `split_mean`, after the pointwise goal `X ω ≤ θ * m + X ω * 1_A(ω)`: in the `pos` case `simp` cancels
`X ω` and leaves `0 ≤ θ * m` (R12, R13); in the `neg` case it leaves `X ω ≤ θ * m`, which `h` gives (R14).

**R9 · `calc`** changes the **goal list**: one goal `a ≤ c` becomes one goal per step. Write `:= ?_` to
leave a step as a goal, or `:= by tac` / `:= term` to prove it inline. `_` at the start of a line means
"the previous right-hand side", and the last `_` may stand for the goal's right side.
Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ≤ c` | `⊢ a ≤ b`, `⊢ b = c` |

**R10 · `refine integral_mono hf hg fun ω => ?_`** changes the **goal and the context**. Lemma
`integral_mono : Integrable f μ → Integrable g μ → f ≤ g → ∫ f ∂μ ≤ ∫ g ∂μ`. `f ≤ g` on functions is
`∀ ω, f ω ≤ g ω`, so `fun ω => ?_` introduces `ω`. Placeholders: `(f g : Ω → ℝ) (hf : Integrable f μ)
(hg : Integrable g μ)`. Here `μ[X]` is the left integral, so `hf` is R1's fact.

| Before | After |
|---|---|
| `⊢ ∫ (ω : Ω), f ω ∂μ ≤ ∫ (ω : Ω), g ω ∂μ` | `ω : Ω ⊢ f ω ≤ g ω` |

**R11 · `(integrable_const c).add hf`** changes the **context**. `integrable_const c : Integrable (fun _ => c) μ`
(finite measure), `Integrable.add : Integrable f μ → Integrable g μ → Integrable (f + g) μ`; Lean accepts the
result as a statement about `fun ω => c + f ω`. Placeholders: `(f : Ω → ℝ) (hf : Integrable f μ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hs : Integrable (fun ω => c + f ω) μ ⊢ G` |

**R12 · `apply mul_nonneg`** changes the **goal list**. Lemma: `0 ≤ a → 0 ≤ b → 0 ≤ a * b`. Placeholders:
`(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ a * b` | `⊢ 0 ≤ a`, `⊢ 0 ≤ b` |

**R13 · `apply integral_nonneg`** changes the **goal**. Lemma: `0 ≤ f → 0 ≤ ∫ ω, f ω ∂μ`. A hypothesis
`hnn : ∀ ω, 0 ≤ f ω` is accepted for `0 ≤ f`, so as a term: `integral_nonneg hnn`. No integrability needed.
Placeholders: `(f : Ω → ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ ∫ (ω : Ω), f ω ∂μ` | `⊢ 0 ≤ f` |

**R14 · `linarith`** **closes** a goal that follows from the hypotheses by adding them with nonnegative
coefficients (linear arithmetic over ordered fields). It reads `¬ a < b` as `b ≤ a`. Treats products of
variables, integrals and `μ.real A` as atoms. `linarith [t]` also uses the extra fact `t`.

| Before | After |
|---|---|
| `h : ¬c < x ⊢ x ≤ c + 0` | closed |

### Computing integrals

**R15 · `rw [integral_add hf hg]`** changes the **goal**. Lemma `integral_add : Integrable f μ →
Integrable g μ → ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ`. The left side is found by matching `f` and
`g` as they are stated in `hf` and `hg`, so state them as `fun ω => …` with exactly the summands of the
integrand (Traps). Placeholders: `(f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (ω : Ω), f ω + g ω ∂μ)` | `⊢ P (∫ (a : Ω), f a ∂μ + ∫ (a : Ω), g a ∂μ)` |

**R16 · `rw [integral_const]`, then `simp`** changes the **goal**. Lemma: `∫ x, c ∂μ = μ.real Set.univ • c`;
`simp` knows `μ.real Set.univ = 1` for a probability measure and `1 • c = c`. A plain `simp` does both
steps. Placeholders: `[IsProbabilityMeasure μ] (c : ℝ)`.

| Before | After `rw [integral_const]` | After `simp` |
|---|---|---|
| `⊢ P (∫ (_ω : Ω), c ∂μ)` | `⊢ P (μ.real Set.univ • c)` | `⊢ P c` |

---

## Part 2 · `cs_indicator` (milestone)

Statement: `(∫ ω, X ω * A.indicator 1 ω ∂μ) ^ 2 ≤ μ[fun ω => X ω ^ 2] * μ.real A` for `X ∈ L²` and an
event `A`. Cauchy–Schwarz `E[X·1_A]² ≤ E[X²]·E[1_A²]` with `E[1_A²] = E[1_A] = P(A)`. Prove it before
`paley_zygmund` (last `calc` step, Part 3). Plan: integrability facts (R17, R18, R3–R8, R21); the fact
`1_A(ω)² = 1_A(ω)` (R7, R8); the key quadratic bound for every `t` (R19–R24); then the discriminant
(R25–R27).

**R17 · `hf.integrable_sq`** changes the **context**. `MemLp.integrable_sq : MemLp f 2 μ →
Integrable (fun x => f x ^ 2) μ`. Placeholders: `(f : Ω → ℝ) (hf : MemLp f 2 μ)`.

| Before | After |
|---|---|
| `⊢ G` | `h2 : Integrable (fun x => f x ^ 2) μ ⊢ G` |

**R18 · `(integrable_const 1).indicator hA`** changes the **context**. `Integrable.indicator : Integrable f μ →
MeasurableSet s → Integrable (s.indicator f) μ`. Write the type with `(1 : Ω → ℝ)`, or Lean cannot tell
which `1`. Placeholders: `[IsProbabilityMeasure μ] (A : Set Ω) (hA : MeasurableSet A)`.

| Before | After |
|---|---|
| `⊢ G` | `hi : Integrable (A.indicator 1) μ ⊢ G` |

**R19 · `linear_combination e * h`** **closes** an equation `a = b` when `a - b - e * (l - r)` is `0` by
`ring`, for `h : l = r`. Use it inside `funext ω` to rewrite `(X ω - t * 1_A ω) ^ 2` into the expanded sum,
with `e = t * t` and `h := hsq ω : 1_A(ω) ^ 2 = 1_A(ω)`. Placeholders: `(x y t : ℝ) (h : x ^ 2 = x)`.

| Before | After |
|---|---|
| `h : x ^ 2 = x ⊢ y + t * t * x ^ 2 = y + t * t * x` | closed by `linear_combination (t * t) * h` |

**R20 · `sq_nonneg`** changes the **context**. Lemma: `sq_nonneg a : 0 ≤ a ^ 2`. Placeholders: `(a : ℝ)`.
With R13 it gives the integral fact in one term: `integral_nonneg fun ω => sq_nonneg _ : 0 ≤ ∫ ω, (… ω) ^ 2 ∂μ`.

| Before | After |
|---|---|
| `⊢ G` | `hs : 0 ≤ a ^ 2 ⊢ G` |

**R21 · `hf.const_mul c`** changes the **context**. `Integrable.const_mul : Integrable f μ → ∀ c,
Integrable (fun x => c * f x) μ`. Placeholders: `(f : Ω → ℝ) (hf : Integrable f μ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hc : Integrable (fun x => c * f x) μ ⊢ G` |

**R22 · `rw [integral_const_mul]`** changes the **goal**. Lemma: `∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ` (no
integrability needed). Placeholders: `(f : Ω → ℝ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (ω : Ω), c * f ω ∂μ)` | `⊢ P (c * ∫ (a : Ω), f a ∂μ)` |

**R23 · `rw [integral_indicator_one hA]`** changes the **goal**. Lemma: `MeasurableSet s →
∫ x, s.indicator 1 x ∂μ = μ.real s` (the expectation of an indicator is the probability). Placeholders:
`(A : Set Ω) (hA : MeasurableSet A)`.

| Before | After |
|---|---|
| `⊢ P (∫ (ω : Ω), A.indicator 1 ω ∂μ)` | `⊢ P (μ.real A)` |

**R24 · `rw [e] at h`** changes the **context**: it rewrites the hypothesis `h`, not the goal. A list
`rw [e₁, e₂, …] at h` applies them in order. In the key step: start from `h0 : 0 ≤ ∫ ω, (X ω - t * 1_A ω) ^ 2 ∂μ`
(R13, R20), rewrite it with the `funext` equation, then R15 twice, R22 twice and R23, and finish with R14.
Placeholders: `(a b : ℝ) (e : a = b)`.

| Before | After |
|---|---|
| `h : P a ⊢ P b` | `h : P b ⊢ P b` |

### The discriminant

**R25 · `discrim_le_zero`** changes the **context**. Lemma: `(∀ x, 0 ≤ a * (x * x) + b * x + c) →
discrim a b c ≤ 0`. The quadratic must be written exactly in this shape (`a * (x * x)`, not `a * x ^ 2`), so
state your key fact that way. Placeholders: `(a b c : ℝ) (hq : ∀ x, 0 ≤ a * (x * x) + b * x + c)`.

| Before | After |
|---|---|
| `⊢ G` | `hd : discrim a b c ≤ 0 ⊢ G` |

**R26 · `rw [discrim] at hd`** changes the **context**: it unfolds `discrim a b c` to `b ^ 2 - 4 * a * c`.
Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `hd : discrim a b c ≤ 0 ⊢ b ^ 2 ≤ 4 * a * c` | `hd : b ^ 2 - 4 * a * c ≤ 0 ⊢ b ^ 2 ≤ 4 * a * c` |

**R27 · `nlinarith`** **closes** goals like `linarith`, but first also multiplies pairs of hypotheses (and
squares), so it handles some nonlinear steps. After R26 in `cs_indicator` the hypothesis contains
`(-2 * I) ^ 2` and `4 * P * E` (with `I = E[X 1_A]`), the goal `I ^ 2 ≤ E * P`: `nlinarith` expands and matches.

| Before | After |
|---|---|
| `ha : 0 ≤ a, hb : 0 ≤ b ⊢ 0 ≤ a * b` | closed |

---

## Part 3 · `paley_zygmund`

Statement: `(1 - θ) ^ 2 * (μ[X]) ^ 2 ≤ μ[fun ω => X ω ^ 2] * μ.real {ω | θ * μ[X] < X ω}`. Uses both
milestones: `have h1 := split_mean μ X hmeas hX hnn θ hθ0`, then a three-line `calc` (R9).

**R28 · `pow_le_pow_left₀`** changes the **goal list**. Lemma: `0 ≤ a → a ≤ b → ∀ n, a ^ n ≤ b ^ n`. As a
term: `pow_le_pow_left₀ ha hab 2`. Placeholders: `(a b : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ a ^ n ≤ b ^ n` | `⊢ 0 ≤ a`, `⊢ a ≤ b` |

The `0 ≤ (1 - θ) * μ[X]` fact is R12 + R13 (with `1 - θ ≥ 0` by R14); `(1 - θ) * μ[X] ≤ E[X 1_A]` is R14
applied to `h1`. The last step `_ ≤ _` is `cs_indicator` at the event `A`, whose measurability is R2.

### Worked combinations (W1–W3, on statements that are not the exercise's)

**W1: Markov's inequality** `c · P(f > c) ≤ E f` for `f ≥ 0`. R2, R18, then `rw [← R23, ← R22]` turns the left
side into one integral, R10 (with R21) reduces to a pointwise bound, R7 + R8 + R14 finish:

```lean-goal
⊢ c * μ.real {ω | c < f ω} ≤ ∫ (ω : Ω), f ω ∂μ
⊢ ∫ (a : Ω), c * {ω | c < f ω}.indicator 1 a ∂μ ≤ ∫ (ω : Ω), f ω ∂μ
⊢ c * {ω | c < f ω}.indicator 1 ω ≤ f ω
```

**W2: discriminant.** `∀ t, 0 ≤ 1 * (t * t) + b * t + c` gives `b ^ 2 ≤ 4 * c` by R25, R26, R14:

```lean-goal
⊢ b ^ 2 ≤ 4 * c
```

with `hd : discrim 1 b c ≤ 0`, then `hd : b ^ 2 - 4 * 1 * c ≤ 0`.

**W3: squaring a bound in `calc`.** `4 * a ^ 2 = (2 * a) ^ 2 := by ring`, then
`_ ≤ b ^ 2 := pow_le_pow_left₀ (by linarith) hab 2` (R9, R28, R14).

---

## Traps

- **Lambda form for `integral_add`** (R15). State integrability as
  `Integrable (fun ω => X ω * A.indicator 1 ω) μ`, matching the integrand's summand literally, before
  `rw [integral_add …]`. A fact about `X * A.indicator 1` (a product of functions) is the same function but
  not the same text, and `rw` then fails with "did not find instance of the pattern".
- **Split on the condition, not on membership.** For `A = {ω | θ * μ[X] < X ω}` write
  `by_cases h : θ * μ[X] < X ω`: `simp [Set.indicator, h]` turns `ω ∈ {ω | …}` into that condition and
  then uses `h`. (For a named set `A`, as in `cs_indicator`, `by_cases h : ω ∈ A` is right.)
- `μ[fun ω => X ω ^ 2]` appears as `∫ (x : Ω), (fun ω => X ω ^ 2) x ∂μ`, but after `rw [integral_add …]` the
  same integral appears as `∫ (a : Ω), X a ^ 2 ∂μ`. They are equal by unfolding, and `linarith` matches them;
  `rw` may not (use `beta_reduce` or `show` to restate).
- R25 needs the quadratic as `a * (t * t) + b * t + c` with exactly that bracketing; write your `key` fact in
  that form, with `a = μ.real A`, `b = -2 * E[X 1_A]`, `c = μ[fun ω => X ω ^ 2]`.
- `1_A² = 1_A` is not a `simp` fact; prove `∀ ω, A.indicator (1 : Ω → ℝ) ω ^ 2 = A.indicator 1 ω` with
  R7 + R8.
- A `have` proved inside one theorem is not visible in another: each milestone redoes its integrability facts.
- `integral_mono` and friends need **both** sides integrable; a non-integrable `f` has `∫ f = 0` in Lean, so the
  lemma would be false without those hypotheses.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `Integrable X μ` from `MemLp X 2 μ` | `hX.integrable one_le_two` | R1 |
| `Integrable (fun ω => X ω ^ 2) μ` | `hX.integrable_sq` | R17 |
| event `{ω \| c < X ω}` measurable | `measurableSet_lt measurable_const hmeas` | R2 |
| `X · 1_A` integrable | `hXi.mul_bdd (c := 1) (measurable_const.indicator hA).aestronglyMeasurable (ae_of_all _ fun ω => ?_)` | R3–R6 |
| `1_A` integrable | `(integrable_const 1).indicator hA` | R18 |
| `c + f`, `c * f` integrable | `(integrable_const c).add hf`, `hf.const_mul c` | R11, R21 |
| evaluate `1_A(ω)` | `by_cases h : cond <;> simp [Set.indicator, h]` | R7, R8 |
| chain (in)equalities | `calc a ≤ b := …`, next line `_ = c := …` | R9 |
| integrate a pointwise bound | `refine integral_mono hf hg fun ω => ?_` | R10 |
| `0 ≤ ∫ f` | `integral_nonneg hnn` | R13 |
| `0 ≤ a * b` | `mul_nonneg ha hb` | R12 |
| linear arithmetic | `linarith` / `linarith [fact]` | R14 |
| `∫ (f + g)` | `rw [integral_add hf hg]` | R15 |
| `∫ c` (probability) | `simp` (or `rw [integral_const]; simp`) | R16 |
| `∫ c * f` | `rw [integral_const_mul]` | R22 |
| `∫ 1_A` | `rw [integral_indicator_one hA]` | R23 |
| rewrite a hypothesis | `rw [e₁, e₂] at h` | R24 |
| equation from `h` times a factor | `linear_combination e * h` | R19 |
| `0 ≤ a ^ 2` | `sq_nonneg a` | R20 |
| quadratic ≥ 0 ⇒ discriminant ≤ 0 | `have := discrim_le_zero key; rw [discrim] at this` | R25, R26 |
| nonlinear finish | `nlinarith` | R27 |
| `a ≤ b ⇒ a ^ 2 ≤ b ^ 2` (`0 ≤ a`) | `pow_le_pow_left₀ ha hab 2` | R28 |
| see the state | infoview | |
