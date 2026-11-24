# E096 · Expectation is linear: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). E095 introduced probability measures; everything needed
from it is repeated below. **New here:** Mathlib's (Bochner) integral `∫ x, f x ∂μ`, the expectation
notation `μ[f]`, integrability `Integrable f μ`, and the four rewrites that evaluate the integral of a
constant.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`apply`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), gives the lemma's statement, lists the placeholders with their types, then
shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{Ω : Type}` is any type. A bracket such as `[MeasurableSpace Ω]`
  is a requirement on `Ω` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `open MeasureTheory ProbabilityTheory` | lets you write `Measure`, `Integrable`, `integral_add`, … without the `MeasureTheory.` prefix, and turns on the notation `μ[f]` |
| `Ω : Type*`, `Ω : Type u_1` | the sample space, a type in any universe |
| `[MeasurableSpace Ω]`, `inst✝¹ : MeasurableSpace Ω` | `Ω` carries a σ-algebra (the measurable sets). `inst✝` is how an unnamed instance prints |
| `μ : Measure Ω` | a (countably additive) measure on `Ω` |
| `[IsProbabilityMeasure μ]` | the assumption `μ Set.univ = 1` (`Set.univ` is the whole of `Ω`) |
| `X : Ω → ℝ` | a real random variable: just a function on the sample space |
| `∫ (x : Ω), f x ∂μ` | the integral of `f` against `μ`: for a probability measure, the expectation $\mathbb E[f]$. It is defined for every `f`, and is `0` when `f` is not integrable (a *junk value*) |
| `μ[f]` | notation for `∫ x, f x ∂μ`. Lean does not print it back: in the infoview `μ[X]` shows as `∫ (x : Ω), X x ∂μ` |
| `∫ (x : Ω), (fun ω => a * X ω + b) x ∂μ` | `μ[fun ω => a * X ω + b]` unfolded. `(fun ω => …) x` is the function applied to `x` (not yet β-reduced); `rw` with R3 or R5 sees through it |
| `∫ (a_1 : Ω), a * X a_1 ∂μ` | the same integral with the bound variable renamed: `a` is taken by your `a : ℝ`, so Lean picks `a_1` |
| `Integrable f μ` | `f` is (almost everywhere strongly) measurable and $\int \lvert f\rvert\,d\mu < \infty$. For `f : Ω → ℝ`, "a.e. strongly measurable" just means: equal to a measurable function outside a `μ`-null set |
| `fun _ => c`, `∫ (_x : Ω), c ∂μ` | a binder named `_` or `_x` is not used in the body: the constant function `c` and its integral |
| `μ.real Set.univ` | the total mass of `μ` as a real number, `(μ Set.univ).toReal`; `1` for a probability measure |
| `r • c` | scalar multiplication; for `r c : ℝ` it is `r * c` (R7) |

---

## Part 1 · `expectation_affine`

Statement: for a probability measure `μ`, an integrable `X : Ω → ℝ` and constants `a b : ℝ`,
$\mathbb E[aX + b] = a\,\mathbb E[X] + b$, i.e. `μ[fun ω => a * X ω + b] = a * μ[X] + b`. Route: produce the two
integrability proofs (R1, R2), split the integral of the sum with them (R3), pull out `a` (R4), and evaluate
the integral of the constant `b` (R5 → R6 → R7 → R8, or `simp`, R9).

### Integrability side conditions

**R1 · `Integrable.const_mul`** changes the **goal**. The lemma is
`Integrable.const_mul : Integrable f μ → ∀ c, Integrable (fun x => c * f x) μ`. `apply Integrable.const_mul`
reduces the goal to `Integrable f μ`. As a term, dot notation `hf.const_mul c` means
`Integrable.const_mul hf c` (because `hf : Integrable f μ`), a proof of `Integrable (fun x => c * f x) μ`.
Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : Integrable f μ) (c : ℝ)`.
The lemma works for any normed ring in place of `ℝ` (`ℂ` too).

| Before | After |
|---|---|
| `⊢ Integrable (fun x => c * f x) μ` | `⊢ Integrable f μ` |

**R2 · `integrable_const`** **closes** `Integrable (fun _ => c) μ`. The lemma is
`integrable_const (c : β) : Integrable (fun _ => c) μ`, which needs `[IsFiniteMeasure μ]` (`μ Set.univ < ∞`);
Lean derives that from `[IsProbabilityMeasure μ]`. As a term: `integrable_const c`. Placeholders:
`{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ Integrable (fun x => c) μ` | no goals |

### Rewriting integrals

**R3 · `rw [integral_add hf hg]`** changes the **goal**: the integral of a sum becomes the sum of the integrals.
The lemma is `integral_add : Integrable f μ → Integrable g μ → ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ`;
`f` and `g` are implicit and read off the two proofs you pass. Placeholders:
`{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)`.
In the exercise, `f` is `fun ω => a * X ω` (proof from R1) and `g` is `fun ω => b` (proof from R2).

| Before | After |
|---|---|
| `⊢ P (∫ (x : Ω), f x + g x ∂μ)` | `⊢ P (∫ (a : Ω), f a ∂μ + ∫ (a : Ω), g a ∂μ)` |

**R4 · `rw [integral_const_mul]`** changes the **goal**: a constant factor comes out of the integral. The lemma
is `integral_const_mul (r : L) (f : α → L) : ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ` for `L` = `ℝ` or `ℂ`
(`[RCLike L]`). No integrability hypothesis: if `f` is not integrable, both sides are the junk value `0`.
Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (r : ℝ) (f : Ω → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : Ω), r * f x ∂μ)` | `⊢ P (r * ∫ (a : Ω), f a ∂μ)` |

### The integral of a constant

`simp` applies R5–R8 by itself (R9). They are listed one by one so you can read what it does.

**R5 · `rw [integral_const]`** changes the **goal**. The lemma is
`integral_const (c : E) : ∫ x, c ∂μ = μ.real Set.univ • c`, for any measure: (total mass) times the constant.
Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (_x : Ω), c ∂μ)` | `⊢ P (μ.real Set.univ • c)` |

**R6 · `rw [probReal_univ]`** changes the **goal**. The lemma is `probReal_univ : μ.real Set.univ = 1`, for a
probability measure. Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]`.

| Before | After |
|---|---|
| `⊢ P (μ.real Set.univ)` | `⊢ P 1` |

**R7 · `rw [smul_eq_mul]`** changes the **goal**. The lemma is `smul_eq_mul : a • a' = a * a'` when the scalar
and the vector are in the same type with `*` (here `ℝ`). Placeholders: `(r c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (r • c)` | `⊢ P (r * c)` |

**R8 · `rw [one_mul]`** changes the **goal**. The lemma is `one_mul : 1 * a = a`. Placeholders:
`{α : Type} [MulOneClass α] (c : α)` (α has `*` and a unit `1`; `ℕ`, `ℤ`, `ℝ`, `ℂ` qualify).

| Before | After |
|---|---|
| `⊢ P (1 * c)` | `⊢ P c` |

**R9 · `simp`** **closes** a goal that R5–R8 reduce to `t = t`. `simp?` reports exactly
`simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]`. Placeholders:
`{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (c u : ℝ)`.

| Before | After |
|---|---|
| `⊢ u + ∫ (_x : Ω), c ∂μ = u + c` | no goals |

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: two random variables.** `μ[fun ω => f ω + 2 * g ω] = μ[f] + 2 * μ[g]` for integrable `f g`. R3 with
`hf` and the R1 term `hg.const_mul 2`, then R4 (which also closes the goal, since both sides then agree):

```lean-goal
⊢ ∫ (x : Ω), (fun ω => f ω + 2 * g ω) x ∂μ = ∫ (x : Ω), f x ∂μ + 2 * ∫ (x : Ω), g x ∂μ
⊢ ∫ (a : Ω), f a ∂μ + ∫ (a : Ω), 2 * g a ∂μ = ∫ (x : Ω), f x ∂μ + 2 * ∫ (x : Ω), g x ∂μ
```

**W2: the expectation of a constant**, `μ[fun _ => (3 : ℝ)] = 3`, by R5, R6, R7, R8:

```lean-goal
⊢ ∫ (x : Ω), (fun x => 3) x ∂μ = 3
⊢ μ.real Set.univ • 3 = 3
⊢ 1 • 3 = 3
⊢ 1 * 3 = 3
```

---

## Traps

- `integral_add` needs both integrability proofs. It is false without them: a non-integrable function has
  integral `0` by convention, so `∫ (f + g)` and `∫ f + ∫ g` can differ.
- The second summand is the *function* `fun ω => b`, so its proof is `integrable_const b`, which needs a finite
  measure. A probability measure is one; Lean finds that by itself.
- `integral_const` gives `μ.real Set.univ • b`, not `b`. Only for a probability measure does R6 make it `1 • b`.
- `rw [integral_const_mul]` must come after `rw [integral_add …]`: before the split, there is no
  `∫ x, r * f x ∂μ` in the goal, only the integral of the whole sum.
- Do not skip R4 and hope `simp` pulls `a` out: `integral_const_mul` is not a `simp` lemma. `simp` straight after
  R3 evaluates the constant integral but stops at `∫ (a_1 : Ω), a * X a_1 ∂μ = a * ∫ (x : Ω), X x ∂μ`.
- The infoview never shows `μ[…]`: look for `∫ (x : Ω), … ∂μ`. Renamed binders (`a_1`, `a`, `x`) do not matter;
  `rw` and `simp` compare integrals up to the bound variable's name.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `Integrable (fun x => c * f x) μ` from `hf : Integrable f μ` | `hf.const_mul c` | R1 |
| `Integrable (fun _ => c) μ` (finite measure) | `integrable_const c` | R2 |
| $\int (f + g) = \int f + \int g$ | `rw [integral_add hf hg]` | R3 |
| $\int r f = r \int f$ | `rw [integral_const_mul]` | R4 |
| $\int c\,d\mu = \mu(\Omega)\cdot c$ | `rw [integral_const]` | R5 |
| `μ.real Set.univ → 1` (probability measure) | `rw [probReal_univ]` | R6 |
| `r • c → r * c` in `ℝ` | `rw [smul_eq_mul]` | R7 |
| `1 * c → c` | `rw [one_mul]` | R8 |
| R5–R8 in one go | `simp` | R9 |
| see the state | infoview | |
