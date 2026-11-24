# E103 · Conditional expectation: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's measure theory as far as this
problem meets it: σ-algebras as values of type `MeasurableSpace Ω`, the order `m ≤ mΩ` between them,
measures and probability measures, the Bochner integral `∫ x, f x ∂μ`, integrability, (strong)
measurability with respect to a chosen σ-algebra, and the conditional expectation `μ[f | m]`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`apply`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop` or `P : Prop`). The step changes only the part inside
  `P (…)`, wherever it sits in a larger goal.
- Placeholders are written as Lean binders: `{Ω : Type}` is the sample space, `{m mΩ : MeasurableSpace Ω}`
  two σ-algebras on it, `(hm : m ≤ mΩ)`, `(μ : Measure Ω)`, `(f : Ω → ℝ)` a real random variable.
- The lemmas hold for `f : Ω → E` with `E` any real Banach space; this sheet states them for `ℝ`.
- A state that contains `μ[f | m]` is shown in a `lean-goal` block instead of a table: a `|` would split
  the table cell.
- Every `⊢` cell and goal line is a state Lean reaches in the companion file; `tools/guide_sync.py`
  checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Ω : Type u_1` | the sample space. The spec writes `{Ω : Type*}`: any type, in any universe level `u_1` (a size level of types; ignore it) |
| `MeasurableSpace Ω` | a σ-algebra on `Ω` (the family of measurable sets). It is a type-class argument, so several can be in scope |
| `{m mΩ : MeasurableSpace Ω}` | two σ-algebras. The one declared **last** (`mΩ`) is the default: `Measure Ω`, `Integrable`, `Measurable f` use it unless told otherwise |
| `m ≤ mΩ` | every `m`-measurable set is `mΩ`-measurable: `m` is a sub-σ-algebra, i.e. coarser information |
| `Measure Ω` | a measure on `(Ω, mΩ)` |
| `IsProbabilityMeasure μ` | `μ Set.univ = 1` (an instance argument `[…]`) |
| `∫ (x : Ω), f x ∂μ` | the integral of `f` against `μ` (Bochner integral); for a probability measure, `E[f]`. You type `∫ x, f x ∂μ` (`\int`, `\partial`) |
| `Integrable f μ` | `f` is measurable (up to null sets) and `∫ ‖f‖ ∂μ < ∞`. Mathlib sets the integral of a non-integrable `f` to `0` (a junk value, E069) |
| `Measurable[m] f` | preimages of measurable sets of `ℝ` under `f` are in `m`: `f` is determined by the information `m` |
| `StronglyMeasurable[m] f` | `f` is a pointwise limit of `m`-measurable simple functions; for `f : Ω → ℝ` it is equivalent to `Measurable[m] f` (R3) |
| `Measurable f`, `StronglyMeasurable f` | **the infoview drops the `[m]`**: hover the hypothesis to see which σ-algebra it uses |
| `μ[f \| m] : Ω → ℝ` | `MeasureTheory.condExp m μ f`, the conditional expectation `E[f \| m]`, itself a function of `ω` |
| `μ[f \| m] x` | its value at `x`; you write `(μ[f \| m]) x` |
| `μ.trim hm` | `μ` restricted to the sets of the coarser σ-algebra `m` |
| `SigmaFinite ν` | `Ω` is a countable union of sets of finite `ν`-measure |
| `inst✝ : …` | an instance argument `[…]` with no name, available to every lemma that needs it |
| `case hf`, `case hfi` | the hypotheses of R4 left as goals by `apply` |

`μ[f | m]` is defined as `0` when `f` is not integrable, `m ≤ mΩ` fails, or `μ.trim hm` is not
σ-finite. Otherwise it is the (almost everywhere unique) `m`-measurable function whose integral over every
`m`-measurable set equals that of `f`. (Not E100's `μ[B | A]`, which is `cond`: there the thing after `|`
is a set `A`; here it is a σ-algebra `m`.)

---

## Part 1 · `integral_condExp_eq`

Statement: for a probability measure `μ` and any `X : Ω → ℝ`, `∫ ω, μ[X | m] ω ∂μ = ∫ ω, X ω ∂μ`: averaging
the conditional expectation gives the expectation (law of total expectation). One library lemma (R2) at
`hm`; its instance argument comes from R1.

**R1 · `infer_instance`** **closes** `SigmaFinite (μ.trim hm)`. R2 and R4 take this as an instance argument
`[SigmaFinite (μ.trim hm)]`: you never pass it. Lean derives it from `[IsProbabilityMeasure μ]` (or
`[IsFiniteMeasure μ]`, W1): the trimmed measure is finite, hence σ-finite. Placeholders: as above.

| Before | After |
|---|---|
| `inst✝ : IsProbabilityMeasure μ ⊢ SigmaFinite (μ.trim hm)` | ∅ (no goal) |

**R2 · `rw [MeasureTheory.integral_condExp hm]`** changes the **goal**. The lemma is
`integral_condExp (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)] : ∫ x, (μ[f | m]) x ∂μ = ∫ x, f x ∂μ` (`m₀` is
Mathlib's name for the ambient σ-algebra, here `mΩ`). `f` is implicit, found by matching. It holds for
**every** `f`, integrable or not (if not, both sides are `0`). With `open MeasureTheory` the prefix can be
dropped. When the goal *is* the lemma's statement, `exact integral_condExp hm` closes it.
Placeholders: `(hm : m ≤ mΩ) (μ : Measure Ω) [SigmaFinite (μ.trim hm)] (f : Ω → ℝ)`.

Before, then after:

```lean-goal
⊢ P (∫ (x : Ω), μ[f | m] x ∂μ)
⊢ P (∫ (x : Ω), f x ∂μ)
```

---

## Part 2 · `condExp_of_measurable`

Statement: if `X` is `m`-measurable (`hXm : Measurable[m] X`) and integrable (`hX : Integrable X μ`), then
`μ[X | m] = X`: conditioning on information that already determines `X` returns `X`. The lemma (R4) wants
*strong* measurability, so convert `hXm` first (R3).

**R3 · `Measurable.stronglyMeasurable`** changes the **context** (used with `have`). The lemma is
`Measurable f → StronglyMeasurable f` for `f : Ω → ℝ` (more generally, into a second-countable metrizable
space). It works for any σ-algebra on `Ω`: from `hf : Measurable[m] f` the dot-notation term
`hf.stronglyMeasurable` has type `StronglyMeasurable[m] f`, the `m` carried along. Placeholders:
`{m : MeasurableSpace Ω} (f : Ω → ℝ) (hf : Measurable[m] f)`. Note the printing: both show without `[m]`.

| Before | After |
|---|---|
| `hf : Measurable f ⊢ P` | `hs : StronglyMeasurable f ⊢ P` |

**R4 · `apply MeasureTheory.condExp_of_stronglyMeasurable hm`** changes the **goal list**. The lemma is
`condExp_of_stronglyMeasurable (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)] {f} (hf : StronglyMeasurable[m] f)
(hfi : Integrable f μ) : μ[f | m] = f`. `apply` matches the conclusion against the goal and leaves `hf` and
`hfi` as goals `case hf` and `case hfi`. As a term with all arguments,
`condExp_of_stronglyMeasurable hm hs hi` proves `μ[f | m] = f` directly (usable with `exact` or `rw`).
Placeholders: `(hm : m ≤ mΩ) (μ : Measure Ω) [SigmaFinite (μ.trim hm)] (f : Ω → ℝ)
(hs : StronglyMeasurable[m] f) (hi : Integrable f μ)`.

Before:

```lean-goal
⊢ μ[f | m] = f
```

| After (`case hf`) | After (`case hfi`) |
|---|---|
| `⊢ StronglyMeasurable f` | `⊢ Integrable f μ` |

The first goal is about the σ-algebra `m` even though it prints as `StronglyMeasurable f`: close it with a
term built by R3 from an `m`-measurability hypothesis. A hypothesis about `mΩ` would not fit.

---

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: R2 inside a larger goal, finite measure.** With `[IsFiniteMeasure μ]` instead of a probability measure,
R1 still finds the instance. `rw [integral_condExp hm]` rewrites the first integral and then closes the goal
by `rfl`:

```lean-goal
⊢ ∫ (x : Ω), μ[f | m] x ∂μ - ∫ (x : Ω), g x ∂μ = ∫ (x : Ω), f x ∂μ - ∫ (x : Ω), g x ∂μ
```

**W2: a constant is known to every σ-algebra.** `μ[fun _ => c | m] = fun _ => c`. R4 splits it; `case hf`
is R3 applied to `measurable_const : Measurable fun _ => c` (it elaborates at `m`); `case hfi` is
`integrable_const c` (a constant is integrable for a finite measure):

```lean-goal
⊢ μ[fun x => c | m] = fun x => c
⊢ StronglyMeasurable fun x => c
⊢ Integrable (fun x => c) μ
```

---

## Traps

- If `X` is not integrable, Mathlib sets `μ[X | m] = 0` (`condExp_of_not_integrable`). Part 1 still holds
  (both integrals are `0`), which is why R2 needs no integrability argument; Part 2 needs `hX`.
- `Measurable[m] X` prints as `Measurable X`. Do not conclude it is about the default σ-algebra `mΩ`; hover
  it, or use `set_option pp.explicit true`.
- R4 needs `StronglyMeasurable[m] f`, not `Measurable[m] f`: passing `hXm` directly is a type error.
  Convert with R3 (`hXm.stronglyMeasurable`).
- Both lemmas take `hm` **explicitly** as their first argument; the instance `[SigmaFinite (μ.trim hm)]`
  comes after it and is never written.
- Names: with `open MeasureTheory` (inside the spec), write `integral_condExp`; elsewhere
  `MeasureTheory.integral_condExp`. `ProbabilityTheory` is opened too but these lemmas are not in it.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `SigmaFinite (μ.trim hm)` | nothing (found automatically); `infer_instance` to check | R1 |
| `∫ μ[f \| m] ∂μ` → `∫ f ∂μ` | `rw [integral_condExp hm]` / `exact integral_condExp hm` | R2 |
| `Measurable[m] f` → `StronglyMeasurable[m] f` | `hf.stronglyMeasurable` | R3 |
| `μ[f \| m] = f` → its two hypotheses | `apply condExp_of_stronglyMeasurable hm` | R4 |
| `μ[f \| m] = f` in one term | `condExp_of_stronglyMeasurable hm hs hi` | R4 |
| non-integrable `f` | `condExp_of_not_integrable : ¬Integrable f μ → μ[f \| m] = 0` | Traps |
| see which σ-algebra | hover, or `set_option pp.explicit true` | |
