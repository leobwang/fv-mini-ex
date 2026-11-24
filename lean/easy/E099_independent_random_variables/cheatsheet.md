# E099 · Independent random variables: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033); a probability measure `μ` on a sample space `Ω` (E095);
the expectation `μ[X]` as an integral (E096). **New here:** independence of random variables
(`IndepFun`, notation `X ⟂ᵢ[μ] Y`), the product rule `E[XY] = E[X] E[Y]`, and the measurability side
condition `AEStronglyMeasurable` it needs.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`apply`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), gives the lemma's statement, lists the placeholders with their types, then
shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{Ω : Type}` is any type. A bracket such as `[MeasurableSpace Ω]`
  is a requirement on `Ω` (a *type class*).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `open MeasureTheory ProbabilityTheory` | lets you write `Measure`, `IndepFun`, … without the `MeasureTheory.` / `ProbabilityTheory.` prefix |
| `{Ω : Type*}`, `Ω : Type u_1` | `Ω` is a type in any universe; `Type*` in the statement prints as `Type u_1` (a universe variable). Treat it as `Type` |
| `[MeasurableSpace Ω]`, `inst✝¹ : MeasurableSpace Ω` | `Ω` carries a σ-algebra (the measurable sets); `inst✝`, `inst✝¹` are how unnamed instance arguments print (numbered when there are several) |
| `μ : Measure Ω`, `[IsProbabilityMeasure μ]` | a measure on `Ω` with `μ Set.univ = 1` |
| `X Y : Ω → ℝ` | real random variables: plain functions on the sample space |
| `Measurable X` | preimages of measurable sets of `ℝ` (Borel sets) under `X` are measurable in `Ω` |
| `AEStronglyMeasurable X μ` | `X` agrees `μ`-almost everywhere with a limit of simple (finitely-valued measurable) functions; the measurability notion integrals use. For `ℝ`-valued `X` it follows from `Measurable X` (R1) |
| `X ⟂ᵢ[μ] Y` | `IndepFun X Y μ`: `μ(X ∈ A ∧ Y ∈ B) = μ(X ∈ A) · μ(Y ∈ B)` for all measurable `A, B ⊆ ℝ`. Without `[μ]` the measure defaults to `volume`. Type `⟂` as `\perp`, `ᵢ` as `\_i` |
| `μ[X]` | the expectation `E[X]`, notation for the integral `∫ x, X x ∂μ` (Bochner integral of `X` against `μ`; it is `0` when `X` is not integrable). The hypotheses `h1`, `h2` print as `h1 : ∫ (x : Ω), X x ∂μ = 2` |
| `∫ (x : Ω), X x ∂μ` | how the infoview prints `μ[X]` |
| `X * Y` | the pointwise product `fun ω => X ω * Y ω` (multiplication of functions, `Pi.instMul`) |
| `(X * Y) x` | that product evaluated at `x`, i.e. `X x * Y x`; `μ[X * Y]` prints as `∫ (x : Ω), (X * Y) x ∂μ` |
| `(∫ (x : Ω), X x ∂μ) * ∫ (x : Ω), Y x ∂μ` | `μ[X] * μ[Y]`; the right integral needs no parentheses because `∫` extends to the end |

---

## Part 1 · `indep_mul`

Statement: for measurable, independent `X, Y : Ω → ℝ` under a probability measure `μ` with `μ[X] = 2` and
`μ[Y] = 3`, `μ[X * Y] = 6`. Route: factor the mean of the product (R2), whose two measurability arguments
come from `hX`, `hY` (R1); substitute the two means (R3); finish `2 * 3 = 6` (R4).

**R1 · `Measurable.aestronglyMeasurable`** changes the **goal**. The lemma is
`Measurable.aestronglyMeasurable : Measurable f → AEStronglyMeasurable f μ`, valid for `f : Ω → β` with `β` a
second-countable metrizable space with its Borel σ-algebra (`ℝ` and `ℂ` qualify; Lean finds these instances).
`μ` is implicit, read off the goal. `apply` reduces the goal to `Measurable f`; as a term, dot notation
`hf.aestronglyMeasurable` (for `hf : Measurable f`) means `Measurable.aestronglyMeasurable hf`.
Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : Measurable f)`.

| Before | After `apply Measurable.aestronglyMeasurable` |
|---|---|
| `⊢ AEStronglyMeasurable f μ` | `⊢ Measurable f` |

**R2 · `IndepFun.integral_mul_eq_mul_integral`** changes the **goal**. The lemma is
`IndepFun.integral_mul_eq_mul_integral : X ⟂ᵢ[μ] Y → AEStronglyMeasurable X μ → AEStronglyMeasurable Y μ →
μ[X * Y] = μ[X] * μ[Y]`, for `X Y : Ω → 𝕜` with `𝕜` = `ℝ` or `ℂ` (class `RCLike 𝕜`). No probability or
integrability assumption: if `X` or `Y` is not integrable both sides are 0 by Lean's convention.
Dot notation `hXY.integral_mul_eq_mul_integral hX hY` (for `hXY : X ⟂ᵢ[μ] Y`) is a proof of the equation,
used with `rw`. Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → ℝ)
(hXY : X ⟂ᵢ[μ] Y) (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : Ω), (X * Y) x ∂μ)` | `⊢ P ((∫ (x : Ω), X x ∂μ) * ∫ (x : Ω), Y x ∂μ)` |

**R3 · `rw [hX]`** with `hX : μ[X] = a` changes the **goal**: the mean is replaced by its value. `μ[X]` in the
hypothesis and `∫ (x : Ω), X x ∂μ` in the goal are the same term (notation only), so `rw` matches.
Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (a : ℝ) (hX : μ[X] = a)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : Ω), X x ∂μ)` | `⊢ P a` |

**R4 · `norm_num`** **closes** an equation between real numerals such as `(4 : ℝ) * 5 = 20`.

**W1** in `guide.lean`: zero covariance, `μ[U * V] - μ[U] * μ[V] = 0`, by R2 (with R1 inside the arguments),
then `ring` (the two products are the same unknown):

```lean-goal
⊢ ∫ (x : Ω), (U * V) x ∂μ - (∫ (x : Ω), U x ∂μ) * ∫ (x : Ω), V x ∂μ = 0
⊢ (∫ (x : Ω), U x ∂μ) * ∫ (x : Ω), V x ∂μ - (∫ (x : Ω), U x ∂μ) * ∫ (x : Ω), V x ∂μ = 0
```

**W2** in `guide.lean`: a mean-zero factor, `h0 : μ[U] = 0 → μ[U * V] = 0`, chains R2 → R3 → R4:

```lean-goal
⊢ ∫ (x : Ω), (U * V) x ∂μ = 0
⊢ (∫ (x : Ω), U x ∂μ) * ∫ (x : Ω), V x ∂μ = 0
⊢ 0 * ∫ (x : Ω), V x ∂μ = 0
```

---

## Traps

- R2 wants `AEStronglyMeasurable`, not `Measurable`: passing `hX` directly is a type error. Convert with
  `hX.aestronglyMeasurable` (R1).
- `X * Y` is the product of functions; `μ[X * Y]` is not `μ[X] * μ[Y]` by definition. Only independence
  (R2) makes them equal.
- Rewrite with R2 *before* `h1`, `h2`: in the original goal `μ[X]` does not occur on its own (it is hidden
  inside `μ[X * Y]`), so `rw [h1]` fails there.
- `have hX' := hX.aestronglyMeasurable` fails with "don't know how to synthesize implicit argument `μ`":
  nothing fixes the measure. Pass it inline inside R2's arguments, or state the type:
  `have hX' : AEStronglyMeasurable X μ := hX.aestronglyMeasurable`.
- `X ⟂ᵢ Y` without `[μ]` means independence under `volume`, not under your `μ`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `AEStronglyMeasurable f μ` from `hf : Measurable f` | `hf.aestronglyMeasurable` | R1 |
| `μ[X * Y] → μ[X] * μ[Y]` for `hXY : X ⟂ᵢ[μ] Y` | `rw [hXY.integral_mul_eq_mul_integral hX' hY']` | R2 |
| substitute a known mean `hX : μ[X] = a` | `rw [hX]` | R3 |
| numeric goal in `ℝ` | `norm_num` | R4 |
| identity in unknown means | `ring` | W1 |
| see the state | infoview | |
