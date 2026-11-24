# E097 · Variance of an affine map: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). E095 introduces the same probability setup (sample space,
σ-algebra, probability measure); the rows below repeat what you need from it. **New here:** Mathlib's
probability spaces (`MeasurableSpace`, `Measure`, `IsProbabilityMeasure`), real random variables
`X : Ω → ℝ`, Mathlib's variance `Var[X; μ]`, and the measurability notion `AEStronglyMeasurable`.

## How to read an entry

Each entry is one tactic or one lemma used with `have`/`rw`. It says what changes (**goal**, **context**,
or **goal list**), gives the lemma's statement, lists the placeholders with their types, then shows the
proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. `P Var[Y; μ]` is `P` applied to `Var[Y; μ]`: the bracket notation needs no
  parentheses.
- Placeholders are written as Lean binders. `{Ω : Type}` is any type. A bracket such as `[MeasurableSpace Ω]`
  or `[IsProbabilityMeasure μ]` is a requirement found by instance search (a *type class*); both are
  explained under *Reading the goals*.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `open MeasureTheory ProbabilityTheory` | lets you write `Measure`, `Var[…]`, `variance_add_const` without the namespace prefixes |
| `Ω : Type*`, infoview `Ω : Type u_1` | the sample space (the set of outcomes), a type in any universe. `Type*` is `Type u` for a fresh universe level `u`, which Lean prints as `u_1` |
| `[MeasurableSpace Ω]`, infoview `inst✝¹ : MeasurableSpace Ω` | `Ω` carries a σ-algebra: the family of subsets (events) that can be measured. `inst✝` is how an unnamed instance argument prints |
| `μ : Measure Ω` | a countably additive measure on `Ω`; `μ A` is the measure of an event `A`, a value in `ENNReal = [0, ∞]` (also printed `ℝ≥0∞`) |
| `[IsProbabilityMeasure μ]`, infoview `inst✝ : IsProbabilityMeasure μ` | the assumption `μ Set.univ = 1` (`Set.univ` is all of `Ω`): `μ` is a probability measure |
| `X : Ω → ℝ` | a real random variable: a function from outcomes to reals |
| `fun ω => a * X ω + b` | the random variable `aX + b`, built pointwise. `fun x => …` and `fun ω => …` are the same function: the bound name is irrelevant |
| `μ[X]` | the expectation `∫ ω, X ω ∂μ` (Bochner integral; `0` when `X` is not integrable) |
| `Var[X; μ]` | `ProbabilityTheory.variance X μ : ℝ`. It is `(eVar[X; μ]).toReal`, where `eVar[X; μ] = ∫⁻ ω, ‖X ω - μ[X]‖ₑ ^ 2 ∂μ` is the variance in `ENNReal` (`[0, ∞]`); `.toReal` sends `∞` to `0` |
| `∫⁻ ω, f ω ∂μ`, `‖r‖ₑ` | the integral of a `[0, ∞]`-valued function; `‖r‖ₑ = |r|` as an element of `[0, ∞]` |
| `Var[X; μ]` for measurable `X` | equals `∫ ω, (X ω - μ[X]) ^ 2 ∂μ` (lemma `variance_eq_integral`), so it is the usual variance when `X` is square-integrable and `0` otherwise |
| `AEStronglyMeasurable X μ` | `X` agrees `μ`-almost everywhere with a strongly measurable function (for `ℝ`-valued `X`: a limit of simple functions). The weakest measurability Mathlib asks of a random variable |
| `c ^ 2` | `c` squared; the exponent is the natural number `2` |
| `case hX` | a side goal named after the lemma argument it fills (the lemma calls its random variable `X`) |

---

## Part 1 · `variance_affine`

Statement: for a probability measure `μ` and a.e.-strongly-measurable `X`,
`Var[fun ω => a * X ω + b; μ] = a ^ 2 * Var[X; μ]`. Read the left side as `Var[Y + b]` with
`Y = fun ω => a * X ω`. Route: build `AEStronglyMeasurable Y μ` (R1), remove `+ b` with it (R2), pull `a`
out as `a ^ 2` (R3). Both sides are then the same term, and `rw` closes the goal by `rfl` itself.

### Measurability of a scaled random variable

**R1 · `AEStronglyMeasurable.const_mul`** changes the **context**. The lemma is
`AEStronglyMeasurable.const_mul : AEStronglyMeasurable f μ → ∀ c, AEStronglyMeasurable (fun x => c * f x) μ`
(for `f` with values in any topological type with a continuous `*`, such as `ℝ`). With
`hf : AEStronglyMeasurable f μ`, dot notation `hf.const_mul c` means `AEStronglyMeasurable.const_mul hf c`,
because `hf`'s type starts with `AEStronglyMeasurable`. Use it as a term: `have hg := hf.const_mul c`, or
directly as the argument of R2. Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ)
(hf : AEStronglyMeasurable f μ) (c : ℝ)`.

| Before | After |
|---|---|
| `hf : AEStronglyMeasurable f μ ⊢ G` | `hg : AEStronglyMeasurable (fun x => c * f x) μ ⊢ G` |

### Rewriting a variance

**R2 · `rw [variance_add_const hY]`** changes the **goal**. The lemma is
`variance_add_const : AEStronglyMeasurable Y μ → ∀ c, Var[fun ω => Y ω + c; μ] = Var[Y; μ]` for a probability
measure `μ` (`[IsProbabilityMeasure μ]` is found by instance search). `hY` fixes `Y`, so `rw` looks for exactly
`Var[fun ω => Y ω + ?c; μ]`; with `Y := fun x => c * f x`, `Y ω` is reduced to `c * f ω` before the search.
Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
(hY : AEStronglyMeasurable Y μ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P Var[fun ω => Y ω + c; μ]` | `⊢ P Var[Y; μ]` |

Without the argument, `rw [variance_add_const]` finds `Y` from the goal and adds the measurability as a side
goal `case hX` (W3 below).

**R3 · `rw [variance_const_mul]`** changes the **goal**. The lemma is
`variance_const_mul : ∀ (c : ℝ) (Y : Ω → ℝ) (μ : Measure Ω), Var[fun ω => c * Y ω; μ] = c ^ 2 * Var[Y; μ]`:
no measurability and no probability assumption, so no argument is needed. Placeholders:
`{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℝ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P Var[fun ω => c * Y ω; μ]` | `⊢ P (c ^ 2 * Var[Y; μ])` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: two scalings.** R3 rewrites the outer factor first (`Y := fun ω => d * Y ω`), then the inner one; `ring`
closes `(c * d) ^ 2 = c ^ 2 * d ^ 2`-style arithmetic:

```lean-goal
⊢ Var[fun ω => c * (d * Y ω); μ] = (c * d) ^ 2 * Var[Y; μ]
⊢ c ^ 2 * Var[fun ω => d * Y ω; μ] = (c * d) ^ 2 * Var[Y; μ]
⊢ c ^ 2 * (d ^ 2 * Var[Y; μ]) = (c * d) ^ 2 * Var[Y; μ]
```

**W2: two scalings and a shift.** R1 twice gives `h1 := (hY.const_mul d).const_mul c`, then R2 with `h1`,
R3 twice, `ring`:

| Before | After |
|---|---|
| `hY : AEStronglyMeasurable Y μ ⊢ Var[fun ω => c * (d * Y ω) + e; μ] = (c * d) ^ 2 * Var[Y; μ]` | `h1 : AEStronglyMeasurable (fun x => c * (d * Y x)) μ ⊢ Var[fun ω => c * (d * Y ω) + e; μ] = (c * d) ^ 2 * Var[Y; μ]` |
| `h1 : AEStronglyMeasurable (fun x => c * (d * Y x)) μ ⊢ Var[fun ω => c * (d * Y ω) + e; μ] = (c * d) ^ 2 * Var[Y; μ]` | `⊢ Var[fun x => c * (d * Y x); μ] = (c * d) ^ 2 * Var[Y; μ]` |

**W3: R2 with no argument** leaves the measurability as a second goal, proved last:

```lean-goal
⊢ Var[fun ω => Y ω + c; μ] + Var[fun ω => d * Y ω; μ] = (1 + d ^ 2) * Var[Y; μ]
⊢ Var[Y; μ] + Var[fun ω => d * Y ω; μ] = (1 + d ^ 2) * Var[Y; μ]
⊢ AEStronglyMeasurable Y μ
⊢ Var[Y; μ] + d ^ 2 * Var[Y; μ] = (1 + d ^ 2) * Var[Y; μ]
```

---

## Traps

- Order matters. `a * X ω + b` is `(a * X ω) + b`, so the outermost operation is `+ b`. `rw [variance_const_mul]`
  first fails: it looks for `Var[fun ω => ?c * ?Y ω; μ]` and the goal has `Var[fun ω => a * X ω + b; μ]`.
- `variance_add_const hX` (with the hypothesis about `X`, not about `a * X`) fixes `Y := X`, so `rw` looks for
  `Var[fun ω => X ω + ?c; μ]` and fails. Pass the measurability of `fun ω => a * X ω` (R1).
- `variance_add_const` needs `[IsProbabilityMeasure μ]` (the constant must integrate to itself);
  `variance_const_mul` needs nothing.
- `Var[X; μ]` is a real number even when the variance is infinite (then it is `0`); the two lemmas hold
  regardless, so no integrability hypothesis is needed here.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `AEStronglyMeasurable (fun x => c * f x) μ` from `hf` | `hf.const_mul c` | R1 |
| `Var[fun ω => Y ω + c; μ] → Var[Y; μ]` | `rw [variance_add_const hY]` | R2 |
| same, measurability as a side goal | `rw [variance_add_const]`, then prove `case hX` | R2, W3 |
| `Var[fun ω => c * Y ω; μ] → c ^ 2 * Var[Y; μ]` | `rw [variance_const_mul]` | R3 |
| several rewrites in one step | `rw [l₁, l₂]` (closes the goal by `rfl` when both sides agree) | TACTIC_STATES |
| real arithmetic left over | `ring` | W1 |
| see the state | infoview | |
