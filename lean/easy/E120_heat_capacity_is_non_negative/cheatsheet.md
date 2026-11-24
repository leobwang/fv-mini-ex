# E120 · Heat capacity is non-negative: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `rw`, `have`, `apply`, `exact`, `intro`, instance
arguments `[…]`. **New here:** physlib's `CanonicalEnsemble` with `heatCapacity`, `energyVariance` and
its fluctuation-dissipation theorem; `Temperature` and the Boltzmann constant `kB`; Mathlib's
non-negative reals `ℝ≥0` (`NNReal`) and their cast to `ℝ`, the Lebesgue integral `∫ x, f x ∂μ`, the
pointwise order on functions, and the tactic `positivity`.

The physics: a canonical ensemble is a system with microstates `i` of energy `E_i` in contact with a heat
bath at temperature `T`. The state `i` has Boltzmann probability `p_i ∝ e^{-E_i/(k_B T)}`; the mean
energy is `U(T) = ⟨E⟩ = ∑_i p_i E_i`, and the heat capacity is `C(T) = dU/dT`. The
fluctuation-dissipation theorem says `C = Var(E) / (k_B T²)` with `Var(E) = ⟨(E - U)²⟩ ≥ 0`. So `C ≥ 0`
is a sign argument, once the derivative is replaced by that quotient: a non-negative numerator (an
integral of a square) over a non-negative denominator (`k_B > 0` times a square).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`apply`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as
  `[MeasurableSpace α]` is a requirement on `α` (a *type class*), filled in by Lean from the context.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `CanonicalEnsemble ι` | physlib structure: a system whose microstates are the elements of `ι`, with a field `energy : ι → ℝ` and a reference measure `μ` on `ι` |
| `[Fintype ι]`, `[Nonempty ι]` | `ι` is finite, and has at least one element |
| `[MeasurableSpace ι]`, `[MeasurableSingletonClass ι]` | a σ-algebra on `ι` (the family of subsets that have a measure; needed to integrate over `ι`), in which every singleton `{i}` is measurable |
| `inst✝⁴ : Fintype ι`, …, `inst✝ : 𝓒.IsFinite` | the unnamed `[…]` arguments of the theorem, shown as hypotheses with inaccessible names `inst✝ⁿ`; Lean uses them by itself, you never write them |
| `[𝓒.IsFinite]` | physlib class: `𝓒`'s measure is the counting measure (and `dof = 0`, `phaseSpaceunit = 1`), so integrals over `ι` are finite sums |
| `Temperature`, `T.val` | physlib structure wrapping one field `val : ℝ≥0`, the absolute temperature |
| `ℝ≥0`, `NNReal` | Mathlib's non-negative reals `{x : ℝ // 0 ≤ x}` (two names for one type) |
| `↑T.val`, `↑t` | that `ℝ≥0` value cast into `ℝ`; the statement writes `(T.val : ℝ)`. Every such cast is `≥ 0` |
| `0 < T.val` | strict positivity in `ℝ≥0` |
| `kB` | `Constants.kB : ℝ`, the Boltzmann constant `k_B`, defined as `1.380649e-23` (J/K) through a subtype, so tactics cannot see that it is positive; `Constants.kB_pos : 0 < kB` says it (R2) |
| `𝓒.heatCapacity T` | `C(T)`, defined as `derivWithin 𝓒.meanEnergyT (Set.Ioi 0) ↑T.val`. Here `𝓒.meanEnergyT t` is `U` at the real temperature `t`, `Set.Ioi 0` is the open interval `(0, ∞)`, and `derivWithin f s x` is the derivative of `f` at `x` computed using only points of `s`. You never unfold it: R1 replaces it |
| `𝓒.meanEnergy T` | `U(T) = ∫ i, 𝓒.energy i ∂𝓒.μProd T`, the mean energy |
| `𝓒.μProd T` | the Boltzmann probability measure on `ι` at temperature `T` (`p_i` above) |
| `𝓒.energyVariance T` | `Var(E) = ∫ i, (𝓒.energy i - 𝓒.meanEnergy T) ^ 2 ∂𝓒.μProd T` (R4) |
| `∫ (x : α), f x ∂μ` | `MeasureTheory.integral μ f`, the (Bochner) integral of `f : α → ℝ` against the measure `μ`; Mathlib sets it to `0` when `f` is not integrable |
| `MeasureTheory.Measure α` | the type of measures on `α` |
| `0 ≤ f` (`f` a function) | pointwise: `∀ x, 0 x ≤ f x` (R6) |
| `0 ≤ fun x => (𝓒.energy x - 𝓒.meanEnergy T) ^ 2` | the goal R5 leaves in the exercise: `f` is the integrand written as a `fun` |
| `(fun x => e) x` | a `fun` applied to `x`; it is `e` by definition (β-reduction), and `exact` sees that |
| `0 x` | the zero function applied to `x`; equal to `0` by definition |
| `case ha`, `case hb` | the two goals `apply div_nonneg` leaves, named after its hypotheses `ha`, `hb` |

---

## Part 1 · `heatCapacity_nonneg`

Statement: for a finite canonical ensemble `𝓒` (with `ι` finite, non-empty, singletons measurable) and a
temperature `T` with `hT : 0 < T.val`, `0 ≤ 𝓒.heatCapacity T`, i.e. `C(T) ≥ 0`.

### From the heat capacity to a quotient

**R1 · `rw [fluctuation_dissipation_theorem_finite 𝓒 T hT]`** changes the **goal**. The lemma
(`CanonicalEnsemble.fluctuation_dissipation_theorem_finite`, short name via `open CanonicalEnsemble`) is

`[MeasurableSingletonClass ι] [𝓒.IsFinite] (T : Temperature) (hT_pos : 0 < T.val) :`
`𝓒.heatCapacity T = 𝓒.energyVariance T / (kB * (T.val : ℝ) ^ 2)`.

You give the explicit arguments `𝓒`, `T`, `hT`; the instance arguments in `[…]` (and `[Fintype ι]`,
`[Nonempty ι]`) are found in the context. Placeholders:
`{ι : Type} [Fintype ι] [MeasurableSpace ι] [Nonempty ι] [MeasurableSingletonClass ι]`,
`(𝓒 : CanonicalEnsemble ι) [𝓒.IsFinite] (T : Temperature) (hT : 0 < T.val)`.

| Before | After |
|---|---|
| `⊢ P (𝓒.heatCapacity T)` | `⊢ P (𝓒.energyVariance T / (kB * ↑T.val ^ 2))` |

**R2 · `have hk := kB_pos`** changes the **context**: it adds `hk`, the statement of
`Constants.kB_pos : 0 < kB`. The goal is unchanged. Placeholders: `(G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `hk : 0 < kB ⊢ G` |

### A quotient of non-negatives

**R3 · `apply div_nonneg`** changes the **goal list**: one goal becomes two. The lemma is
`div_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a / b` (for `ℝ` and any ordered field). The new goals are named
`ha` (numerator) and `hb` (denominator). Term form: `div_nonneg proof_a proof_b`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ a / b` | `⊢ 0 ≤ a`, `⊢ 0 ≤ b` |

### The numerator: an integral of a square

**R4 · `unfold energyVariance`** changes the **goal**: the name is replaced by its definition. It is
optional: `apply`/`exact` see through definitions, so R5 applies to `𝓒.energyVariance T` directly. Use it
to see what you are proving. Placeholders: `{ι : Type} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι)
(T : Temperature)`.

| Before | After |
|---|---|
| `⊢ P (𝓒.energyVariance T)` | `⊢ P (∫ (i : ι), (𝓒.energy i - 𝓒.meanEnergy T) ^ 2 ∂𝓒.μProd T)` |

**R5 · `apply MeasureTheory.integral_nonneg`** changes the **goal**. The lemma is
`MeasureTheory.integral_nonneg : 0 ≤ f → 0 ≤ ∫ x, f x ∂μ`, for any measure `μ`, with no integrability
assumption (a non-integrable `f` has integral `0`). Placeholders:
`{α : Type} [MeasurableSpace α] (μ : MeasureTheory.Measure α) (f : α → ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ ∫ (x : α), f x ∂μ` | `⊢ 0 ≤ f` |

**R6 · `intro x`** on `0 ≤ f` changes the **context and the goal**. For functions, `≤` is pointwise, so
`0 ≤ f` *is* `∀ x, 0 x ≤ f x`, and `intro` (or the term `fun x => …`) opens the `∀`. Placeholders:
`{α : Type} (f : α → ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ f` | `x : α ⊢ 0 x ≤ f x` |

**R7 · `exact sq_nonneg a`** **closes** `0 ≤ a ^ 2`. The lemma is `sq_nonneg a : 0 ≤ a ^ 2` (for `ℝ` and
any ordered ring). In the exercise the goal after R6 reads `0 x ≤ (fun x => (… - …) ^ 2) x`; `exact` unfolds
`0 x` to `0` and applies the `fun`, so `exact sq_nonneg _` closes it (`_`: Lean finds `a`).

| Before | After |
|---|---|
| `⊢ 0 ≤ a ^ 2` | no goals |

### The denominator

**R8 · `positivity`** **closes** a goal `0 ≤ e` or `0 < e` (also `e ≠ 0`) where `e` is built from `*`, `/`,
`+`, `^`, casts, … of pieces it can sign. Squares and casts of `ℝ≥0` values are `≥ 0` by themselves; an
atom such as `kB` (or `c`) needs a hypothesis `0 < kB` in the context, which is why R2 comes first.
Placeholders: `(c : ℝ) (t : NNReal) (hc : 0 < c)`.

| Before | After |
|---|---|
| `hc : 0 < c ⊢ 0 ≤ c * ↑t ^ 2` | no goals |

### Worked combinations (W1–W2, on a quotient that is not the exercise's)

**W1: step by step.** `0 ≤ (∫ x, (g x - m) ^ 2 ∂μ) / (c * ↑t ^ 2)` for any measure `μ`, `g : α → ℝ`,
`m c : ℝ`, `t : ℝ≥0`, `hc : 0 < c`. R3 splits it into the two goals below; the first is closed by R5, R6,
R7, the second by R8:

```lean-goal
⊢ 0 ≤ (∫ (x : α), (g x - m) ^ 2 ∂μ) / (c * ↑t ^ 2)
⊢ 0 ≤ ∫ (x : α), (g x - m) ^ 2 ∂μ
⊢ 0 ≤ c * ↑t ^ 2
```

**W2: one term.** The same proof as a term:
`div_nonneg (MeasureTheory.integral_nonneg fun _ => sq_nonneg _) (by positivity)`. Here `fun _ => …` is R6
in term form, and `(by positivity)` runs a tactic inside a term.

---

## Traps

- Do not try to differentiate: `heatCapacity` is a `derivWithin` of the mean energy, and nothing about it
  is easy to compute by hand. R1 replaces it before any other step.
- `positivity` fails on `0 ≤ kB * ↑T.val ^ 2` if `hk : 0 < kB` is not in the context
  ("failed to prove positivity/nonnegativity/nonzeroness"): it does not know `kB` is positive. Do R2 first,
  before the `exact`/`apply` that contains `by positivity`.
- R1 needs `hT : 0 < T.val`; at `T = 0` the theorem says nothing. Pass `hT` explicitly; the instance
  arguments (`[𝓒.IsFinite]`, …) you never pass.
- `rw [h]`-style rewriting is not needed under the integral: R5 removes the `∫` instead.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `𝓒.heatCapacity T` → `𝓒.energyVariance T / (kB * ↑T.val ^ 2)` | `rw [fluctuation_dissipation_theorem_finite 𝓒 T hT]` | R1 |
| `0 < kB` in the context | `have hk := kB_pos` | R2 |
| `0 ≤ a / b` → `0 ≤ a`, `0 ≤ b` | `apply div_nonneg` / `div_nonneg ha hb` | R3 |
| see the variance as an integral | `unfold energyVariance` (optional) | R4 |
| `0 ≤ ∫ x, f x ∂μ` → `0 ≤ f` | `apply MeasureTheory.integral_nonneg` | R5 |
| `0 ≤ f` (function) → `0 x ≤ f x` | `intro x` / `fun x => …` | R6 |
| `0 ≤ a ^ 2` | `exact sq_nonneg _` | R7 |
| `0 ≤ c * ↑t ^ 2` with `0 < c` known | `positivity` | R8 |
| numerator and denominator in one term | `div_nonneg (MeasureTheory.integral_nonneg fun _ => sq_nonneg _) (by positivity)` | W2 |
| see the state | infoview | |
