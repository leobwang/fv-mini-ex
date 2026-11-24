# E101 · Laws: the Gaussian: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033); the measures, integrals `∫ x, f x ∂μ` and `Var[X; P]`
met in E095–E097 help but are re-explained below. **New here:** the law (distribution) of a random
variable, `HasLaw X μ P`, the Gaussian measure `gaussianReal m v`, and the nonnegative reals `ℝ≥0`
with their cast `↑v` into `ℝ`.

The idea: a question about the mean or variance of `X : Ω → ℝ` depends only on the law of `X` (the
measure `μ` on `ℝ` with `μ(B) = P(X ∈ B)`). So first move the question from `(Ω, P)` to `(ℝ, μ)`
(R2, R4), then answer it with what Mathlib knows about `μ` (R3, R5).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal. (So in the guide the underlying measure is called `Q`, not `P`.)
- Placeholders are written as Lean binders: `{Ω : Type} [MeasurableSpace Ω]` is a sample space with its
  σ-algebra, `(Q : Measure Ω)` a measure on it, `(Y : Ω → ℝ)` a real random variable, `(μ : Measure ℝ)`
  a measure on `ℝ` (the law), `(m : ℝ) (v : ℝ≥0)` the Gaussian's parameters.
- Every `⊢` cell and goal line is a state Lean reaches in the companion file; `tools/guide_sync.py`
  checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Ω : Type u_1` | the spec's `{Ω : Type*}`: `Ω` is a type in any universe level `u_1`; read it as "`Ω` is a type" |
| `Measure Ω` | a measure on `Ω` (with its σ-algebra, the instance `[MeasurableSpace Ω]`, printed `inst✝`) |
| `∫ (x : Ω), X x ∂P` | the integral of `X` against `P`: for a probability measure, `E[X]`. You type `P[X]` (notation) or `∫ x, X x ∂P` (`\int`, `\partial`); the infoview always shows the `∫` form |
| `Var[X; P]` | `ProbabilityTheory.variance X P`, the variance `E[(X − E[X])²]` of `X` under `P` (a real number; Mathlib returns `0` when it is infinite) |
| `HasLaw X μ P` | the law of `X` under `P` is `μ`: `X` is almost-everywhere measurable and `P.map X = μ`, i.e. `μ(B) = P(X⁻¹(B))` for measurable `B`. Fields: `hX.aemeasurable`, `hX.map_eq` |
| `gaussianReal m v : Measure ℝ` | the normal law `N(m, v)`: density `(2πv)^(−1/2) exp(−(x − m)²/(2v))` for `v ≠ 0`, the point mass at `m` for `v = 0` |
| `ℝ≥0` | `NNReal`, the reals `≥ 0` (needs `open scoped NNReal`); the variance parameter has this type |
| `↑v` | `v : ℝ≥0` cast to `ℝ` (`NNReal.toReal v`). In the statement `Var[X; P] = v` Lean inserts it, so the goal reads `Var[X; P] = ↑v` |
| `id` | the identity function `fun x => x`; `Var[id; μ]` is the variance of the coordinate `x` under `μ` |
| `∫ (x : ℝ), x ∂μ` | the mean of the law `μ` |
| `Measure.dirac c` | the point mass at `c` (Part W only) |
| `case refine_1`, `case refine_2` | the two goals after R1: the mean and the variance |

---

## Part 1 · `gaussian_moments`

Statement: if `hX : HasLaw X (gaussianReal m v) P`, then `P[X] = m ∧ Var[X; P] = v`, i.e. the goal
`∫ (x : Ω), X x ∂P = m ∧ Var[X; P] = ↑v`. Split it (R1); each half is two rewrites: to the law, then
the Gaussian fact.

**R1 · `refine ⟨?_, ?_⟩`** changes the **goal list**: `A ∧ B` becomes two goals. `constructor` does the same.
As a term, `⟨by tac₁, by tac₂⟩` proves both halves in place (TACTIC_STATES, "Structure").
Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ B` | `⊢ A`, `⊢ B` |

**R2 · `rw [hY.integral_eq]`** changes the **goal**. The lemma is
`HasLaw.integral_eq : HasLaw X μ P → ∫ x, X x ∂P = ∫ x, x ∂μ` (for `X` with values in `ℝ`, or more generally in
a real normed space with second-countable topology whose σ-algebra contains the open sets). From `hY : HasLaw Y μ Q`, the dot-notation term
`hY.integral_eq` is that equation, so `rw` replaces the mean of `Y` by the mean of its law. `Ω` and `Q`
disappear from the goal. Placeholders: `{Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) (Y : Ω → ℝ)
(μ : Measure ℝ) (hY : HasLaw Y μ Q)`.

| Before | After |
|---|---|
| `hY : HasLaw Y μ Q ⊢ P (∫ (x : Ω), Y x ∂Q)` | `hY : HasLaw Y μ Q ⊢ P (∫ (x : ℝ), x ∂μ)` |

**R3 · `rw [integral_id_gaussianReal]`** changes the **goal**. The lemma is
`integral_id_gaussianReal : ∫ x, x ∂gaussianReal μ v = μ` (Mathlib names the mean `μ` here; it is a real
number, our `m`). Both arguments are implicit, found by matching. Placeholders: `(m : ℝ) (v : ℝ≥0)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ), x ∂gaussianReal m v)` | `⊢ P m` |

**R4 · `rw [hY.variance_eq]`** changes the **goal**. The lemma is
`HasLaw.variance_eq : HasLaw X μ P → Var[X; P] = Var[id; μ]` (for `X : Ω → ℝ`). Under the law `μ`, the
identity `id` plays the role of `Y`. Placeholders: as in R2.

| Before | After |
|---|---|
| `hY : HasLaw Y μ Q ⊢ P Var[Y; Q]` | `hY : HasLaw Y μ Q ⊢ P Var[id; μ]` |

**R5 · `rw [variance_id_gaussianReal]`** changes the **goal**. The lemma is
`variance_id_gaussianReal : Var[id; gaussianReal μ v] = ↑v`. The right side is the cast `↑v : ℝ`, which is
exactly what the goal's right side `↑v` is. Placeholders: `(m : ℝ) (v : ℝ≥0)`.

| Before | After |
|---|---|
| `⊢ P Var[id; gaussianReal m v]` | `⊢ P ↑v` |

After the second rewrite of each half the goal is `m = m` or `↑v = ↑v`, and `rw` closes it by itself
(it tries `rfl` after rewriting).

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: a point mass.** `hY : HasLaw Y (Measure.dirac c) Q` says `Y = c` almost surely. The two facts about
`dirac c` are `integral_dirac f c : ∫ x, f x ∂dirac c = f c` and `variance_dirac c : Var[X; dirac c] = 0`;
they play the roles of R3 and R5. Goal `Q[Y] + Var[Y; Q] = c`, after R2, `integral_dirac`, R4,
`variance_dirac`, and finally `simp`:

```lean-goal
⊢ ∫ (x : Ω), Y x ∂Q + Var[Y; Q] = c
⊢ ∫ (x : ℝ), x ∂Measure.dirac c + Var[Y; Q] = c
⊢ c + Var[Y; Q] = c
⊢ c + Var[id; Measure.dirac c] = c
⊢ c + 0 = c
```

**W2: as one term.** `Q[Y] = c ∧ Var[Y; Q] = 0` is
`⟨by rw [hY.integral_eq, integral_dirac], by rw [hY.variance_eq, variance_dirac]⟩`: R1's term form, each
half two rewrites in one `rw [a, b]`, each closed by `rw`'s `rfl`.

---

## Traps

- `P[X]` is only notation: the goal shows `∫ (x : Ω), X x ∂P`. `rw` matches that form, so R2 applies.
- R2's right side is `∫ x, x ∂μ`, the integral of the identity. R3 is stated in exactly this form, so the
  two chain; a lemma about `∫ x, f x ∂μ` for some other `f` would not match.
- R4 produces `Var[id; μ]`, not `Var[fun x => x; μ]`; R5 is stated with `id`, so they chain.
- `v : ℝ≥0`, not `ℝ`: the goal's right side is the cast `↑v`. Do not try to prove `Var[…] = v` at type
  `ℝ≥0`; R5 already produces `↑v`.
- Inside the spec, the measure is named `P`. In the guide `P` is "the rest of the goal" and the measure is
  `Q`.
- `HasLaw` lemmas are used by dot notation on the hypothesis: `hX.integral_eq`, not `integral_eq hX` (the
  full names are `ProbabilityTheory.HasLaw.integral_eq` / `.variance_eq`).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| split `A ∧ B` | `refine ⟨?_, ?_⟩` / `constructor` / term `⟨by …, by …⟩` | R1 |
| mean of `X` → mean of its law | `rw [hX.integral_eq]` | R2 |
| mean of `N(m, v)` | `rw [integral_id_gaussianReal]` (`= m`) | R3 |
| variance of `X` → variance of its law | `rw [hX.variance_eq]` | R4 |
| variance of `N(m, v)` | `rw [variance_id_gaussianReal]` (`= ↑v`) | R5 |
| mean / variance of `dirac c` | `integral_dirac` (`= f c`) / `variance_dirac` (`= 0`) | W1 |
| several rewrites at once | `rw [a, b]` (closes `x = x` by itself) | W2 |
| see the state | infoview | |
