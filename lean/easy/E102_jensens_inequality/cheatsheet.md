# E102 · Jensen's inequality: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's measures and integrals
(`Measure`, `∫ … ∂μ`, `μ[X]`, `Integrable`, "almost everywhere" `∀ᵐ`), convex functions (`ConvexOn`),
continuity (`Continuous`, `ContinuousOn`), closed sets (`IsClosed`), and Jensen's inequality
`ConvexOn.map_integral_le`.

## How to read an entry

Each entry is one tactic or one lemma used with `refine`/`apply`/`exact`/`rw`. It says what changes
(**goal**, **context**, or **goal list**), gives the lemma's statement, lists the placeholders with their
types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[TopologicalSpace α]`
  is a requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Ω : Type u_1` | how `{Ω : Type*}` prints: `Ω` is an arbitrary type (in some universe `u_1`); `Type*` is `Type` with the universe left general |
| `inst✝ : IsProbabilityMeasure μ` | an unnamed instance argument `[…]` from the statement; `✝` marks a name you cannot refer to |
| `MeasurableSpace Ω` | `Ω` carries a σ-algebra: the family of subsets ("events") a measure can measure |
| `Measure Ω` | a measure `μ`: a countably additive map from those sets to `[0, ∞]` |
| `IsProbabilityMeasure μ` | `μ Set.univ = 1`: `μ` is a probability measure, `Ω` the sample space |
| `X : Ω → ℝ` | a real random variable |
| `∫ (x : Ω), f x ∂μ` | the (Bochner) integral of `f` against `μ`; for a probability measure it is the expectation `E[f]`. It is defined as `0` when `f` is not integrable, which is why the problem hands you integrability facts |
| `μ[X]` | notation for `∫ x, X x ∂μ`. The infoview never shows `μ[…]`: it prints the `∫` form |
| `∫ (x : Ω), (fun ω => Real.exp (X ω)) x ∂μ` | how `μ[fun ω => Real.exp (X ω)]` prints: the `fun` is applied to `x` but not reduced. It is the same term as `∫ x, Real.exp (X x) ∂μ` |
| `Integrable f μ` | `f` is measurable and the integral of its absolute value is finite |
| `∀ᵐ (x : Ω) ∂μ, p x` | `p x` holds for `μ`-almost every `x`: the set where it fails has measure `0` |
| `Set.univ` | the set of all elements of the type (here all of `ℝ`) |
| `Set ℝ`, `b ∈ s` | the type of sets of reals; `b` is an element of the set `s` |
| `ConvexOn ℝ s g` | `s` is convex and `g (t•a + (1-t)•b) ≤ t•g a + (1-t)•g b` for `a, b ∈ s`, `t ∈ [0, 1]` |
| `Continuous g`, `ContinuousOn g s` | `g` is continuous everywhere, resp. restricted to `s` |
| `IsClosed s` | `s` is a closed set (contains its limit points) |
| `g ∘ f` | composition `fun x => g (f x)` |
| `Real.exp` | the real exponential `x ↦ eˣ` |
| `Even n` | `∃ r, n = r + r` |
| `case left`, `case right` | the two halves of an `∧` after `constructor`; `case left.refine_3` is the third `?_` of a `refine` inside `left` |
| `?s` (a name with `?`) | a metavariable: a part of a term Lean has not determined yet (see Traps) |

---

## Part 1 · `jensen`

Statement: for a probability measure `μ` and an integrable `X` (with `exp ∘ X` and `X²` integrable),
`exp(E[X]) ≤ E[exp X]` and `(E[X])² ≤ E[X²]`. Both halves are Jensen's inequality
`g(E[f]) ≤ E[g ∘ f]` for a convex `g`, with `f = X` and the set `s = Set.univ`.

Route: split the `∧` (`constructor`, TACTIC_STATES "Structure"). In each half apply Jensen (R1) with the
convexity proof as first argument (R2 for `exp`; R9 → R10 for `x ^ 2`), then close the five side goals:
continuity (R3 with R4 or R11), closedness (R5), almost-everywhere membership (R6, `intro a`, R7), and the two
integrability hypotheses (`exact`; R8 says why the composed one matches).

### Jensen's inequality

**R1 · `ConvexOn.map_integral_le`** changes the **goal list**: one goal becomes five. The lemma is

```
ConvexOn.map_integral_le : ConvexOn ℝ s g → ContinuousOn g s → IsClosed s →
  (∀ᵐ x ∂μ, f x ∈ s) → Integrable f μ → Integrable (g ∘ f) μ →
  g (∫ x, f x ∂μ) ≤ ∫ x, g (f x) ∂μ
```

for a probability measure `μ` (instance argument `[IsProbabilityMeasure μ]`). Write
`refine ConvexOn.map_integral_le hg ?_ ?_ ?_ ?_ ?_` with the convexity proof `hg` given: it fixes `g` and `s`,
and each `?_` becomes a goal, in argument order. Placeholders: `{Ω : Type} [MeasurableSpace Ω]
(μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (g : ℝ → ℝ) (s : Set ℝ)`. (Mathlib allows `f` with values
in any complete normed real vector space `E`; here `E = ℝ`.)

| Before | After |
|---|---|
| `⊢ g (∫ (x : Ω), f x ∂μ) ≤ ∫ (x : Ω), g (f x) ∂μ` | `⊢ ContinuousOn g s`, `⊢ IsClosed s`, `⊢ ∀ᵐ (x : Ω) ∂μ, f x ∈ s`, `⊢ Integrable f μ`, `⊢ Integrable (g ∘ f) μ` |

### The convex function `Real.exp`

**R2 · `convexOn_exp`** **closes** the goal. The lemma is `convexOn_exp : ConvexOn ℝ Set.univ Real.exp`. As the
first argument of R1 it sets `g = Real.exp`, `s = Set.univ`.

| Before | After |
|---|---|
| `⊢ ConvexOn ℝ Set.univ Real.exp` | no goals |

**R3 · `Continuous.continuousOn`** changes the **goal**. The lemma is
`Continuous.continuousOn : Continuous g → ContinuousOn g s`: continuous everywhere implies continuous on any
`s`. With `apply` the goal becomes `Continuous g`; as a term, `hc.continuousOn` (dot notation: `hc : Continuous g`
is the first explicit argument). Placeholders: `{α β : Type} [TopologicalSpace α] [TopologicalSpace β]`
(`α`, `β` carry a topology; `ℝ`, `ℂ` do), `(g : α → β) (s : Set α)`.

| Before | After |
|---|---|
| `⊢ ContinuousOn g s` | `⊢ Continuous g` |

**R4 · `Real.continuous_exp`** **closes** the goal. The lemma is `Real.continuous_exp : Continuous Real.exp`.
So `Real.continuous_exp.continuousOn : ContinuousOn Real.exp s` (R3 as a term).

| Before | After |
|---|---|
| `⊢ Continuous Real.exp` | no goals |

### The side conditions on `s = Set.univ`

**R5 · `isClosed_univ`** **closes** the goal. The lemma is `isClosed_univ : IsClosed Set.univ` in any
topological space. Placeholders: `{X : Type} [TopologicalSpace X]`.

| Before | After |
|---|---|
| `⊢ IsClosed Set.univ` | no goals |

**R6 · `ae_of_all`** changes the **goal**. The lemma is `ae_of_all μ : (∀ a, p a) → ∀ᵐ a ∂μ, p a`: what holds
everywhere holds almost everywhere. `μ` is explicit; write `ae_of_all _ …` and Lean reads it off the goal.
Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (p : Ω → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ᵐ (x : Ω) ∂μ, p x` | `⊢ ∀ (a : Ω), p a` |

**R7 · `Set.mem_univ`** **closes** the goal. The lemma is `Set.mem_univ (b : β) : b ∈ Set.univ`. After R6 the
goal is `∀ a, f a ∈ Set.univ`: in tactic mode `intro a` then `exact Set.mem_univ _`, or as one term
`fun _ => Set.mem_univ _` (`_` lets Lean fill in `f a`).
So the third side goal of R1 is `ae_of_all _ fun _ => Set.mem_univ _`. Placeholders: `{β : Type} (b : β)`.

| Before | After |
|---|---|
| `⊢ b ∈ Set.univ` | no goals |

**R8 · `Function.comp_def`** changes the **goal**. The lemma is `g ∘ f = fun x => g (f x)`. The two sides are
equal *by definition*, so you rarely need the rewrite: `exact h` with `h : Integrable (fun ω => Real.exp (X ω)) μ`
closes the goal `Integrable (Real.exp ∘ X) μ` as it stands. Placeholders: `{α β γ : Type} (f : α → β) (g : β → γ)`.

| Before | After |
|---|---|
| `⊢ P (g ∘ f)` | `⊢ P fun x => g (f x)` |

### The convex function `x ↦ x ^ n`

**R9 · `Even.convexOn_pow`** changes the **goal**. The lemma is
`Even.convexOn_pow : Even n → ConvexOn 𝕜 Set.univ fun x => x ^ n`: an even power is convex on the whole line.
With `apply`, the goal becomes `Even n`; as a term, `Even.convexOn_pow hn`. Placeholders: `(n : ℕ)`, and `𝕜`
an ordered commutative ring (`[CommRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`; `ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ ConvexOn ℝ Set.univ fun x => x ^ n` | `⊢ Even n` |

**R10 · `even_two`** **closes** the goal. The lemma is `even_two : Even 2` (in `ℕ`, `ℤ`, `ℝ`, …; Lean picks
the type from the goal). So `Even.convexOn_pow even_two : ConvexOn ℝ Set.univ fun x => x ^ 2`.

| Before | After |
|---|---|
| `⊢ Even 2` | no goals |

**R11 · `continuous_pow`** **closes** the goal. The lemma is `continuous_pow (n : ℕ) : Continuous fun a => a ^ n`
(in any topological monoid; `ℝ` qualifies). `n` is explicit: write `continuous_pow 2`, and
`(continuous_pow 2).continuousOn` for R3 as a term.

| Before | After |
|---|---|
| `⊢ Continuous fun x => x ^ n` | no goals |

### Worked combinations (W1–W2, on the fourth power, not the exercise's objects)

**W1.** Jensen for `x ↦ x ^ 4` in tactic mode. `refine ConvexOn.map_integral_le (Even.convexOn_pow (by decide : Even 4)) ?_ ?_ ?_ ?_ ?_`
turns the goal into five side goals, each closed by one `exact` (R3 + R11, R5, R6 + R7, then the two
hypotheses; the last via R8):

```lean-goal
⊢ (∫ (ω : Ω), Y ω ∂ν) ^ 4 ≤ ∫ (ω : Ω), Y ω ^ 4 ∂ν
⊢ ContinuousOn (fun x => x ^ 4) Set.univ
⊢ IsClosed Set.univ
⊢ ∀ᵐ (x : Ω) ∂ν, Y x ∈ Set.univ
⊢ Integrable Y ν
⊢ Integrable ((fun x => x ^ 4) ∘ Y) ν
```

**W2.** The same inequality as a single term: put the five proofs of W1 in place of the five `?_`, in order.

---

## Traps

- Give the convexity proof as R1's **first** argument. With every argument left as `?_`, Lean must guess `g`
  from the goal; for `(∫ …) ^ 2` it cannot, and the error is the unhelpful "typeclass instance problem is
  stuck". Naming only `g` (`(g := …)`) is not enough either: `s` is then still unknown.
- `apply ConvexOn.map_integral_le` works on the `exp` half but leaves the set as a metavariable `?s` (printed
  like `?left.s`) and adds a goal `Set ℝ`. Closing the convexity goal with R2 first fixes `s = Set.univ`.
- The infoview prints `μ[X]` as `∫ (x : Ω), X x ∂μ`, and `μ[fun ω => …]` with an unreduced `(fun ω => …) x`.
  Neither needs simplifying: `refine`/`exact` see through it.
- `Integrable (Real.exp ∘ X) μ` and `Integrable (fun ω => Real.exp (X ω)) μ` are the same statement (R8); `exact`
  accepts one for the other.
- The `∫` of a non-integrable function is `0`, so Jensen genuinely needs both integrability arguments; they are
  the hypotheses `hX` and `hexp` / `hsq`, not something to prove.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| split `A ∧ B` | `constructor` or `⟨_, _⟩` | TACTIC_STATES |
| Jensen, five side goals | `refine ConvexOn.map_integral_le hg ?_ ?_ ?_ ?_ ?_` | R1 |
| `exp` is convex | `convexOn_exp` | R2 |
| `x ^ n` is convex, `n` even | `Even.convexOn_pow hn`, `hn := even_two` for `n = 2` | R9, R10 |
| `ContinuousOn g s` from `Continuous g` | `hc.continuousOn` | R3 |
| `exp`, `x ^ n` continuous | `Real.continuous_exp`, `continuous_pow n` | R4, R11 |
| `IsClosed Set.univ` | `isClosed_univ` | R5 |
| `∀ᵐ x ∂μ, f x ∈ Set.univ` | `ae_of_all _ fun _ => Set.mem_univ _` | R6, R7 |
| `Integrable (g ∘ f) μ` from a `fun` hypothesis | `exact h` | R8 |
| see the state | infoview | |
