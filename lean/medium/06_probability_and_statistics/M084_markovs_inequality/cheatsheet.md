# M084 · Markov's inequality: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's measure theory: measurable
spaces and sets, measurable and integrable functions, the Bochner integral `∫ x, f x ∂μ` (the
expectation `μ[X]`), `μ.real`, set-builder sets `{ω | p ω}` and indicator functions `S.indicator f`.

The math: with $S = \{\omega : c \le X(\omega)\}$, pointwise $c\,\mathbf 1_S \le X$ (on $S$ because
$c \le X$, off $S$ because $0 \le X$). Integrate: $\int c\,\mathbf 1_S\,d\mu = c\,\mu(S) \le \int X\,d\mu$.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`apply`/`exact`/`have`. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the proof
state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`, `P : Set Ω → Prop`). The step changes only the part
  inside `P (…)`, wherever it sits in a larger goal.
- Placeholders are written as Lean binders. `{Ω : Type}` is any type. A bracket such as `[Zero M]` or
  `[IsFiniteMeasure μ]` is a requirement Lean must find (a *type class* instance). Each entry says when
  the exercise meets it.
- States that contain a set `{ω | …}` are shown in a ```` ```lean-goal ```` block, before then after (a
  `|` cannot sit inside a table cell).
- `exacts [h₁, h₂]` closes the open goals in order, like `exact h₁` then `exact h₂`; the examples use
  it to close the goals an `apply` leaves.
- Every `⊢` cell and every `lean-goal` line is a state Lean reaches in the companion file;
  `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Ω`, `ω : Ω` | the sample space and an outcome |
| `Set Ω` | the type of subsets of `Ω` (a set is a predicate `Ω → Prop`) |
| `MeasurableSpace Ω` | a σ-algebra on `Ω`: the family of sets ("events") that have a probability |
| `MeasurableSet S` | `S` is in that σ-algebra |
| `μ : Measure Ω` | a measure; `μ S : ℝ≥0∞` (extended non-negative reals `[0, ∞]`) is the measure of `S` |
| `IsProbabilityMeasure μ` | `μ Set.univ = 1`. Lean derives `IsFiniteMeasure μ` from it by itself (needed by R9) |
| `μ.real S` | `(μ S).toReal`: the probability of `S` as a real number, so it can be multiplied by `c : ℝ` |
| `Measurable X` | preimages of measurable sets of `ℝ` are measurable: `X` is a random variable |
| `Integrable X μ` | `X` is measurable (almost everywhere) and `∫ ‖X‖ dμ < ∞` |
| `μ[X]` | the expectation `∫ x, X x ∂μ`. Lean **prints** it as `∫ (x : Ω), X x ∂μ` |
| `∫ (x : Ω), f x ∂μ` | the (Bochner) integral of `f` against `μ`. A non-integrable `f` gets the junk value `0`, which is why R11 asks for integrability |
| `{ω \| c ≤ X ω}` | the set of `ω` with `c ≤ X ω` (`setOf`). `ω ∈ {ω \| p ω}` is by definition `p ω` (R7) |
| `S.indicator f` | `Set.indicator S f`: equals `f ω` for `ω ∈ S` and `0` otherwise (needs `[Zero M]`; `ℝ` has it) |
| `fun x => c` | the constant function `c`; Lean names the unused binder `x` |
| `S.indicator (fun x => c)` | $c\,\mathbf 1_S$. As a whole function Lean prints it `S.indicator fun x => c`, and in `hle` as `(S.indicator fun x => c) ≤ X` |
| `f ≤ g` (functions) | `∀ ω, f ω ≤ g ω` by definition (R4) |
| `a • b` | scalar multiplication; for `a b : ℝ` it is `a * b` (R13) |
| `S : Set Ω := e` | a local definition made by `set` (R1): `S` stands for `e`. Inside some goals Lean elides `e` as `S : Set Ω := ⋯` |
| `case hf`, `case hg` | the goals `apply measurableSet_le` leaves (R2), named after the lemma's arguments; the first prints as `Measurable fun a => c` |
| `ω ∉ S` | `¬ (ω ∈ S)` |
| `case pos`, `case neg` | the two goals of `by_cases` (R5): with `h : ω ∈ S` and with `h : ω ∉ S` |
| `this` | the name `have :=` gives a fact you did not name |
| `inst✝ : …` | an unnamed instance hypothesis, such as `[MeasurableSpace Ω]` |
| `Type*`, `Type u_1` | a type in some universe: read it as `Type` |

---

## Part 1 · `markov`

Statement: for a probability measure `μ`, a measurable, integrable `X ≥ 0` and any `c : ℝ`,
`c * μ.real {ω | c ≤ X ω} ≤ μ[X]`. After `set S := {ω | c ≤ X ω}` (R1) the goal reads
`c * μ.real S ≤ ∫ (x : Ω), X x ∂μ`.

### Naming the event

**R1 · `set S := e`** changes the **context and the goal**: it adds the local definition `S : T := e`
and replaces every `e` in the goal by `S`. Lean still knows that `S` unfolds to `e`, so later `exact`
steps can see through it. Placeholders: `{Ω : Type} (p : Ω → Prop) (P : Set Ω → Prop)`. Before, then
after (the context gains `S : Set Ω := {ω | p ω}`):

```lean-goal
⊢ P {ω | p ω}
⊢ P S
```

### Measurability of the event

**R2 · `measurableSet_le`** changes the **goal list**. The lemma is
`Measurable f → Measurable g → MeasurableSet {ω | f ω ≤ g ω}` (for `ℝ`-valued `f g`; any ordered
space with the right topology works). `apply` leaves the two measurability goals; as a term, write
`measurableSet_le hf hg`. Placeholders: `{Ω : Type} [MeasurableSpace Ω] (f g : Ω → ℝ)`. In the
exercise `f` is the constant function `fun _ => c`. Before, then the two goals after:

```lean-goal
⊢ MeasurableSet {ω | f ω ≤ g ω}
⊢ Measurable f
⊢ Measurable g
```

**R3 · `measurable_const`** **closes** the goal: a constant function is measurable. Placeholders:
`(c : ℝ)`.

| Before | After |
|---|---|
| `⊢ Measurable fun x => c` | closed |

### The pointwise comparison `S.indicator (fun _ => c) ≤ X`

Prove it as a `have` (TACTIC_STATES, "Adding facts") with its own `by` block.

**R4 · `intro ω` on `f ≤ g`** changes the **context and the goal**. On functions, `≤` is by definition
pointwise (`Pi.le_def`), so `intro` works as on a `∀`. Placeholders: `{Ω : Type} (f g : Ω → ℝ)`.

| Before | After |
|---|---|
| `⊢ f ≤ g` | `ω : Ω ⊢ f ω ≤ g ω` |

**R5 · `by_cases h : ω ∈ S`** changes the **goal list**: the goal is split by whether `ω ∈ S`; each copy
gets `h`. Work on each with a bullet `·`. Placeholders: `{Ω : Type} (S : Set Ω) (ω : Ω) (Q : Prop)`.

| Before | After |
|---|---|
| `⊢ Q` | `h : ω ∈ S ⊢ Q`, `h : ω ∉ S ⊢ Q` |

**R6 · `rw [Set.indicator_of_mem h]`** changes the **goal**. The lemma is
`Set.indicator_of_mem : ω ∈ S → ∀ f, S.indicator f ω = f ω`; `rw` also beta-reduces `(fun _ => c) ω`
to `c`. Placeholders: `{Ω M : Type} [Zero M] (S : Set Ω) (c : M) (ω : Ω) (hω : ω ∈ S)`.

| Before | After |
|---|---|
| `⊢ P (S.indicator (fun x => c) ω)` | `⊢ P c` |

**R7 · `exact hω`** with `hω : ω ∈ {x | p x}` **closes** `p ω`: membership in a set-builder set is by
definition the predicate (`Set.mem_setOf_eq : a ∈ {x | p x} = p a`, which you could also `rw` with).
`exact` sees through a `set` name too: `h : ω ∈ S` proves `c ≤ X ω`. Placeholders:
`{Ω : Type} (p : Ω → Prop) (ω : Ω)`. With `hω : ω ∈ {x | p x}` in the context, before (after: closed):

```lean-goal
⊢ p ω
```

**R8 · `rw [Set.indicator_of_notMem h]`** changes the **goal**. The lemma is
`Set.indicator_of_notMem : ω ∉ S → ∀ f, S.indicator f ω = 0`. Placeholders:
`{Ω M : Type} [Zero M] (S : Set Ω) (f : Ω → M) (ω : Ω) (hω : ω ∉ S)`. In the exercise the goal is then
`0 ≤ X ω`: that is `hnn ω`.

| Before | After |
|---|---|
| `⊢ P (S.indicator f ω)` | `⊢ P 0` |

### Integrability of both sides

**R9 · `integrable_const c`** **closes** `Integrable (fun x => c) μ`. It needs `[IsFiniteMeasure μ]`,
which a probability measure provides. Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
[IsFiniteMeasure μ] (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ Integrable (fun x => c) μ` | closed |

**R10 · `Integrable.indicator`** changes the **goal list**. The lemma is
`Integrable f μ → MeasurableSet S → Integrable (S.indicator f) μ`: cutting a function down to a
measurable set keeps it integrable. `apply` leaves both hypotheses as goals. Its name starts with
`Integrable.`, so with `hf : Integrable f μ` you can write it as `hf.indicator hS` (dot notation), and
`(integrable_const c).indicator hS : Integrable (S.indicator fun _ => c) μ`. Placeholders:
`{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (S : Set Ω)`.

| Before | After |
|---|---|
| `⊢ Integrable (S.indicator f) μ` | `⊢ Integrable f μ`, `⊢ MeasurableSet S` |

### Integrating and tidying

**R11 · `have := integral_mono hf hg hfg`** changes the **context**. The lemma is
`integral_mono : Integrable f μ → Integrable g μ → f ≤ g → ∫ a, f a ∂μ ≤ ∫ a, g a ∂μ`: the integral is
monotone. The **smaller** function's integrability comes first. Placeholders:
`{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | adds `this : ∫ (x : Ω), f x ∂μ ≤ ∫ (x : Ω), g x ∂μ`; `⊢ G` |

**R12 · `rw [integral_indicator_const e hS]`** changes the **goal** (or, with `at`, a hypothesis). The
lemma is `integral_indicator_const (e) (hS : MeasurableSet S) : ∫ x, S.indicator (fun _ => e) x ∂μ =
μ.real S • e`: the integral of $e\,\mathbf 1_S$ is $\mu(S)\cdot e$, with the **measure first**.
Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (S : Set Ω) (e : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (ω : Ω), S.indicator (fun x => e) ω ∂μ)` | `⊢ P (μ.real S • e)` |

**R13 · `rw [smul_eq_mul]`** changes the **goal**. The lemma is `smul_eq_mul : a • b = a * b` when the
scalars and the vectors are the same type. Placeholders: `{α : Type} [Mul α] (a b : α)`; `ℝ` qualifies.

| Before | After |
|---|---|
| `⊢ P (a • b)` | `⊢ P (a * b)` |

**R14 · `rw [mul_comm]`** changes the **goal**. The lemma is `mul_comm : a * b = b * a`; without
arguments `rw` swaps the first product it finds (give `mul_comm x y` to pick one). Placeholders:
`{α : Type} [CommMagma α] (a b : α)` (α has a commutative `*`; `ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ P (a * b)` | `⊢ P (b * a)` |

**R15 · `rw [e] at hq`** changes the **context**: it rewrites the hypothesis `hq` instead of the goal.
`rwa [e₁, e₂] at hq` rewrites, then closes the goal with a hypothesis that matches it (`assumption`).
Placeholders: `{α : Type} (a b : α) (Q : α → Prop) (hab : a = b)`.

| Before | After |
|---|---|
| `hq : Q a ⊢ Q b` | `hq : Q b ⊢ Q b` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: a pointwise upper bound by an indicator.** `Y ≤ {ω | 0 < Y ω}.indicator (fun _ => 1)` from
`hY : ∀ ω, Y ω ≤ 1`. After R1 (`set T := {ω | 0 < Y ω}`) and R4 (`intro ω`):

```lean-goal
⊢ Y ≤ T.indicator fun x => 1
⊢ Y ω ≤ T.indicator (fun x => 1) ω
```

R5 splits on `ω ∈ T`. In the first case R6 leaves `Y ω ≤ 1`, which is `hY ω`. In the second R8 leaves
`Y ω ≤ 0`; here `h : ω ∉ T` is by definition `¬ 0 < Y ω`, and `not_lt.mp h` (`not_lt : ¬ a < b ↔ b ≤ a`)
gives `Y ω ≤ 0`.

**W2: integrating it.** `μ[Y] ≤ μ.real S` from `hYS : Y ≤ S.indicator (fun _ => 1)`. R11 with R9 and R10
as its second argument, then R12 at `this`. The goal is unchanged and `this` becomes
`∫ (x : Ω), Y x ∂μ ≤ μ.real S • 1`:

```lean-goal
⊢ ∫ (x : Ω), Y x ∂μ ≤ μ.real S
```

Finish with `rwa [smul_eq_mul, mul_one] at this` (R13, R15; `mul_one : a * 1 = a`).

**W3: measurability as one term.** `measurableSet_le hY measurable_const : MeasurableSet {ω | Y ω ≤ 2}`
(R2, R3). The constant sits on whichever side of `≤` it occupies in the set.

---

## Traps

- `c` is any real; no case split on its sign is needed. The comparison `c · 1_S ≤ X` holds for every
  `c` (on `S` by membership, off `S` by `hnn`).
- `integral_indicator_const` gives `μ.real S • c` (measure first), the goal has `c * μ.real S`: you need
  both `smul_eq_mul` (R13) and `mul_comm` (R14).
- `integral_mono` takes the integrability of the **smaller** side first: `integral_mono hsmall hbig hle`.
- `integrable_const` needs a finite measure. Here `IsProbabilityMeasure μ` supplies it; for a general
  measure the constant `c` is not integrable.
- `S.indicator (fun _ => c)`: the constant is a **function**. `S.indicator c` is a type error.
- After `by_cases` there are two goals: use bullets `·`, or the second goal is silently left for later.
- Mathlib renamed `Set.indicator_of_not_mem` to `Set.indicator_of_notMem`; older tutorials use the
  first.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| name the event | `set S := {ω \| c ≤ X ω}` | R1 |
| `{ω \| f ω ≤ g ω}` measurable | `measurableSet_le hf hg` | R2 |
| constant measurable | `measurable_const` | R3 |
| prove `f ≤ g` on functions | `intro ω` | R4 |
| split on membership | `by_cases h : ω ∈ S` | R5 |
| indicator on / off the set | `rw [Set.indicator_of_mem h]` / `rw [Set.indicator_of_notMem h]` | R6, R8 |
| use `h : ω ∈ {x \| p x}` as `p ω` | `exact h` | R7 |
| constant integrable | `integrable_const c` | R9 |
| indicator integrable | `(integrable_const c).indicator hS` | R10 |
| integrate `f ≤ g` | `have := integral_mono hf hg hle` | R11 |
| `∫ S.indicator (fun _ => e)` | `rw [integral_indicator_const e hS]` | R12 |
| `a • b → a * b` | `rw [smul_eq_mul]` | R13 |
| swap a product | `rw [mul_comm]` | R14 |
| rewrite a hypothesis, then close | `rwa [...] at this` | R15 |
| see the state | infoview | |
