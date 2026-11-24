# H058 · Empirical frequencies converge: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's measure-theoretic probability
(probability measures, measurable functions, integrals, independence, identical distribution, "almost
surely"), the strong law of large numbers `strong_law_ae`, filters and limits (`∀ᶠ`, `atTop`, `𝓝`,
`Tendsto`), and the order and metric characterisations of a limit on `ℝ`.

The mathematics. Write `Fₙ(t) = #{i < n | Xᵢ ≤ t} / n` (the *empirical CDF* of the first `n` samples) and
`F(t) = P(X₀ ≤ t)` (the CDF). The proof has three milestones and a squeeze:

1. `frequency_tendsto`: for one measurable set `A`, the frequency `#{i < n | Xᵢ ∈ A} / n → P(X₀ ∈ A)` a.s.
   This is the strong law applied to the indicators `Yᵢ = 1_A(Xᵢ)`, which are bounded (so integrable),
   pairwise independent and identically distributed, with mean `E[Y₀] = P(X₀ ∈ A)`.
2. `frequency_tendsto_rat`: a countable intersection of probability-one events has probability one, so
   a.s. the convergence holds for *every* rational threshold `q` at once (`A = (-∞, q]`).
3. `frequency_mono`: `s ≤ t → Fₙ(s) ≤ Fₙ(t)`.
4. `empirical_cdf`: fix `ω` in the good event and a continuity point `t` of `F`. For `a < F(t)` pick a
   rational `q < t` with `a < F(q)` (continuity); eventually `a < Fₙ(q) ≤ Fₙ(t)`. Symmetrically above.
   That is `Fₙ(t) → F(t)` by the order characterisation of limits.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`apply`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal, and `k : … → G` only consumes a new hypothesis.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[MeasurableSpace α]`
  is a requirement on the type (a *type class*): here, that `α` carries a σ-algebra. `ℝ`, `ℚ`, `ℕ` all carry
  their Borel σ-algebra automatically; your `Ω` gets one from the hypothesis `[MeasurableSpace Ω]`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that. A hypothesis
  whose type contains `, ` (such as `∀ᶠ x in l, p x`) is written next to the cell: "context gains `h : …`".
- A state containing `|` (absolute value, set-builder `{x | …}`) cannot sit in a Markdown table (`|` splits
  cells). Such states are given as a `lean-goal` block instead: the first line is the goal before the step,
  the next line the goal after.

## Reading the goals

| You see | It means |
|---|---|
| `Ω : Type u_1` | the sample space; `Type*` in a statement makes a universe variable `u_1` (ignore it) |
| `μ : Measure Ω`, `IsProbabilityMeasure μ` | a measure on `Ω` with `μ Ω = 1`: the probability `P` |
| `Measurable f` | preimages of measurable sets are measurable: `f` is a random variable |
| `MeasurableSet A` | `A` is in the σ-algebra (an event) |
| `μ.real S` | `P(S)` as a real number. (`μ S` itself is in `ℝ≥0∞ = [0, ∞]`; `.real` converts) |
| `∫ (x : Ω), f x ∂μ` | the integral of `f`, i.e. the expectation `E[f]` |
| `AEStronglyMeasurable f μ` | the measurability condition integrals need; follows from `Measurable f` (R4) |
| `Integrable f μ` | `E[‖f‖] < ∞` (and `f` is a.e.-strongly measurable) |
| `‖x‖` | the norm; on `ℝ` it is `\|x\|` |
| `X ⟂ᵢ[μ] Y` | `IndepFun X Y μ`: the random variables `X`, `Y` are independent under `μ` |
| `IdentDistrib X Y μ μ` | `X` and `Y` have the same law (distribution) |
| `Pairwise r` | `∀ ⦃i j⦄, i ≠ j → r i j` (R10). `strong_law_ae` prints it as `Pairwise (Function.onFun …)`, the same thing |
| `∀ᵐ (ω : Ω) ∂μ, p ω` | `p` holds almost surely: `{ω \| ¬p ω}` has measure `0` |
| `∀ᶠ (n : ℕ) in atTop, p n` | `p n` holds for all large `n` (eventually) |
| `∀ᶠ (y : ℝ) in 𝓝 x, p y` | `p` holds on some neighbourhood of `x` |
| `atTop`, `𝓝 L` | the filters "`n → ∞`" and "close to `L`" (`𝓝` needs `open Topology`) |
| `Tendsto u atTop (𝓝 L)` | `u n → L` as `n → ∞` |
| `ContinuousAt F t` | `F` is continuous at `t`; by definition `Tendsto F (𝓝 t) (𝓝 (F t))` |
| `A.indicator g` | `Set.indicator A g`: `x ↦ if x ∈ A then g x else 0` (R7) |
| `Z ⁻¹' A` | the preimage `{ω \| Z ω ∈ A}` |
| `Set.Iic c` | the interval `(-∞, c] = {x \| x ≤ c}` |
| `{ω \| X 0 ω ≤ s}` | `setOf`: the event `X₀ ≤ s`; by definition the same set as `X 0 ⁻¹' Set.Iic s` (R23) |
| `ω : Ω` in the context and `{ω \| X 0 ω ≤ ↑q}` in `hω` | after `filter_upwards … with ω`, the `ω` inside the braces is still a bound variable, not your sample point |
| `{i ∈ Finset.range n \| X i ω ≤ t}` | `(Finset.range n).filter (fun i => …)`: the indices `i < n` with `Xᵢ(ω) ≤ t` |
| `Finset.filter p s` | the same filter, printed this way when `p` is a name rather than a `fun` |
| `s.card`, `#s` | the number of elements of a finite set `s`. Lean prints `.card`; `#s` is notation that parses only after `open Finset` |
| `↑k`, `↑n`, `↑q` | a cast: a natural number `k` (or rational `q`) seen as a real |
| `a • b` | scalar multiplication; on `ℝ` it is `a * b` (R15) |
| `∑ i ∈ Finset.range n, f i` | `f 0 + … + f (n - 1)` |
| `x : α := e` | a local definition made by `set` (R1) |
| `dist y x` | the distance; on `ℝ`, `\|y - x\|` (R34) |
| `δ > 0` | `0 < δ`; `a' > L` is `L < a'` |
| `∀ ⦃y : ℝ⦄, …` | a strict-implicit binder: `h hy` supplies `y` from `hy : dist y x < δ` |
| `inst✝ : …` | an anonymous instance hypothesis; never named, used automatically |
| `case pos`, `case neg` | after `split_ifs`: the branch where the condition holds / fails |

---

## Part 1 · `frequency_tendsto` (milestone)

Statement: for a measurable `A ⊆ α`, almost surely `#{i < n | X i ω ∈ A} / n → μ.real (X 0 ⁻¹' A)`.
Plan: name `f := A.indicator (fun _ => 1)` and `Y i := f ∘ X i`; check the three hypotheses of the strong
law for `Y`; compute its mean; then match `(↑n)⁻¹ • ∑ i < n, Y i ω` with the frequency.

**R1 · `set x := e with hx`** changes the **goal and the context**: it adds a local definition `x := e`, an
equation `hx : x = e`, and replaces `e` by `x` everywhere. Placeholders: `{α : Type} (e : α)`. Use it to name
`f` and `Y`; give the type when it is not obvious: `set f : α → ℝ := A.indicator (fun _ => 1) with hf_def`.

| Before | After |
|---|---|
| `⊢ P e` | `x : α := e, hx : x = e ⊢ P x` |

**R2 · `Measurable.indicator`** changes the **goal list**: `Measurable (A.indicator g)` needs `Measurable g`
and `MeasurableSet A`. The statement: `Measurable g → MeasurableSet A → Measurable (A.indicator g)`. A constant
function is measurable (`measurable_const`). Placeholders: `{α : Type} [MeasurableSpace α] (A : Set α)
(hA : MeasurableSet A)`. In one term: `measurable_const.indicator hA`.

| Before | After `apply Measurable.indicator` |
|---|---|
| `⊢ Measurable (A.indicator fun x => 1)` | `⊢ Measurable fun x => 1`, `⊢ MeasurableSet A` |

**R3 · `hf.comp hg`** (`Measurable.comp`) changes the **context** (with `have`): `Measurable f → Measurable g →
Measurable (f ∘ g)`. Placeholders: `(f : α → ℝ) (g : Ω → α)`. Gives `Measurable (Y 0)` from `hf` and `hmeas 0`.

| Before | After `have h := hf.comp hg` |
|---|---|
| `⊢ G` | `h : Measurable (f ∘ g) ⊢ G` |

**R4 · `hf.aestronglyMeasurable`** changes the **context**: `Measurable f → AEStronglyMeasurable f μ` (for
real-valued `f`). Placeholders: `(μ : Measure Ω) (f : Ω → ℝ)`. Usually written inline:
`(hf.comp (hmeas 0)).aestronglyMeasurable`.

| Before | After |
|---|---|
| `⊢ G` | `h : AEStronglyMeasurable f μ ⊢ G` |

**R5 · `refine Integrable.of_bound hf C ?_`** changes the **goal**: an a.e. bound gives integrability on a finite
measure. Statement: `AEStronglyMeasurable f μ → ∀ C, (∀ᵐ x ∂μ, ‖f x‖ ≤ C) → Integrable f μ`, with
`[IsFiniteMeasure μ]` (a probability measure is finite; Lean finds that itself). Placeholders:
`(f : Ω → ℝ) (C : ℝ)`. For an indicator, `C = 1`.

| Before | After |
|---|---|
| `⊢ Integrable f μ` | `⊢ ∀ᵐ (x : Ω) ∂μ, ‖f x‖ ≤ C` |

**R6 · `refine Eventually.of_forall fun ω => ?_`** changes the **goal and the context**: to prove `p` a.s.
it suffices to prove it everywhere. Statement: `(∀ x, p x) → ∀ᶠ x in f, p x` (`∀ᵐ x ∂μ` *is* `∀ᶠ x in ae μ`).
Placeholders: `(p : Ω → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ᵐ (ω : Ω) ∂μ, p ω` | `ω : Ω ⊢ p ω` |

**R7 · `simp only [Set.indicator, Function.comp]`** changes the **goal**: it unfolds the indicator and the
composition into an `if`. Placeholders: `(A : Set α) (Z : Ω → α) (ω : Ω)`. In the exercise also unfold your
`set` names (`hY`, `hf_def`) in the same call.

| Before | After |
|---|---|
| `⊢ P (((A.indicator fun x => 1) ∘ Z) ω)` | `⊢ P (if Z ω ∈ A then 1 else 0)` |

**R8 · `split_ifs`** changes the **goal list**: one goal per branch of the `if`, with the condition (or its
negation) as an anonymous hypothesis `h✝`. Placeholders: `(c : Prop) [Decidable c]`.

| Before | After |
|---|---|
| `⊢ P (if c then 1 else 0)` | `h✝ : c ⊢ P 1`, `h✝ : ¬c ⊢ P 0` |

**R9 · `simp`** **closes** `‖1‖ ≤ 1` and `‖0‖ ≤ 1` (via `norm_one`, `norm_zero`). After R8, write
`split_ifs <;> simp`.

| Before | After |
|---|---|
| `⊢ ‖1‖ ≤ 1 ∧ ‖0‖ ≤ 1` | no goals |

**R10 · `intro i j hij`** on `Pairwise r` changes the **goal and the context**: `Pairwise r` unfolds to
`∀ ⦃i j⦄, i ≠ j → r i j`. As a term: `fun i j hij => …`, and `hindep hij : X i ⟂ᵢ[μ] X j` applies the
hypothesis. Placeholders: `(r : ℕ → ℕ → Prop)`.

| Before | After |
|---|---|
| `⊢ Pairwise r` | `i j : ℕ, hij : i ≠ j ⊢ r i j` |

**R11 · `hYZ.comp hφ hψ`** (`IndepFun.comp`) changes the **context**: functions of independent variables are
independent. Statement: `Y ⟂ᵢ[μ] Z → Measurable φ → Measurable ψ → (φ ∘ Y) ⟂ᵢ[μ] (ψ ∘ Z)`. Placeholders:
`(Y Z : Ω → β) (φ ψ : β → γ)`. In the exercise: `(hindep hij).comp hf hf`.

| Before | After `have h := hYZ.comp hφ hψ` |
|---|---|
| `⊢ G` | `h : (φ ∘ Y) ⟂ᵢ[μ] ψ ∘ Z ⊢ G` |

**R12 · `hYZ.comp hφ`** (`IdentDistrib.comp`) changes the **context**: a function of identically distributed
variables is identically distributed. Statement: `IdentDistrib Y Z μ μ → Measurable φ →
IdentDistrib (φ ∘ Y) (φ ∘ Z) μ μ`. Placeholders: `(Y Z : Ω → β) (φ : β → γ)`. In the exercise: `(hident i).comp hf`.

| Before | After |
|---|---|
| `⊢ G` | `h : IdentDistrib (φ ∘ Y) (φ ∘ Z) μ μ ⊢ G` |

**R13 · `rfl`** **closes** `A.indicator (fun _ => c) ∘ Z = (Z ⁻¹' A).indicator (fun _ => c)`: both sides
unfold to `fun ω => if Z ω ∈ A then c else 0`, because `ω ∈ Z ⁻¹' A` *is* `Z ω ∈ A`. Use it to restate `Y 0`
as an indicator on `Ω`, ready for R14: `have e : Y 0 = (X 0 ⁻¹' A).indicator (fun _ => 1) := rfl`.

| Before | After |
|---|---|
| `⊢ (A.indicator fun x => c) ∘ Z = (Z ⁻¹' A).indicator fun x => c` | no goals |

**R14 · `rw [integral_indicator_const e hS]`** changes the **goal**: the expectation of `e · 1_S` is
`P(S) · e`. Statement: `MeasurableSet S → ∫ x, S.indicator (fun _ => e) x ∂μ = μ.real S • e`. Placeholders:
`(S : Set Ω) (e : ℝ)`. For `S = X 0 ⁻¹' A`, measurability is `hmeas 0 hA` (a measurable function applied to a
measurable set is its measurable preimage).

| Before | After |
|---|---|
| `⊢ P (∫ (ω : Ω), S.indicator (fun x => e) ω ∂μ)` | `⊢ P (μ.real S • e)` |

**R15 · `rw [smul_eq_mul]`, `rw [mul_one]`** change the **goal**: `a • b = a * b` and `a * 1 = a`.
Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a • b)` | `⊢ P (a * b)` |
| `⊢ P (a * 1)` | `⊢ P a` |

**R16 · `strong_law_ae Y hint hind hid`** changes the **context**: the strong law of large numbers (Etemadi's
version, pairwise independence suffices). Statement, for `Y : ℕ → Ω → ℝ`:
`Integrable (Y 0) μ → Pairwise (fun i j => Y i ⟂ᵢ[μ] Y j) → (∀ i, IdentDistrib (Y i) (Y 0) μ μ) →
∀ᵐ ω ∂μ, Tendsto (fun n => (↑n)⁻¹ • ∑ i ∈ Finset.range n, Y i ω) atTop (𝓝 (∫ x, Y 0 x ∂μ))`.
Note the average is `(↑n)⁻¹ • ∑ …`, not `(∑ …) / n`.

| Before | After `have hslln := strong_law_ae Y hint hind hid` |
|---|---|
| `⊢ G` | `⊢ G`, context gains `hslln : ∀ᵐ (ω : Ω) ∂μ, Tendsto (fun n => (↑n)⁻¹ • ∑ i ∈ Finset.range n, Y i ω) atTop (𝓝 (∫ (x : Ω), Y 0 x ∂μ))` |

**R17 · `filter_upwards [h] with ω hω`** changes the **goal and the context**: to prove `q` a.s. from
`h : p` a.s., prove `q ω` for an `ω` with `p ω`. It works for any filter (`∀ᶠ n in atTop` as well, Part 4), takes
several hypotheses `[h₁, h₂]`, and the names after `with` also introduce the goal's further `∀`/`→` binders.
Placeholders: `(p q : Ω → Prop)`, `(R Q : Ω → ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ᵐ (ω : Ω) ∂μ, q ω` | `ω : Ω, hω : p ω ⊢ q ω` |
| `⊢ ∀ᵐ (ω : Ω) ∂μ, ∀ (t : ℝ), R ω t → Q ω t` (`with ω hω t ht`) | `ω : Ω, hω : p ω, t : ℝ, ht : R ω t ⊢ Q ω t` |

**R18 · `rw [e] at h`** changes the **context**: it rewrites hypothesis `h` instead of the goal. Placeholders:
`(e : a = b)`. Use it to put your mean `hmean : ∫ … = μ.real (X 0 ⁻¹' A)` into the strong-law hypothesis.

| Before | After |
|---|---|
| `h : P a ⊢ P b` | `h : P b ⊢ P b` |

**R19 · `convert h using 2 with n`** changes the **goal**: the goal and `h` are compared, and only the places
where they differ remain as equations. `using 2` stops two levels deep: past `Tendsto` and past `fun n =>`, so
you get one equation per term `n`. Placeholders: `(a b : ℕ → ℝ) (L : ℝ)`.

| Before | After |
|---|---|
| `⊢ Tendsto (fun n => a n / b n) atTop (𝓝 L)` | `n : ℕ ⊢ a n / b n = (b n)⁻¹ • a n` |

**R20 · `rw [Finset.sum_boole]`** changes the **goal**: summing `1`s over the indices where `p` holds counts
them. Statement: `(∑ i ∈ s, if p i then 1 else 0) = ↑#{i ∈ s | p i}`. Placeholders:
`{ι : Type} (s : Finset ι) (p : ι → Prop) [DecidablePred p]`. After R7 turns `Y i ω` into an `if`, the sum has
exactly this shape (`exact Finset.sum_boole _ _` also works).

Before, then after (`|` cannot sit in a table's code span):

```lean-goal
⊢ P (∑ i ∈ s, if p i then 1 else 0)
⊢ P ↑{x ∈ s | p x}.card
```

**R21 · `rw [div_eq_inv_mul]`** changes the **goal**: `a / b = b⁻¹ * a`. Placeholders: `(a b : ℝ)`. With R15
(`smul_eq_mul`) this matches `#… / ↑n` against the strong law's `(↑n)⁻¹ • …`.

| Before | After |
|---|---|
| `⊢ P (a / b)` | `⊢ P (b⁻¹ * a)` |

---

## Part 2 · `frequency_tendsto_rat` (milestone, uses Part 1)

Statement: a.s., for **every** rational `q`, `#{i < n | X i ω ≤ ↑q} / n → μ.real {ω | X 0 ω ≤ ↑q}`.

**R22 · `rw [ae_all_iff]`** changes the **goal**: for a countable index type, "a.s. for all `i`" is "for all
`i`, a.s." (a countable union of null sets is null). Statement: `[Countable ι] → ((∀ᵐ a ∂μ, ∀ i, p a i) ↔
∀ i, ∀ᵐ a ∂μ, p a i)`. `ℚ` is countable; `ℝ` is not, which is why the exercise goes through rationals.
Placeholders: `(p : Ω → ℚ → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ᵐ (ω : Ω) ∂μ, ∀ (q : ℚ), p ω q` | `⊢ ∀ (i : ℚ), ∀ᵐ (a : Ω) ∂μ, p a i` |

**R23 · `change`** changes the **goal** to a definitionally equal one. `{ω | Z ω ≤ c}` and `Z ⁻¹' Set.Iic c`
are the same set by unfolding, so Part 1 with `A = Set.Iic c` applies directly (`exact` sees through the
difference too; `rw` does not). Likewise `X i ω ∈ Set.Iic c` *is* `X i ω ≤ c`. Placeholders:
`(Z : Ω → ℝ) (c : ℝ)`.

Before, then after (`|` cannot sit in a table's code span):

```lean-goal
⊢ P (μ.real {ω | Z ω ≤ c})
⊢ P (μ.real (Z ⁻¹' Set.Iic c))
```

**R24 · `measurableSet_Iic`** **closes** `MeasurableSet (Set.Iic c)`: closed half-lines are Borel.

| Before | After |
|---|---|
| `⊢ MeasurableSet (Set.Iic c)` | no goals |

---

## Part 3 · `frequency_mono` (milestone)

Statement: `s ≤ t → #{i < n | X i ω ≤ s} / n ≤ #{i < n | X i ω ≤ t} / n`.

**R25 · `gcongr`** changes the **goal**: for a goal `f(a) ≤ f(b)` with the same "shape" `f` on both sides, it
reduces to `a ≤ b`, using monotonicity lemmas it knows. Side conditions such as `0 ≤ c` for dividing are
closed by itself (from hypotheses or by `positivity`), and so is the main goal when a hypothesis states it.
Placeholders: `(a b c : ℝ) (hc : 0 ≤ c)`.

| Before | After |
|---|---|
| `⊢ a / c ≤ b / c` | `⊢ a ≤ b` |

**R26 · `gcongr with i hi`** changes the **goal and the context**: on cardinalities of filters it goes through
the cast `↑`, `Finset.card` (a subset has fewer elements) and `Finset.filter` (a weaker predicate keeps more),
and leaves `p i → q i` for `i ∈ s`. Placeholders: `(n : ℕ) (p q : ℕ → Prop)`. In the exercise this last goal is
`X i ω ≤ s → X i ω ≤ t`, which `gcongr` closes from `hst` by itself: plain `gcongr` proves the milestone.

| Before | After |
|---|---|
| `⊢ ↑(Finset.filter p (Finset.range n)).card ≤ ↑(Finset.filter q (Finset.range n)).card` | `i : ℕ, hi : i ∈ Finset.range n ⊢ p i → q i` |

---

## Part 4 · `empirical_cdf`

Statement: a.s., for every `t` at which `F(s) = μ.real {ω | X 0 ω ≤ s}` is continuous, `Fₙ(t) → F(t)`.
Write `F t` for `μ.real {ω | X 0 ω ≤ t}` and `Fₙ(t)` for the frequency.

**R27 · `rw [tendsto_order]`** changes the **goal**: on an ordered space, `u n → L` iff every `a < L` is
eventually below `u n` and every `a > L` is eventually above. Statement: `Tendsto f x (𝓝 a) ↔ (∀ a' < a,
∀ᶠ b in x, a' < f b) ∧ ∀ a' > a, ∀ᶠ b in x, f b < a'`. Then `constructor` and `intro a ha` in each half.
Placeholders: `(u : ℕ → ℝ) (L : ℝ)`.

| Before | After |
|---|---|
| `⊢ Tendsto u atTop (𝓝 L)` | `⊢ (∀ a' < L, ∀ᶠ (b : ℕ) in atTop, a' < u b) ∧ ∀ a' > L, ∀ᶠ (b : ℕ) in atTop, u b < a'` |

**R28 · `(tendsto_order.1 hu).1 a ha`** changes the **context**: the same lemma used forwards on a hypothesis
(`.1` of an `↔` is `→`; then `.1`/`.2` pick a half of the `∧`). Use it on `hω q` (Part 2) at a rational `q`.
Placeholders: `(u : ℕ → ℝ) (L a : ℝ) (ha : a < L)`.

| Before | After `have h := (tendsto_order.1 hu).1 a ha` |
|---|---|
| `⊢ G` | `⊢ G`, context gains `h : ∀ᶠ (b : ℕ) in atTop, a < u b` |

**R29 · `lt_mem_nhds ha`** changes the **context**: a strict inequality persists near the point. Statements:
`lt_mem_nhds : a < b → ∀ᶠ x in 𝓝 b, a < x` and `gt_mem_nhds : b < a → ∀ᶠ x in 𝓝 b, x < a` (upper half).
Placeholders: `(a b : ℝ)`.

| Before | After `have h := lt_mem_nhds ha` |
|---|---|
| `ha : a < b ⊢ G` | `⊢ G`, context gains `h : ∀ᶠ (x : ℝ) in 𝓝 b, a < x` |

**R30 · `ht.eventually hev`** (`Filter.Tendsto.eventually`; `ContinuousAt F t` is a `Tendsto`) changes the
**context**: what holds near `F t` holds for `F s` with `s` near `t`. Statement: `Tendsto f l₁ l₂ →
(∀ᶠ y in l₂, p y) → ∀ᶠ x in l₁, p (f x)`. Placeholders: `(F : ℝ → ℝ) (t a : ℝ)`. Combined with R29:
`ht.eventually (lt_mem_nhds ha)`.

| Before | After `have h := ht.eventually hev` |
|---|---|
| `⊢ G`, with `hev : ∀ᶠ (y : ℝ) in 𝓝 (F t), a < y` | `⊢ G`, context gains `h : ∀ᶠ (x : ℝ) in 𝓝 t, a < F x` |

**R31 · `obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 hev`** changes the **context**: "near `x`" becomes
an explicit `δ`-ball. Statement: `(∀ᶠ y in 𝓝 x, p y) ↔ ∃ ε > 0, ∀ ⦃y⦄, dist y x < ε → p y`. Placeholders:
`(x : ℝ) (p : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ G`, with `hev : ∀ᶠ (y : ℝ) in 𝓝 x, p y` | `δ : ℝ, hδ : δ > 0 ⊢ G`, and `h : ∀ ⦃y : ℝ⦄, dist y x < δ → p y` |

**R32 · `obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hxy`** changes the **context**: `ℚ` is dense in `ℝ`.
Statement: `x < y → ∃ q : ℚ, x < ↑q ∧ ↑q < y`. Placeholders: `(x y : ℝ)`. For the lower half use
`x = t - δ, y = t`; for the upper half `x = t, y = t + δ`.

| Before | After |
|---|---|
| `hxy : x < y ⊢ G` | `q : ℚ, hq1 : x < ↑q, hq2 : ↑q < y ⊢ G` |

**R33 · `linarith`** **closes** a goal that is a linear consequence (sums and positive multiples) of
hypotheses and the goal's negation. `show t - δ < t by linarith` builds the argument for R32 inline.

| Before | After |
|---|---|
| `hδ : δ > 0 ⊢ t - δ < t` | no goals |

**R34 · `rw [Real.dist_eq]`** changes the **goal**: `dist x y = |x - y|` on `ℝ`. Placeholders: `(x y : ℝ)`.

Before, then after (`|` cannot sit in a table's code span):

```lean-goal
⊢ P (dist x y)
⊢ P |x - y|
```

**R35 · `rw [abs_sub_lt_iff]`** changes the **goal**: `|a - b| < c ↔ a - b < c ∧ b - a < c`. Then
`constructor <;> linarith`. Placeholders: `(a b c : ℝ)`.

Before, then after (`|` cannot sit in a table's code span):

```lean-goal
⊢ |a - b| < c
⊢ a - b < c ∧ b - a < c
```

**R36 · `h₁.trans_le h₂`, `h₂.trans_lt h₁`, `h.le`** **close** a chained inequality: `a < b → b ≤ c → a < c`
(`lt_of_lt_of_le`) and `a ≤ b → b < c → a < c` (`lt_of_le_of_lt`); `h.le : a ≤ b` from `h : a < b`. With
Part 3: `hn.trans_le (frequency_mono X ω n hq2.le)` lifts `a < Fₙ(q)` to `a < Fₙ(t)`.

| Before | After |
|---|---|
| `h₁ : a < b, h₂ : b ≤ c ⊢ a < c` | no goals |
| `h₂ : a ≤ b, h₁ : b < c ⊢ a < c` | no goals |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: a point of `(t - δ, t)` is in the `δ`-ball.** R34 and R35 in one `rw`, then R33 twice:

```lean-goal
⊢ dist y t < δ
⊢ y - t < δ ∧ t - y < δ
```

**W2: continuity, a strict bound, and a rational.** For `x ↦ x ^ 2` at `1` with `1 ^ 2 < 2`: R29 + R30 give
`∀ᶠ y in 𝓝 1, y ^ 2 < 2`, R31 a `δ`, R32 a rational `q ∈ (1, 1 + δ)`, and W1 shows `q` is in the ball:

```lean-goal
⊢ ∃ q, 1 < ↑q ∧ ↑q ^ 2 < 2
⊢ dist (↑q) 1 < δ
⊢ ↑q - 1 < δ ∧ 1 - ↑q < δ
```

**W3: lifting an eventual bound along `u ≤ v`.** R17 on the filter `atTop`, then R36:

```lean-goal
⊢ ∀ᶠ (n : ℕ) in atTop, a < v n
⊢ a < v n
```

---

## Traps

- `strong_law_ae` averages as `(↑n)⁻¹ • ∑ …`; the exercise has `↑#… / ↑n`. Match them pointwise with `convert …
  using 2 with n` (R19), then R15, R20, R21. With `using 1` you get an equation of functions instead.
- `rw` cannot see that `{ω | X 0 ω ≤ ↑q}` is `X 0 ⁻¹' Set.Iic ↑q`; `exact` and `change` can (R23). So apply
  Part 1 with `exact frequency_tendsto … (Set.Iic (q : ℝ)) measurableSet_Iic`, and do not try to rewrite.
- Part 1 needs `[DecidablePred (· ∈ A)]` for the filter. For `A = Set.Iic ↑q` Lean finds it from `≤` on `ℝ`,
  and the two decision procedures agree by `exact` (both are classical on `ℝ`).
- `ae_all_iff` needs a countable index: it works for `∀ q : ℚ`, not for `∀ t : ℝ`. That is the reason for the
  rationals and the squeeze.
- Write a count as `↑{i ∈ Finset.range n | p i}.card` or `↑((Finset.range n).filter p).card` in your own `have`s.
  The `#{…}` form in the docs needs `open Finset`, which the problem file does not have.
- `ContinuousAt F t` is a `Tendsto`, so `ht.eventually` works on it directly; no unfolding needed.
- In the lower half pick `q ∈ (t - δ, t)` (so `q ≤ t`, and monotonicity goes `Fₙ(q) ≤ Fₙ(t)`); in the upper
  half `q ∈ (t, t + δ)`. The `δ`-ball membership is `dist ↑q t < δ`, i.e. `|↑q - t| < δ` (W1).
- `a' > L` means `L < a'`: `gt_mem_nhds` takes exactly that (`F t < a`).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| name a term, with its equation | `set f : α → ℝ := A.indicator (fun _ => 1) with hf_def` | R1 |
| indicator is measurable | `measurable_const.indicator hA` | R2 |
| `Y 0` measurable / a.e.-strongly measurable | `(hf.comp (hmeas 0)).aestronglyMeasurable` | R3, R4 |
| bounded → integrable | `Integrable.of_bound hm 1 (Eventually.of_forall fun ω => ?_)` | R5, R6 |
| bound an indicator | `simp only [hY, hf_def, Function.comp, Set.indicator]; split_ifs <;> simp` | R7–R9 |
| pairwise independence of `f ∘ X i` | `fun i j hij => (hindep hij).comp hf hf` | R10, R11 |
| same law for `f ∘ X i` | `fun i => (hident i).comp hf` | R12 |
| `E[1_A ∘ X 0] = P(X 0 ∈ A)` | `rfl` restatement, then `rw [integral_indicator_const _ (hmeas 0 hA), smul_eq_mul, mul_one]` | R13–R15 |
| strong law | `strong_law_ae Y hint hind hid` | R16 |
| a.s. / eventually → pointwise | `filter_upwards [h] with ω hω` | R17 |
| rewrite a hypothesis | `rw [e] at h` | R18 |
| match two limits pointwise | `convert h using 2 with n` | R19 |
| sum of `if … then 1 else 0` | `Finset.sum_boole` | R20 |
| `a / b → b⁻¹ * a` | `rw [div_eq_inv_mul]` | R21 |
| a.s. for all rationals | `rw [ae_all_iff]; intro q` | R22 |
| `{ω \| Z ω ≤ c}` as a preimage | `change`, or just `exact` | R23 |
| `(-∞, c]` measurable | `measurableSet_Iic` | R24 |
| monotone frequency | `gcongr` | R25, R26 |
| limit via order | `rw [tendsto_order]; constructor` / `(tendsto_order.1 h).1 a ha` | R27, R28 |
| continuity → near `t`, `a < F s` | `ht.eventually (lt_mem_nhds ha)` (`gt_mem_nhds` above) | R29, R30 |
| near → `δ`-ball | `obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 …` | R31 |
| a rational in `(x, y)` | `obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x < y by linarith)` | R32, R33 |
| ball membership | `rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith` | R34, R35, R33 |
| chain `<` and `≤` | `hn.trans_le h`, `h.trans_lt hn`, `hq.le` | R36 |
| see the state | infoview | |
