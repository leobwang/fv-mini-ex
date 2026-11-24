# M087 · Cantelli's one-sided inequality: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `have`, `exact`, `intro`, `rw`, `simp`,
`ring`, `∀`/`∃`/`∧`, anonymous constructors `⟨_, _⟩`. Helpful but not required: M084 (Markov's
inequality, proved from scratch) and M085 (Chebyshev from Markov, which applies the same Mathlib lemma R14). **New here:**
Mathlib's measure theory and probability: probability measures, the integral `∫ ω, f ω ∂μ`,
`Integrable`, `MemLp` (finite p-th moment), `AEMeasurable`, "almost everywhere" (`0 ≤ᵐ[μ] f`),
`μ.real`, `Var[X; μ]`; the tactics `nlinarith`, `field_simp`, `positivity`.

**The maths.** Let `(Ω, μ)` be a probability space, `X : Ω → ℝ` with `E[X²] < ∞`, `m = E X`,
`v = Var X = E[(X - m)²]`, and `t > 0`. Let `A = {ω | t ≤ X ω - m}`.

1. **Shifted Markov** (`shifted_markov`). For a shift `u ≥ 0` put
   `Y = (X - m)² + 2u(X - m) + u² = (X - m + u)² ≥ 0`. By linearity and `E[X - m] = 0`,
   `E Y = v + u²`. On `A`, `X - m + u ≥ t + u ≥ 0`, so `Y ≥ (t + u)²`; hence
   `A ⊆ {Y ≥ (t + u)²}`. Markov's inequality `ε P(Y ≥ ε) ≤ E Y` at `ε = (t + u)²` gives
   `P(A) (t + u)² ≤ v + u²`.
2. **Optimise** (`cantelli`). `P(A) ≤ (v + u²)/(t + u)²` is smallest at `u = v/t`, where
   `(t + v/t)² = (v + t²)²/t²` and `v + (v/t)² = v(v + t²)/t²`. Cancel `t²`:
   `P(A)(v + t²)² ≤ v(v + t²)`, and divide by `v + t² > 0`: `P(A) ≤ v/(v + t²)`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`apply`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. `G : Prop` with `h : T → G` is a goal the entry does not touch; `h` only shows
  which fact `T` the step added.
- Placeholders are written as Lean binders. `{Ω : Type}` is any type (the sample space).
  `[MeasurableSpace Ω]` says `Ω` carries a σ-algebra (the events); `(μ : Measure Ω)` is a measure on it;
  `[IsProbabilityMeasure μ]` says `μ Ω = 1` (it implies `IsFiniteMeasure μ`, which several lemmas ask
  for). A bracket `[…]` is a requirement Lean finds by itself (a *type class*).
- When a new hypothesis contains `, ` (an integral) or `|` (a set), the cell says "context gains" in words.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `μ[X]` (in the source) | the expectation `E X = ∫ ω, X ω ∂μ`; the infoview prints it as `∫ (x : Ω), X x ∂μ` |
| `∫ (ω : Ω), f ω ∂μ` | the (Bochner) integral of `f : Ω → ℝ` against `μ`; it is `0` if `f` is not integrable |
| `Var[X; μ]` | `ProbabilityTheory.variance X μ`, the variance `E[(X - E X)²]` (R4) |
| `μ.real s` | `μ s` as a real number: `P(s)` for a probability measure (`μ s` itself lives in `[0, ∞]`) |
| `{ω \| Q ω}` | the set (event) of `ω` with `Q ω`; `ω ∈ {ω \| Q ω}` simplifies to `Q ω` (R20) |
| `s ⊆ t` | set inclusion, by definition `∀ ω, ω ∈ s → ω ∈ t` (R19) |
| `Integrable f μ` | `f` is measurable (a.e. strongly) and `∫ ‖f‖ ∂μ < ∞`, i.e. `f ∈ L¹(μ)` |
| `MemLp f 2 μ` | `f ∈ L²(μ)`: `E[f²] < ∞` (the `2` is an extended real `ℝ≥0∞`) |
| `AEMeasurable f μ` | `f` agrees `μ`-a.e. with a measurable function (R3) |
| `0 ≤ᵐ[μ] f` | `0 ≤ f ω` for `μ`-almost every `ω` (outside a null set) |
| `0 x` | the zero function `0 : Ω → ℝ` applied to `x`; it is the number `0` (R15) |
| `f - fun x => c` | the function `ω ↦ f ω - c` written as a difference of functions (R5) |
| `inst✝ : …` | an unnamed type-class hypothesis (`[MeasurableSpace Ω]` etc.) |
| `Ω : Type u_1` | the spec's `{Ω : Type*}`: `Ω` is a type in an arbitrary universe `u_1` (treat it as `Type`) |
| `Measure Ω`, `IsProbabilityMeasure μ` | `μ` is a measure on the σ-algebra `[MeasurableSpace Ω]`, and `μ Ω = 1` |
| `(fun ω => e) ω` | a lambda applied to `ω`: it means `e`; `show` with the plain form restates it (R15) |
| `2 * u * (X ω - m)` | how Lean prints `(2 * u) * (X ω - m)` (`*` groups to the left) |

---

## Part 1 · `shifted_markov` (milestone)

Statement: for `u ≥ 0`, `μ.real {ω | t ≤ X ω - μ[X]} * (t + u) ^ 2 ≤ Var[X; μ] + u ^ 2`. Prove it first:
`cantelli` applies it once, at `u = Var[X; μ] / t`. Plan: name the mean (R1) and collect facts (R2–R4);
prove the four integrability facts for `Y` (R5–R9); compute `∫ Y` (R10–R13); apply Markov (R14–R17); put `∫ Y`
into Markov's bound (R18); compare the events (R19–R21).

### Naming terms and integrability facts

**R1 · `obtain ⟨m, hm⟩ : ∃ m, e = m := ⟨_, rfl⟩`** changes the **context**: it introduces a variable `m`
and the equation `hm : e = m`, for any term `e`. The proof `⟨_, rfl⟩` takes `m := e`. Use it to give the big
term `μ[X]` a short name, then `rw [hm]` replaces it in the goal. Placeholders: `(f : Ω → ℝ)`, `e := μ[f]`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : Ω), f x ∂μ)` | `⊢ P (∫ (x : Ω), f x ∂μ)`, context gains `m : ℝ` and `hm : ∫ (x : Ω), f x ∂μ = m` |

**R2 · `hf.integrable one_le_two`** changes the **context**. `MemLp.integrable : 1 ≤ p → MemLp f p μ →
Integrable f μ` on a finite measure (`L² ⊆ L¹` when `μ Ω < ∞`). Placeholders: `[IsProbabilityMeasure μ]
(f : Ω → ℝ) (hf : MemLp f 2 μ)`.

| Before | After |
|---|---|
| `⊢ G` | `hi : Integrable f μ ⊢ G` |

**R3 · `hf.aemeasurable`** changes the **context**. `MemLp.aemeasurable : MemLp f p μ → AEMeasurable f μ`.
Placeholders: `(f : Ω → ℝ) (hf : MemLp f 2 μ)`.

| Before | After |
|---|---|
| `⊢ G` | `hm : AEMeasurable f μ ⊢ G` |

**R4 · `rw [variance_eq_integral hf]`** changes the **goal**. Lemma: `AEMeasurable X μ →
Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ`. In the milestone, state the fact `hvar` with `m` and prove it by
`rw [variance_eq_integral hX.aemeasurable, hm]` (R3 inline). Placeholders: `(f : Ω → ℝ)
(hf : AEMeasurable f μ)`.

| Before | After |
|---|---|
| `⊢ P Var[f; μ]` | `⊢ P (∫ (ω : Ω), (f ω - ∫ (x : Ω), f x ∂μ) ^ 2 ∂μ)` |

**R5 · `hf.sub (memLp_const c)`** changes the **context**. `memLp_const c : MemLp (fun _ => c) p μ` (finite
measure); `MemLp.sub : MemLp f p μ → MemLp g p μ → MemLp (f - g) p μ`. Placeholders:
`[IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : MemLp f 2 μ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hs : MemLp (f - fun x => c) 2 μ ⊢ G` |

**R6 · `hs.integrable_sq`** changes the **context**. `MemLp.integrable_sq : MemLp g 2 μ →
Integrable (fun x => g x ^ 2) μ`. With `g = f - fun _ => c` the raw type is
`Integrable (fun x => (f - fun x => c) x ^ 2) μ`; writing the type in the `have` restates it in lambda
form (the two are equal by unfolding). Chain: `(hX.sub (memLp_const _)).integrable_sq` (R5 then R6).
Placeholders: `(f : Ω → ℝ) (c : ℝ) (hs : MemLp (f - fun _ => c) 2 μ)`.

| Before | After |
|---|---|
| `⊢ G` | `h2 : Integrable (fun ω => (f ω - c) ^ 2) μ ⊢ G` |

**R7 · `integrable_const c`** changes the **context**: a constant is integrable on a finite measure.
Usually written `integrable_const _` inside a bigger term, where Lean infers `μ`. Placeholders:
`[IsProbabilityMeasure μ] (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hc : Integrable (fun x => c) μ ⊢ G` |

**R8 · `hf.sub hg`** (and `hf.add hg`) changes the **context**. `Integrable.sub : Integrable f μ →
Integrable g μ → Integrable (f - g) μ`; `Integrable.add` is the same with `+`. State the type in lambda form
(`fun ω => f ω - g ω`), as `rw [integral_add …]` needs it (Traps). Placeholders: `(f g : Ω → ℝ)
(hf : Integrable f μ) (hg : Integrable g μ)`.

| Before | After |
|---|---|
| `⊢ G` | `hs : Integrable (fun ω => f ω - g ω) μ ⊢ G` |

**R9 · `hf.const_mul c`** changes the **context**. `Integrable.const_mul : Integrable f μ → ∀ c,
Integrable (fun x => c * f x) μ`. Placeholders: `(f : Ω → ℝ) (hf : Integrable f μ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hc : Integrable (fun x => c * f x) μ ⊢ G` |

### Computing `∫ Y`

**R10 · `rw [integral_add hf hg]`** changes the **goal**. Lemma `integral_add : Integrable f μ →
Integrable g μ → ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ`. `+` groups to the left, so
`A + B + C` is `(A + B) + C`: the first `rw` splits off `C` (with `hf` about `A + B`), the second splits
`A + B`. Placeholders: `(f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (ω : Ω), f ω + g ω ∂μ)` | `⊢ P (∫ (a : Ω), f a ∂μ + ∫ (a : Ω), g a ∂μ)` |

**R11 · `rw [integral_const_mul]`** changes the **goal**. Lemma: `∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ` (no
integrability needed). Placeholders: `(f : Ω → ℝ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (ω : Ω), c * f ω ∂μ)` | `⊢ P (c * ∫ (a : Ω), f a ∂μ)` |

**R12 · `rw [integral_sub hf hg]`** changes the **goal**. Lemma `integral_sub`: as R10 with `-`. In the
milestone `g` is the constant `m`, so `hg` is `integrable_const _` (R7). After it, `∫ X` is back as
`∫ (a : Ω), X a ∂μ`: `rw [hm]` once more turns it into `m`. Placeholders: as R10.

| Before | After |
|---|---|
| `⊢ P (∫ (ω : Ω), f ω - g ω ∂μ)` | `⊢ P (∫ (a : Ω), f a ∂μ - ∫ (a : Ω), g a ∂μ)` |

**R13 · `simp`** on the integral of a constant changes the **goal**: `∫ ω, c ∂μ` becomes `c` for a
probability measure (`simp` uses `integral_const : ∫ x, c ∂μ = μ.real univ • c` and `μ.real univ = 1`). In
the milestone it also simplifies `m - m` to `0` and closes `hE`. Placeholders: `[IsProbabilityMeasure μ]
(c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (_ω : Ω), c ∂μ)` | `⊢ P c` |

### Markov's inequality

**R14 · `mul_meas_ge_le_integral_of_nonneg hnn hfi ε`** changes the **context**. This is Markov's
inequality: `0 ≤ᵐ[μ] f → Integrable f μ → ∀ ε : ℝ, ε * μ.real {x | ε ≤ f x} ≤ ∫ x, f x ∂μ`. Take
`f = Y` (its integrability is the fourth `have`) and `ε = (t + u) ^ 2`. Placeholders: `(f : Ω → ℝ)
(hnn : 0 ≤ᵐ[μ] f) (hfi : Integrable f μ) (ε : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, context gains `hmk : ε * μ.real {x \| ε ≤ f x} ≤ ∫ (x : Ω), f x ∂μ` |

**R15 · `Filter.Eventually.of_forall`** changes the **goal**: what holds everywhere holds almost everywhere.
Lemma: `(∀ x, p x) → ∀ᶠ x in l, p x`, where `∀ᶠ x in l, p x` reads "`p x` holds eventually along the filter `l`"; for `l = ae μ` (the filter of `μ`-almost-everywhere sets) that is "`p x` for `μ`-a.e. `x`", and `0 ≤ᵐ[μ] f` is notation for `∀ᶠ x in ae μ, 0 x ≤ f x`. As a term, `Filter.Eventually.of_forall fun ω => ?_`. The new goal
reads `0 x ≤ f x`, with the zero *function*; in the milestone `f` is a `fun`, so restate the goal with
`show (0 : ℝ) ≤ … by …` before proving it. Placeholders: `(f : Ω → ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ᵐ[μ] f` | `⊢ ∀ (x : Ω), 0 x ≤ f x` |

**R16 · `sq_nonneg a`** changes the **context**: `0 ≤ a ^ 2`. Mostly used as a hint inside
`nlinarith [sq_nonneg (…)]` (R17). Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hsq : 0 ≤ a ^ 2 ⊢ G` |

**R17 · `nlinarith [t₁, …]`** **closes** a goal that follows from the hypotheses and the hint terms `tᵢ`
by linear arithmetic after multiplying pairs of them (`linarith` alone does not multiply). It treats
`μ.real {…}`, `Var[X; μ]` and integrals as unknown numbers. Typical hints: `sq_nonneg (…)` (R16), a
fact such as R21's. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ x ^ 2 - 2 * x * y + y ^ 2` | closed by `nlinarith [sq_nonneg (x - y)]` |

### Comparing the events

**R18 · `rw [e] at h ⊢`** changes the **context and the goal**: `at h` rewrites the hypothesis `h`, `⊢`
the goal; `at h` alone leaves the goal untouched. Use `rw [hE] at hmk` to put `Var[X; μ] + u ^ 2` into
Markov's bound. Placeholders: `(a b : ℝ) (e : a = b)`.

| Before | After |
|---|---|
| `h : P a ⊢ Q a` | `h : P b ⊢ Q b` |

**R19 · `intro ω hω`** on `s ⊆ t` changes the **goal and the context**: `⊆` unfolds to
`∀ ω, ω ∈ s → ω ∈ t`, so `intro` works directly. Placeholders: `{Ω : Type} (s t : Set Ω)`.

| Before | After |
|---|---|
| `⊢ s ⊆ t` | `ω : Ω, hω : ω ∈ s ⊢ ω ∈ t` |

**R20 · `simp only [Set.mem_setOf_eq] at hω ⊢`** changes the **context and the goal**. Lemma
`Set.mem_setOf_eq : (a ∈ {x | p x}) = p a`. Placeholders: `(Q R : Ω → Prop) (ω : Ω)`. The hypothesis
`hω : ω ∈ {x | Q x}` becomes `hω : Q ω`, and the goal:

```lean-goal
⊢ ω ∈ {x | R x}
⊢ R ω
```

**R21 · `measureReal_mono (μ := μ) hst`** changes the **context**. Lemma: `s₁ ⊆ s₂ → μ.real s₁ ≤ μ.real s₂`
(its second argument `μ s₂ ≠ ∞` is filled in automatically for a finite measure). `μ` does not occur in
`hst`, so pass it by name. Pass the result straight to `nlinarith` as a hint. Placeholders:
`[IsProbabilityMeasure μ] (s t : Set Ω) (hst : s ⊆ t)`.

| Before | After |
|---|---|
| `⊢ G` | `hle : μ.real s ≤ μ.real t ⊢ G` |

The last step of the milestone: `hmk` says `(t + u)² · P(Y ≥ (t + u)²) ≤ v + u²`, R21 says
`P(A) ≤ P(Y ≥ (t + u)²)`; multiplying the second by `(t + u)² ≥ 0` is the product `nlinarith` needs, so give
it R21's fact and `sq_nonneg (t + u)`.

---

## Part 2 · `cantelli`

Statement: `μ.real {ω | t ≤ X ω - μ[X]} ≤ Var[X; μ] / (Var[X; μ] + t ^ 2)`. Apply the milestone at
`u = Var[X; μ] / t` (R22–R24), name the variance `v` (R1, R25, R18), simplify the bound (R26–R29), clear
the goal's denominator (R30) and finish (R17).

**R22 · `variance_nonneg X μ`** changes the **context**: `0 ≤ Var[X; μ]`, with no hypotheses. Placeholders:
`(f : Ω → ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hv : 0 ≤ Var[f; μ] ⊢ G` |

**R23 · `ht.le`** changes the **context**. `LT.lt.le : a < b → a ≤ b`, written with dot notation on
`ht : 0 < t`. Placeholders: `(t : ℝ) (ht : 0 < t)`.

| Before | After |
|---|---|
| `ht : 0 < t ⊢ G` | `ht' : 0 ≤ t ⊢ G` |

**R24 · `div_nonneg`** changes the **goal list**. Lemma: `0 ≤ a → 0 ≤ b → 0 ≤ a / b`. As a term
`div_nonneg ha hb`; with R22 and R23 it proves the milestone's `0 ≤ u` at `u = Var[X; μ] / t`.
Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ a / b` | `⊢ 0 ≤ a`, `⊢ 0 ≤ b` |

**R25 · `e ▸ t`** changes the **context**: it rewrites the *type* of the proof `t` with `e : a = b` (in
whichever direction makes it fit the stated type). `have hv0 : 0 ≤ v := hv ▸ variance_nonneg X μ` turns R22's
fact into one about `v`. Placeholders: `(a b : ℝ) (e : a = b) (ha : 0 ≤ a)`.

| Before | After |
|---|---|
| `e : a = b, ha : 0 ≤ a ⊢ G` | `hb : 0 ≤ b ⊢ G` |

**R26 · `field_simp`** changes the **goal**: it multiplies out every denominator it can prove nonzero (it
finds `0 < a` in the context) and normalises both sides, often leaving an equation `ring` closes. Use it for
the two facts `e1 : (t + v / t) ^ 2 = (v + t ^ 2) ^ 2 / t ^ 2` and `e2 : v + (v / t) ^ 2 = v * (v + t ^ 2) / t ^ 2`:
`field_simp`, then `ring`. Placeholders: `(a b : ℝ) (ha : 0 < a)`.

| Before | After |
|---|---|
| `ha : 0 < a ⊢ (a + b / a) * 2 = (2 * b + 2 * a ^ 2) / a` | `⊢ a ^ 2 + b = b + a ^ 2` |

**R27 · `rw [mul_div_assoc']`** changes the **goal** (or, `at hk`, a hypothesis). Lemma:
`a * (b / c) = a * b / c`. After `rw [e1, e2] at hk` the left side is `P(A) * ((v + t²)² / t²)`; this puts both
sides over `t ^ 2`. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a * (b / c))` | `⊢ P (a * b / c)` |

**R28 · `rw [div_le_div_iff_of_pos_right hc] at h`** changes the **context**. Lemma:
`0 < c → (a / c ≤ b / c ↔ a ≤ b)`; `rw` with an `↔` replaces the left statement by the right. Write the
positivity argument inline: `div_le_div_iff_of_pos_right (by positivity)` (R29). Placeholders:
`(a b c : ℝ) (hc : 0 < c)`.

| Before | After |
|---|---|
| `h : a / c ≤ b / c ⊢ a ≤ b` | `h : a ≤ b ⊢ a ≤ b` |

**R29 · `positivity`** **closes** a goal `0 < e` or `0 ≤ e` when `e` is built from `+`, `*`, `^`, `/` and
atoms it can see are positive or nonnegative (from hypotheses such as `0 < t`, `0 ≤ v`, or squares). It
proves `0 < t ^ 2` and `0 < v + t ^ 2` here. Placeholders: `(a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)`.

| Before | After |
|---|---|
| `⊢ 0 < b + 2 * a ^ 2` | closed |

**R30 · `rw [le_div_iff₀ hc]`** changes the **goal**. Lemma: `0 < c → (a ≤ b / c ↔ a * c ≤ b)`.
Placeholders: `(a b c : ℝ) (hc : 0 < c)`. After it, the goal `P(A) * (v + t²) ≤ v` follows from
`hk : P(A) * (v + t²)² ≤ v * (v + t²)` and `v + t² > 0` by `nlinarith` (R17).

| Before | After |
|---|---|
| `⊢ a ≤ b / c` | `⊢ a * c ≤ b` |

### Worked combinations (W1–W3, on statements that are not the exercise's)

**W1: Markov on `f ²`** (a Chebyshev-type step): `c · P(c ≤ f²) ≤ E[f²]` for `f ∈ L²`. R6 gives the
integrability, R15 with `show (0 : ℝ) ≤ f ω ^ 2 from sq_nonneg (f ω)` (R16) the a.e. bound, and R14 closes:

```lean-goal
⊢ c * μ.real {x | c ≤ f x ^ 2} ≤ ∫ (x : Ω), f x ^ 2 ∂μ
```

**W2: a centred variable has mean zero**, `∫ ω, (f ω - μ[f]) ∂μ = 0`. R1, R2, then `rw [hm, integral_sub …]`
(R12 with R7), then `rw [hm]` again (the mean came back), and R13:

```lean-goal
⊢ ∫ (ω : Ω), f ω - ∫ (x : Ω), f x ∂μ ∂μ = 0
⊢ ∫ (a : Ω), f a ∂μ - ∫ (a : Ω), m ∂μ = 0
⊢ m - ∫ (a : Ω), m ∂μ = 0
```

**W3: cancel a common denominator, then clear another.** From
`h : p * ((a + 1) ^ 2 / a ^ 2) ≤ b * (a + 1) / a ^ 2` with `0 < a`: `rw [R27, R28 (by positivity)] at h` gives
`h : p * (a + 1) ^ 2 ≤ b * (a + 1)`; `rw [R30 (by positivity)]` and `nlinarith` (R17):

```lean-goal
⊢ p ≤ b / (a + 1)
⊢ p * (a + 1) ≤ b
```

---

## Traps

- **Lambda form for `integral_add` / `integral_sub`** (R10, R12). `rw [integral_add hf hg]` finds
  `∫ ω, F ω + G ω ∂μ` only when `hf`, `hg` are stated as `Integrable (fun ω => F ω) μ` and
  `Integrable (fun ω => G ω) μ` with exactly the summands of the integrand. A fact about `f - g` or
  `fun x => (f - fun x => c) x ^ 2` is the same function but not the same text; state each `have` with an
  explicit lambda type (R6, R8).
- **Write `Y` the same way everywhere**: `(X ω - m) ^ 2 + (2 * u) * (X ω - m) + u ^ 2`, grouped as
  `(A + B) + C`. The integrability facts, `hE`, Markov's set and `hsub` must all match it literally.
  The infoview prints `(2 * u) * (X ω - m)` as `2 * u * (X ω - m)`; both are the same term.
- **`μ[X]` comes back.** `obtain` plus `rw [hm]` removes `μ[X]` from the goal, but `integral_sub` produces
  `∫ (a : Ω), X a ∂μ` again; rewrite with `hm` once more (W2).
- **`0 x ≤ f x`** after R15 is the zero function applied to `x`; `nlinarith` may not see through it or
  through `(fun ω => …) ω`. State the pointwise fact with `show (0 : ℝ) ≤ … by …`.
- `measureReal_mono hsub` cannot infer `μ`: write `measureReal_mono (μ := μ) hsub`.
- Name the variance (`obtain ⟨v, hv⟩ : ∃ v, Var[X; μ] = v := ⟨_, rfl⟩`) before `field_simp`/`nlinarith`,
  so they treat it as one number, and keep `hv0 : 0 ≤ v` in the context for `positivity`.
- A `have` proved inside one theorem is not visible in another.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| name a big term | `obtain ⟨m, hm⟩ : ∃ m, μ[X] = m := ⟨_, rfl⟩` | R1 |
| `Integrable X μ` from `MemLp X 2 μ` | `hX.integrable one_le_two` | R2 |
| `Var` as an integral | `rw [variance_eq_integral hX.aemeasurable]` | R3, R4 |
| `(X - m)²` integrable | `(hX.sub (memLp_const _)).integrable_sq` | R5, R6 |
| constant, difference, sum, `c * f` integrable | `integrable_const _`, `hf.sub hg`, `hf.add hg`, `hf.const_mul c` | R7–R9 |
| split `∫ (f + g)`, `∫ (f - g)` | `rw [integral_add hf hg]`, `rw [integral_sub hf hg]` | R10, R12 |
| `∫ c * f` | `rw [integral_const_mul]` | R11 |
| `∫ c` (probability) | `simp` | R13 |
| Markov `ε P(ε ≤ f) ≤ E f` | `mul_meas_ge_le_integral_of_nonneg hnn hfi ε` | R14 |
| a.e. from everywhere | `Filter.Eventually.of_forall fun ω => show (0 : ℝ) ≤ … by …` | R15 |
| `0 ≤ a ^ 2` | `sq_nonneg a` | R16 |
| nonlinear finish | `nlinarith [hints]` | R17 |
| rewrite a hypothesis (add ⊢ for the goal too) | `rw [e] at h` | R18 |
| prove `s ⊆ t` | `intro ω hω`, then `simp only [Set.mem_setOf_eq] at hω` and ⊢ | R19, R20 |
| `P(s) ≤ P(t)` from `s ⊆ t` | `measureReal_mono (μ := μ) hst` | R21 |
| `0 ≤ Var`, `0 ≤ t`, `0 ≤ a / b` | `variance_nonneg X μ`, `ht.le`, `div_nonneg ha hb` | R22–R24 |
| move a fact along `e : a = b` | `e ▸ fact` | R25 |
| clear denominators in an equation | `field_simp; ring` | R26 |
| `a * (b / c) → a * b / c` | `rw [mul_div_assoc']` | R27 |
| cancel `/ c` on both sides | `rw [div_le_div_iff_of_pos_right (by positivity)] at h` | R28 |
| `0 < e` | `positivity` | R29 |
| `a ≤ b / c → a * c ≤ b` | `rw [le_div_iff₀ hc]` | R30 |
| see the state | infoview | |
