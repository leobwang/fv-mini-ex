# M092 · Unbiased sample variance: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's measure-theoretic probability
(probability measures, expectation as an integral, variance, `L²`, independence), finite sums over
`Finset`, and casts `ℕ → ℝ`.

The math. Let `X 0, …, X (n-1)` be real random variables on a sample space `Ω` with probability
measure `μ`, all with mean `m = E[X i]` and variance `σ² = Var X i = E[X i²] − m²`, pairwise
independent. Write `S = ∑ i < n, X i` and `X̄ = S / n`. Then pointwise

  `∑ (X i − X̄)² = ∑ X i² − S² / n`,

`E[X i²] = σ² + m²`, `E[S] = n m`, `Var S = n σ²` (independence), so `E[S²] = n σ² + n² m²` and

  `E[∑ (X i − X̄)²] = n (σ² + m²) − (n σ² + n² m²) / n = (n − 1) σ²`.

Dividing by `n − 1` gives `σ²`. In Lean `σ²` is the variable `σ2`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal.
- `G : Prop` is an arbitrary goal and `k : … → G` only consumes the new hypothesis; such entries
  change the **context** (a new `h`), and the goal stays `⊢ G`.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[CommRing α]`
  is a requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Ω : Type u_1`, `[MeasurableSpace Ω]` | the sample space, with its σ-algebra of events (`Type*` in the source becomes `Type u_1`) |
| `μ : Measure Ω`, `[IsProbabilityMeasure μ]` | a measure on `Ω` with `μ Ω = 1`: a probability distribution |
| `X : ℕ → Ω → ℝ` | a sequence of real random variables; `X i ω` is the value of the `i`-th one at outcome `ω` |
| `μ[F]` (in the source) | the expectation `E[F] = ∫ F dμ`. The infoview prints it as `∫ (x : Ω), F x ∂μ` |
| `∫ (x : Ω), f x ∂μ` | the Lebesgue integral of `f` against `μ` (`MeasureTheory.integral`); `0` if `f` is not integrable |
| `Var[Y; μ]` | the variance `E[(Y − E[Y])²]` (`ProbabilityTheory.variance`) |
| `MemLp Y 2 μ` | `Y` is in `L²(μ)`: measurable (a.e.) with `E[Y²] < ∞` |
| `Integrable f μ` | `f` is measurable (a.e.) and `∫ |f| dμ < ∞` (so `∫` is not the junk value `0`) |
| `Y i ⟂ᵢ[μ] Y j` | `Y i` and `Y j` are independent under `μ` (`ProbabilityTheory.IndepFun`) |
| `Pairwise r` | `∀ i j, i ≠ j → r i j` |
| `(↑s).Pairwise r` | `Set.Pairwise`: `∀ i ∈ s, ∀ j ∈ s, i ≠ j → r i j` (`↑s` is the finset `s` viewed as a set) |
| `Finset.range n` | the finite set `{0, 1, …, n-1}` |
| `∑ i ∈ s, f i` | the finite sum over `s` (`Finset.sum`); the bound name may be printed as `x`, `x_1`, `c`, `a` |
| `∑ i ∈ s, Y i` with `Y i : Ω → ℝ` | a sum of functions: itself a function `Ω → ℝ` |
| `(Finset.range k).card` | the number of elements of a finset, here `k` |
| `k • c` | `c + … + c` (`k` times; `nsmul`) |
| `↑n` | the natural number `n` cast into `ℝ` (`Nat.cast`) |
| `Y ^ 2`, `(Y ^ 2) x` | the function `ω ↦ Y ω ^ 2` (powers of functions are pointwise), applied to `x` |
| `(fun ω => X i ω ^ 2) x` | a lambda applied but not yet β-reduced; it means `X i x ^ 2` |
| `S : Ω → ℝ := …` | a local definition made by `set` (R13): `S` abbreviates the right side |
| `inst✝ : …`, `a✝ : …` | an anonymous instance or hypothesis (no name you can use) |
| `case hf`, `case hg` | a side goal left by `rw` with a lemma that needs `Integrable f μ` (`hf`) or `Integrable g μ` (`hg`) |

---

## Part 1 · `sample_var_unbiased`

Statement: for `n ≥ 2` (`hn : 1 < n`), `X i ∈ L²` (`hL2`), pairwise independent (`hindep`), with
`E[X i] = m` (`hmean`) and `Var X i = σ2` (`hvar`): `μ[sampleVar n X] = σ2`. The entries below are
grouped in the order the SKELETON uses them.

### Facts about `n`

**R1 · `omega`** **closes** a goal of linear arithmetic over `ℕ` or `ℤ` (with `+`, `-`, `<`, `≤`,
constants), using the hypotheses. Placeholders: `(k : ℕ) (hk : 1 < k)`.

| Before | After |
|---|---|
| `hk : 1 < k ⊢ 0 < k` | closed |

**R2 · `positivity`** **closes** a goal `0 < e`, `0 ≤ e` or `e ≠ 0` by looking at how `e` is built;
for an atom such as `k` it looks for `0 < k` in the context. Placeholders: `(k : ℕ) (hk : 0 < k)`.

| Before | After |
|---|---|
| `hk : 0 < k ⊢ ↑k ≠ 0` | closed |

**R3 · `exact_mod_cast hk`** **closes** a goal that is `hk` up to casts: `(1 : ℝ) < ↑k` from
`hk : 1 < k` in `ℕ`. Placeholders: `(k : ℕ)`.

| Before | After |
|---|---|
| `hk : 1 < k ⊢ 1 < ↑k` | closed |

**R4 · `linarith`** **closes** a linear (in)equality over an ordered field such as `ℝ` that follows
from the hypotheses by adding them with nonnegative coefficients. A goal `t ≠ s` is closed when one of
`t < s`, `t > s` follows (here `b = a - 1 > 0`). Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `h : 1 < a, e : b = a - 1 ⊢ b ≠ 0` | closed |

### The algebra: milestone `key`

`key` is stated for an arbitrary `x : ℕ → ℝ` (plain reals, no probability). One `simp only` with
R5–R10 expands it; then R11 and R12 finish.

**R5 · `sub_sq`** changes the **goal**: `(a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2`. Placeholders:
`{α : Type} [CommRing α] (a b : α)`; `ℝ`, `ℤ`, `ℂ` are commutative rings.

| Before | After |
|---|---|
| `⊢ P ((a - b) ^ 2)` | `⊢ P (a ^ 2 - 2 * a * b + b ^ 2)` |

**R6 · `Finset.sum_add_distrib`** changes the **goal**: `∑ i ∈ s, (f i + g i) = ∑ i ∈ s, f i + ∑ i ∈ s, g i`.
Placeholders: `{β : Type} [AddCommMonoid β] (s : Finset ℕ) (f g : ℕ → β)` (β has a commutative `+`
with `0`; `ℝ` and functions `Ω → ℝ` qualify).

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ s, (f i + g i))` | `⊢ P (∑ x ∈ s, f x + ∑ x ∈ s, g x)` |

**R7 · `Finset.sum_sub_distrib`** changes the **goal**: the same for `-`. Placeholders:
`{β : Type} [AddCommGroup β]` (also has `-`; `ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ s, (f i - g i))` | `⊢ P (∑ x ∈ s, f x - ∑ x ∈ s, g x)` |

**R8 · `rw [← Finset.sum_mul]`** changes the **goal**. The lemma is
`Finset.sum_mul : (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a`; right to left it pulls a factor that does
not depend on `i`, on the right, out of the sum. Placeholders: `(s : Finset ℕ) (f : ℕ → ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ s, f i * a)` | `⊢ P ((∑ i ∈ s, f i) * a)` |

**R9 · `rw [← Finset.mul_sum]`** changes the **goal**. The lemma is
`Finset.mul_sum : a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`; right to left it pulls a left factor out.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ s, a * f i)` | `⊢ P (a * ∑ i ∈ s, f i)` |

**R10 · `Finset.sum_const`, `Finset.card_range`, `nsmul_eq_mul`** change the **goal**: a sum of `k`
copies of a term `c` that does not depend on the index becomes `↑k * c`. The lemmas:
`∑ _x ∈ s, c = s.card • c`, `(Finset.range k).card = k`, `k • c = ↑k * c`. Placeholders:
`(k : ℕ) (c : ℝ)`. `simp [hc]` with `hc : ∀ i, f i = c` does all three after rewriting `f i` to `c`.

| Before | After `Finset.sum_const` | After `Finset.card_range` | After `nsmul_eq_mul` |
|---|---|---|---|
| `⊢ P (∑ _i ∈ Finset.range k, c)` | `⊢ P ((Finset.range k).card • c)` | `⊢ P (k • c)` | `⊢ P (↑k * c)` |

**R11 · `field_simp`** changes the **goal**: an equation with divisions becomes one without, by
multiplying through by the denominators. It needs a proof that each denominator is `≠ 0` in the
context (`hn' : (n : ℝ) ≠ 0` for `/ ↑n`, `hn1` for `/ (↑n - 1)`). The result is normalized in its own
way (here `b * c` became `c * b`), so finish with `ring`. Placeholders: `(a b c d : ℝ) (hc : c ≠ 0)`.

| Before | After |
|---|---|
| `hc : c ≠ 0 ⊢ a / c + b = d` | `⊢ a + c * b = c * d` |

**R12 · `ring`** **closes** an equation that holds in every commutative ring; sums `∑ …` and `↑n` are
treated as unknowns.

| Before | After |
|---|---|
| `⊢ (a + b) ^ 2 - 2 * a * b = a ^ 2 + b ^ 2` | closed |

**W1 (squares around a fixed `c`).** The `simp only` with R5–R10 turns the first line into the second;
`ring` closes it. `key` is the same with `c` replaced by the mean `(∑ j, x j) / n`, plus R11 for the
`/ n`.

```lean-goal
⊢ ∑ i ∈ Finset.range k, (x i - c) ^ 2 = ∑ i ∈ Finset.range k, x i ^ 2 - 2 * c * ∑ i ∈ Finset.range k, x i + ↑k * c ^ 2
⊢ ∑ x_1 ∈ Finset.range k, x x_1 ^ 2 - (2 * ∑ i ∈ Finset.range k, x i) * c + ↑k * c ^ 2 = ∑ i ∈ Finset.range k, x i ^ 2 - 2 * c * ∑ i ∈ Finset.range k, x i + ↑k * c ^ 2
```

### Naming the sum, and the pointwise form of `sampleVar` (milestone `e`)

**R13 · `set Z : Ω → ℝ := e with hZ`** changes the **context and the goal**: it adds a local
definition `Z : Ω → ℝ := e` and `hZ : Z = e`, and replaces every `e` in the goal and the context by
`Z`. Placeholders: `{Ω : Type} (s : Finset ℕ) (Y : ℕ → Ω → ℝ)`, `e` is `∑ i ∈ s, Y i`.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ s, Y i)` | `⊢ P Z`, with `Z : Ω → ℝ := ∑ i ∈ s, Y i` and `hZ : Z = ∑ i ∈ s, Y i` added |

**R14 · `memLp_finsetSum'`** changes the **context**: `memLp_finsetSum' s hL : MemLp (∑ i ∈ s, Y i) 2 μ`
from `hL : ∀ i ∈ s, MemLp (Y i) 2 μ`. A finite sum of `L²` functions is `L²`. Placeholders:
`{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s : Finset ℕ) (Y : ℕ → Ω → ℝ)`. With
`hL2 : ∀ i, MemLp (X i) 2 μ`, pass `fun i _ => hL2 i`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, with `h : MemLp (∑ i ∈ s, Y i) 2 μ` added |

**R15 · `Finset.sum_apply`** changes the **goal**: `(∑ i ∈ s, g i) ω = ∑ i ∈ s, g i ω`. A sum of
functions, applied to `ω`, is the sum of the values. Placeholders: `(s : Finset ℕ) (g : ℕ → Ω → ℝ) (ω : Ω)`.

| Before | After |
|---|---|
| `⊢ P ((∑ i ∈ s, g i) ω)` | `⊢ P (∑ c ∈ s, g c ω)` |

**R16 · `funext ω`** changes the **goal and the context**: an equation of functions becomes the
equation of their values at a new `ω`. Placeholders: `(f g : Ω → ℝ)`.

| Before | After |
|---|---|
| `⊢ f = g` | `ω : Ω ⊢ f ω = g ω` |

For `hSapp : ∀ ω, S ω = ∑ i ∈ range n, X i ω`: after `intro ω` the goal is `⊢ S ω = …`, and R15 can
fire only once `S` is replaced by its definition, so write `simp only [hS, Finset.sum_apply]` (see Traps).

For `e`: after `funext ω`, `simp only [sampleVar, sampleMean, hSapp]` unfolds the two definitions and
turns `S ω` into the sum of values, and then the left numerator is literally the left side of `key`.

### Second moments: milestones `hsq` and `hS2`

**R17 · `variance_eq_sub`** changes the **context**: from `hY : MemLp Y 2 μ` (and a probability
measure), `variance_eq_sub hY : Var[Y; μ] = μ[Y ^ 2] - μ[Y] ^ 2`, i.e. `Var Y = E[Y²] − E[Y]²`.
Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)`.
The new hypothesis prints as

```lean
h : Var[Y; μ] = ∫ (x : Ω), (Y ^ 2) x ∂μ - (∫ (x : Ω), Y x ∂μ) ^ 2
```

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, with the `h` above added |

**R18 · `rw [e] at h`** changes the **context**: it rewrites inside the hypothesis `h` instead of the
goal. Use it to put `hvar i` and `hmean i` (or `hSvar`, `hSmean`) into the `variance_eq_sub` fact.
Placeholders: `(a b : ℝ) (e : a = b)`.

| Before | After |
|---|---|
| `h : P a ⊢ P b` | `h : P b ⊢ P b` |

**R19 · `simp only [Pi.pow_apply] at h`** changes the **context**. The lemma is `(Y ^ 2) x = Y x ^ 2`;
it turns the integrand `(Y ^ 2) x` into `Y x ^ 2`, the form the rest of the proof uses.
Placeholders: `(Y : Ω → ℝ) (r : ℝ)`. In the guide `h` goes from

```lean
h : ∫ (x : Ω), (Y ^ 2) x ∂μ = r
h : ∫ (x : Ω), Y x ^ 2 ∂μ = r
```

| Before | After |
|---|---|
| `⊢ ∫ (ω : Ω), Y ω ^ 2 ∂μ = r` | `⊢ ∫ (ω : Ω), Y ω ^ 2 ∂μ = r` (goal unchanged; `h` now matches it) |

Then `linarith` (R4) solves the linear equation in `h` for the second moment.

**W2 (one variable with `E[Y] = 0`, `Var Y = 1`).** `have h := variance_eq_sub hY` (R17),
`rw [h1, h0] at h` (R18), `simp only [Pi.pow_apply] at h` (R19), `linarith` (R4). The goal stays
`⊢ ∫ (ω : Ω), Y ω ^ 2 ∂μ = 1`; `h` evolves as

```lean
h : Var[Y; μ] = ∫ (x : Ω), (Y ^ 2) x ∂μ - (∫ (x : Ω), Y x ∂μ) ^ 2
h : 1 = ∫ (x : Ω), (Y ^ 2) x ∂μ - 0 ^ 2
h : 1 = ∫ (x : Ω), Y x ^ 2 ∂μ - 0 ^ 2
```

### The mean of `S` (milestone `hSmean`)

**R20 · `integral_finsetSum`** changes the **goal**: the integral of a finite sum is the sum of the
integrals, `∫ ω, ∑ i ∈ s, f i ω ∂μ = ∑ i ∈ s, ∫ ω, f i ω ∂μ`, given `hf : ∀ i ∈ s, Integrable (f i) μ`.
Placeholders: `(s : Finset ℕ) (f : ℕ → Ω → ℝ)`. Written `rw [integral_finsetSum s hf]`; with the
arguments left out (`rw [integral_finsetSum]`) the `∀ i ∈ s, Integrable …` becomes a side goal.

| Before | After |
|---|---|
| `⊢ P (∫ (ω : Ω), ∑ i ∈ s, f i ω ∂μ)` | `⊢ P (∑ i ∈ s, ∫ (a : Ω), f i a ∂μ)` |

**R21 · `MemLp.integrable`** changes the **context**: `hf.integrable one_le_two : Integrable f μ` from
`hf : MemLp f 2 μ` (`L² ⊆ L¹` on a finite measure; `one_le_two : 1 ≤ 2` is the exponent comparison).
`IsProbabilityMeasure μ` supplies the finiteness automatically.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, with `h : Integrable f μ` added |

**W3 (a sum of means).** `rw [integral_finsetSum _ (fun i _ => (hL i).integrable one_le_two)]` (R20
with R21), then `simp [ha]` (R10) closes it:

```lean-goal
⊢ ∫ (ω : Ω), ∑ i ∈ Finset.range k, Y i ω ∂μ = ↑k * a
⊢ ∑ i ∈ Finset.range k, ∫ (a : Ω), Y i a ∂μ = ↑k * a
```

In the exercise the goal is `μ[S]` with `S` a `set` name: unfold it first with `simp only [hS,
Finset.sum_apply]` (R15), so the integrand is a sum of values.

### The variance of `S` (milestone `hSvar`): the only use of independence

**R22 · `IndepFun.variance_sum`** changes the **goal**: for pairwise independent `L²` summands,
`Var[∑ i ∈ s, Y i; μ] = ∑ i ∈ s, Var[Y i; μ]`. Arguments: `hL : ∀ i ∈ s, MemLp (Y i) 2 μ` and
`hp : (↑s).Pairwise fun i j => Y i ⟂ᵢ[μ] Y j` (R23). Placeholders:
`{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s : Finset ℕ) (Y : ℕ → Ω → ℝ)`.

| Before | After |
|---|---|
| `⊢ P Var[∑ i ∈ s, Y i; μ]` | `⊢ P (∑ i ∈ s, Var[Y i; μ])` |

**R23 · `Pairwise r` → `(↑s).Pairwise r`** changes the **goal and the context**: `intro i _ j _ hij`
introduces the two indices, their memberships (unused, so `_`) and `hij : i ≠ j`; then `hr hij` closes
`r i j`. As a term: `fun i _ j _ hij => hr hij`. Placeholders: `(r : ℕ → ℕ → Prop) (s : Finset ℕ)`.

| Before | After `intro i _ j _ hij` |
|---|---|
| `hr : Pairwise r ⊢ (↑s).Pairwise r` | `i : ℕ, a✝¹ : i ∈ ↑s, j : ℕ, a✝ : j ∈ ↑s, hij : i ≠ j ⊢ r i j` |

For `hS2`, repeat the `hsq` pattern (R17 → R18 → R19 → R4) on `variance_eq_sub hSL2` with `hSvar` and
`hSmean`.

### The final computation

**R24 · `integral_div`** changes the **goal**: `∫ a, f a / r ∂μ = (∫ a, f a ∂μ) / r`. No
integrability needed (both sides are `0` when `f` is not integrable). Placeholders: `(f : Ω → ℝ) (r : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (ω : Ω), f ω / r ∂μ)` | `⊢ P ((∫ (a : Ω), f a ∂μ) / r)` |

**R25 · `integral_sub`** changes the **goal list**: `∫ a, f a - g a ∂μ = ∫ f - ∫ g`, which needs both
`Integrable f μ` and `Integrable g μ`. `rw [integral_sub]` without the two proofs adds them as side
goals `case hf`, `case hg`, after the main goal. Placeholders: `(f g : Ω → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (ω : Ω), f ω - g ω ∂μ)` | `⊢ P (∫ (a : Ω), f a ∂μ - ∫ (a : Ω), g a ∂μ)`, `⊢ Integrable f μ`, `⊢ Integrable g μ` |

**R26 · `MemLp.integrable_sq`** changes the **context**: `hf.integrable_sq : Integrable (fun x => f x ^ 2) μ`
from `hf : MemLp f 2 μ` (`f ∈ L²` means exactly that `f²` is integrable).

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, with `h : Integrable (fun x => f x ^ 2) μ` added |

**R27 · `integrable_finsetSum`** changes the **context**: `integrable_finsetSum s hf :
Integrable (fun a => ∑ i ∈ s, f i a) μ` from `hf : ∀ i ∈ s, Integrable (f i) μ`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, with `h : Integrable (fun a => ∑ i ∈ s, f i a) μ` added |

**R28 · `Integrable.div_const`** changes the **context**: `hf.div_const c : Integrable (fun x => f x / c) μ`
from `hf : Integrable f μ`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, with `h : Integrable (fun x => f x / c) μ` added |

**W4 (side goals of a `rw` chain).** `rw [integral_div, integral_sub, integral_div]` (R24, R25, R24) on
the first goal below; `rw` closes the main goal by `rfl` and leaves the two `Integrable` goals, closed
by `hY.integrable_sq` (R26) and `hZ.div_const c` (R28):

```lean-goal
⊢ ∫ (ω : Ω), (Y ω ^ 2 - Z ω / c) / 2 ∂μ = (∫ (ω : Ω), Y ω ^ 2 ∂μ - (∫ (ω : Ω), Z ω ∂μ) / c) / 2
⊢ Integrable (fun a => Y a ^ 2) μ
⊢ Integrable (fun a => Z a / c) μ
```

In the exercise, `rw [e, integral_div, integral_sub, integral_finsetSum, integral_div, hS2]` leaves
four goals, in this order: the numeric goal (close with `simp only [hsq, …R10…]`, R11, R12), then
`∀ i ∈ Finset.range n, Integrable (fun a => X i a ^ 2) μ` (R26), then
`Integrable (fun a => ∑ i ∈ Finset.range n, X i a ^ 2) μ` (R27 with R26), then
`Integrable (fun a => S a ^ 2 / ↑n) μ` (R26 then R28). Use `·` to focus each one.

---

## Traps

- `∑ i ∈ range n, c` (a term with no `i`) does not disappear by itself: it is `n • c`
  (`Finset.sum_const`, `Finset.card_range`), and `nsmul_eq_mul` makes it `↑n * c` (R10). Put all three
  in your `simp only`.
- The infoview never shows `μ[F]`: it shows `∫ (x : Ω), F x ∂μ`. A hypothesis stated as
  `μ[fun ω => X i ω ^ 2] = …` prints with an unreduced `(fun ω => X i ω ^ 2) x`; `simp only [hsq]`
  still finds it.
- `variance_eq_sub` gives the integrand `(Y ^ 2) x`, not `Y x ^ 2`; rewrite with `Pi.pow_apply` (R19)
  before comparing it with your goal.
- `rw [integral_sub]` and `rw [integral_finsetSum]` without arguments add `Integrable` side goals after
  the main goal; count them before writing the `·` blocks (W4).
- `field_simp` only clears a denominator whose `≠ 0` proof is in the context: prove `(n : ℝ) ≠ 0` and
  `(n : ℝ) - 1 ≠ 0` first. `1 < n` lives in `ℕ`; move it to `ℝ` with `exact_mod_cast` (R3).
- `hindep` is `Pairwise …` (all `i ≠ j`), but `IndepFun.variance_sum` wants `(↑s).Pairwise …` (R23).
- `set` replaces the sum only in the goal and context present at that moment. A later `have` you type
  shows exactly what you typed. And `S` is a local definition (`S : Ω → ℝ := …`): `simp only
  [Finset.sum_apply]` on `⊢ S ω = …` makes no progress, because it does not unfold `S`. Pass `hS` too:
  `simp only [hS, Finset.sum_apply]` (for `hSapp` and `hSmean`), or `rw [hS]` first (for `hSvar`).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `0 < n` from `1 < n` (ℕ) | `omega` | R1 |
| `(n : ℝ) ≠ 0` | `positivity` | R2 |
| `(1 : ℝ) < n` from `1 < n` | `exact_mod_cast hn` | R3 |
| linear facts over `ℝ` | `linarith` | R4 |
| expand `∑ (x i - c) ^ 2` | `simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]` | R5–R10 |
| clear `/ n`, finish | `field_simp` then `ring` | R11, R12 |
| name the sum | `set S : Ω → ℝ := ∑ i ∈ Finset.range n, X i with hS` | R13 |
| sum is `L²` | `memLp_finsetSum' _ (fun i _ => hL2 i)` | R14 |
| `(∑ g i) ω → ∑ g i ω` | `simp only [Finset.sum_apply]` | R15 |
| equation of functions | `funext ω` | R16 |
| `Var Y = E[Y²] − E[Y]²` | `have := variance_eq_sub hY` | R17 |
| rewrite in a hypothesis | `rw [hvar, hmean] at this` | R18 |
| `(Y ^ 2) x → Y x ^ 2` | `simp only [Pi.pow_apply] at this` | R19 |
| `E[∑] = ∑ E` | `rw [integral_finsetSum _ (fun i _ => …)]` | R20 |
| `L² → L¹` | `(hL2 i).integrable one_le_two` | R21 |
| `Var[∑] = ∑ Var` | `IndepFun.variance_sum (fun i _ => hL2 i) (fun i _ j _ hij => hindep hij)` | R22, R23 |
| `∫ f / r` | `rw [integral_div]` | R24 |
| `∫ (f - g)` | `rw [integral_sub]` (+ two side goals) | R25 |
| `f²` integrable | `hf.integrable_sq` | R26 |
| finite sum integrable | `integrable_finsetSum _ (fun i _ => …)` | R27 |
| `f / c` integrable | `hf.div_const c` | R28 |
| see the state | infoview | |
