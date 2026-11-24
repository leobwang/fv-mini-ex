# H050 · Weak law of large numbers: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033: `rw`, `simp`, `have`, `calc`, `funext`, `intro`, `exact`,
`apply`, `refine`). **New here:** Mathlib's measure-theoretic probability (probability measures, integrals as
expectations, `L²` random variables, variance, independence, Chebyshev's inequality), extended non-negative
reals `ℝ≥0∞` (where measures take their values), filters and limits (`atTop`, `𝓝`, `Tendsto`, `∀ᶠ`), convergence
in measure, and the tactics `ring`, `field_simp`, `gcongr`, `exact_mod_cast`, `convert`, `filter_upwards`.

The mathematics. Let `X̄ₙ(ω) = (X₀(ω) + … + X_{n-1}(ω)) / n` (the *sample mean*), with `E Xᵢ = m`,
`Var Xᵢ ≤ C` and the `Xᵢ` pairwise independent. Three milestones and a squeeze:

1. `sample_mean_mean`: `E X̄ₙ = (1/n) ∑ E Xᵢ = (1/n)·n·m = m` (linearity; needs `n > 0`).
2. `sample_mean_variance_le`: `Var X̄ₙ = n⁻² Var(∑ Xᵢ) = n⁻² ∑ Var Xᵢ ≤ n⁻²·n·C = C/n`. The middle equality
   is where pairwise independence is used (the covariances vanish).
3. `tail_bound`: Chebyshev, `P(|Y - E Y| ≥ ε) ≤ Var Y / ε²`, for `Y = X̄ₙ`, gives
   `P(|X̄ₙ - m| ≥ ε) ≤ C / (n ε²)`.
4. `weak_law`: *convergence in probability* (Mathlib: `TendstoInMeasure`) means: for each `ε > 0`,
   `P(|X̄ₙ - m| ≥ ε) → 0`. Squeeze it between the constant `0` and the bound `C / (n ε²) → 0`.
   Probabilities live in `ℝ≥0∞`, so the bound is written `ENNReal.ofReal (C / (n ε²))`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`apply`/`refine`/`exact`. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal, and `k : … → G` only consumes a new hypothesis.
- Placeholders are written as Lean binders. `{Ω : Type}` is any type. A bracket such as `[MeasurableSpace Ω]`
  is a requirement on the type (a *type class*): here, that `Ω` carries a σ-algebra (its events). `ℝ` and `ℕ`
  carry theirs automatically; your `Ω` gets one from the hypothesis `[MeasurableSpace Ω]`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that. A hypothesis
  whose type contains `, ` (such as `∀ i ∈ s, …`) is written next to the table: "context gains `h : …`".
- A state containing `|` (absolute value, set-builder `{ω | …}`) cannot sit in a Markdown table (`|` splits
  cells). Such states are given as a `lean-goal` block instead: the first line is the goal before the step,
  the next line the goal after.

## Reading the goals

| You see | It means |
|---|---|
| `Ω : Type u_1` | the sample space; `Type*` in a statement makes a universe variable `u_1` (ignore it) |
| `μ : Measure Ω`, `IsProbabilityMeasure μ` | a measure on `Ω` with `μ Ω = 1`: the probability `P` |
| `μ S` | `P(S)` for a set `S ⊆ Ω`; its type is `ℝ≥0∞` (printed `ENNReal`), the interval `[0, ∞]` |
| `ENNReal.ofReal r` | the real `r` as an element of `ℝ≥0∞`; negative `r` becomes `0` |
| `⊥` | the least element of an order; in `ℝ≥0∞` it is `0` |
| `μ[Y]` | the expectation `E Y`; the infoview prints it as `∫ (x : Ω), Y x ∂μ` (Bochner integral) |
| `Var[Y; μ]` | `variance Y μ = E (Y - E Y)²`, a real number |
| `MemLp Y 2 μ` | `Y` is in `L²`: measurable enough and `E Y² < ∞`. With `2` replaced by `1`: integrable |
| `Integrable Y μ` | `E ‖Y‖ < ∞` (and `Y` is a.e.-strongly measurable): what an integral lemma needs |
| `Y ⟂ᵢ[μ] Z` | `IndepFun Y Z μ`: the random variables `Y`, `Z` are independent under `μ` |
| `Pairwise r` | `∀ ⦃i j⦄, i ≠ j → r i j` |
| `(↑s).Pairwise r` | `Set.Pairwise ↑s r`: `∀ i ∈ s, ∀ j ∈ s, i ≠ j → r i j`; `↑s` is the finset `s` as a set |
| `s : Finset ℕ` | a finite set of natural numbers (a list without order or repeats) |
| `Finset.range n` | the finite set `{0, 1, …, n - 1}` |
| `∑ i ∈ s, f i` | `f` summed over the finite set `s` |
| `∑ i ∈ s, Y i` (with `Y i : Ω → ℝ`) | a sum of **functions**; `(∑ i ∈ s, Y i) ω = ∑ i ∈ s, Y i ω` (R7) |
| `↑n` | the natural number `n` cast to `ℝ` |
| `{ω \| p ω}` | the set (event) of outcomes `ω` with `p ω` |
| `\|x\|` | the absolute value of `x : ℝ` |
| `dist x y` | the distance; on `ℝ`, `\|x - y\|` (R20) |
| `fun (n : ℕ) ω => …` | a function of two arguments: the sequence of random variables `n ↦ (ω ↦ …)` |
| `fun _ => m` | the constant random variable `m` (the argument is ignored) |
| `IsFiniteMeasure μ` | `μ Ω < ∞`; a probability measure has it, and Lean finds it by itself |
| `atTop` | the filter "`n → ∞`" on `ℕ` |
| `𝓝 a` | the neighbourhood filter of `a`: "close to `a`" (`𝓝` needs `open Topology`) |
| `Tendsto u atTop (𝓝 a)` | `u n → a` as `n → ∞` |
| `∀ᶠ n in atTop, p n` | `p n` holds for all large `n` (*eventually*) |
| `TendstoInMeasure μ Z atTop g` | `Z n → g` in measure (in probability): `∀ ε > 0, μ {ω \| ε ≤ dist (Z n ω) (g ω)} → 0` (R24) |
| `inst✝ : …` | an anonymous instance hypothesis; never named, used automatically |

---

## Part 1 · `sample_mean_mean` (milestone)

Statement: for `n > 0`, `μ[fun ω => (∑ i ∈ Finset.range n, X i ω) / n] = m`. Plan: pull `/ n` out of the
integral, swap integral and finite sum, replace each `∫ X i` by `m`, and cancel `n`.

**R1 · `rw [integral_div]`** changes the **goal**: a constant divisor leaves the integral. Statement:
`∫ a, f a / r ∂μ = (∫ a, f a ∂μ) / r`. Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
(f : Ω → ℝ) (r : ℝ)`. In the exercise the goal shows the integrand as `(fun ω => …) x`; `rw` still finds it.

| Before | After |
|---|---|
| `⊢ P (∫ (ω : Ω), f ω / r ∂μ)` | `⊢ P ((∫ (a : Ω), f a ∂μ) / r)` |

**R2 · `hf.integrable one_le_two`** (`MemLp.integrable`) changes the **context** (with `have`): an `L²`
variable on a finite measure is integrable. Statement: `1 ≤ q → MemLp f q μ → Integrable f μ` with
`[IsFiniteMeasure μ]` (a probability measure is finite; Lean finds that itself). `one_le_two : 1 ≤ 2` is the
side condition `1 ≤ q` for `q = 2`. Placeholders: `(f : Ω → ℝ) (hf : MemLp f 2 μ)`. In the exercise:
`(hL2 i).integrable one_le_two`.

| Before | After `have h := hf.integrable one_le_two` |
|---|---|
| `⊢ G` | `h : Integrable f μ ⊢ G` |

**R3 · `rw [integral_finsetSum s hf]`** changes the **goal**: the integral of a finite sum is the sum of the
integrals. Statement: `(∀ i ∈ s, Integrable (f i) μ) → ∫ a, ∑ i ∈ s, f i a ∂μ = ∑ i ∈ s, ∫ a, f i a ∂μ`.
Placeholders: `(s : Finset ℕ) (f : ℕ → Ω → ℝ)`. Write `s` as `_` to let Lean find it; the integrability
argument is a function `fun i _ => …` built with R2.

| Before | After |
|---|---|
| `⊢ P (∫ (ω : Ω), ∑ i ∈ s, f i ω ∂μ)` | `⊢ P (∑ i ∈ s, ∫ (a : Ω), f i a ∂μ)` |

**R4 · `simp [hf]`** on a sum of equal terms changes the **goal**: with `hf : ∀ i, f i = c`, `simp` rewrites
every term to `c`, then `Finset.sum_const` (`∑ _ ∈ s, c = s.card • c`), `Finset.card_range`
(`(Finset.range n).card = n`) and `smul_eq_mul` give `↑n * c`. Placeholders: `(n : ℕ) (f : ℕ → ℝ) (c : ℝ)`.
In the exercise `simp [hmean]` does this (Part 1) and plain `simp` does `∑ i ∈ Finset.range n, C = ↑n * C`
(Part 2).

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ Finset.range n, f i)` | `⊢ P (↑n * c)` |

**R5 · `field_simp`** changes the **goal**: it multiplies out denominators, using every `x ≠ 0` it can prove;
here it gets `↑k ≠ 0` from `hk : 0 < k` in the context, and the goal closes. Placeholders: `(k : ℕ) (hk : 0 < k)
(a : ℝ)`. It also finishes `(↑n)⁻¹ ^ 2 * (↑n * C) = C / ↑n` in Part 2.

| Before | After |
|---|---|
| `hk : 0 < k ⊢ ↑k * a / ↑k = a` | no goals |

---

## Part 2 · `sample_mean_variance_le` (milestone)

Statement: `Var[fun ω => (∑ i ∈ Finset.range n, X i ω) / n; μ] ≤ C / n`. Plan: restate the sample mean as
`fun ω => (↑n)⁻¹ * (∑ i ∈ Finset.range n, X i) ω` (the shape R9 and R10 want), pull out `(↑n)⁻¹ ^ 2`, split the
variance of the sum, bound each term by `C`.

**R6 · `funext ω`** changes the **goal and the context**: an equation of functions becomes an equation of their
values at a new `ω`. Placeholders: `{Ω : Type} (f g : Ω → ℝ)`.

| Before | After |
|---|---|
| `⊢ f = g` | `ω : Ω ⊢ f ω = g ω` |

**R7 · `simp [Finset.sum_apply]`** changes the **goal**: a sum of functions applied to `ω` becomes the sum of
the values. Statement: `(∑ c ∈ s, g c) a = ∑ c ∈ s, g c a`. Placeholders: `(s : Finset ℕ) (g : ℕ → Ω → ℝ)
(ω : Ω)`. (The bound variable may be renamed; `∑ c ∈ s, g c ω` and `∑ i ∈ s, g i ω` are the same term.)

| Before | After |
|---|---|
| `⊢ P ((∑ i ∈ s, g i) ω)` | `⊢ P (∑ c ∈ s, g c ω)` |

**R8 · `ring`** **closes** an identity of commutative rings, and in a field it also handles division and `⁻¹`
of unknowns: `a / b = b⁻¹ * a` (it reads `a / b` as `a * b⁻¹` and `b⁻¹` as an atom). It proves the leftover
`(∑ …) / ↑n = (↑n)⁻¹ * ∑ …` after R6, R7. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ a / b = b⁻¹ * a` | no goals |

**R9 · `rw [variance_const_mul]`** changes the **goal**: a constant factor leaves the variance squared.
Statement: `Var[fun ω => c * Y ω; μ] = c ^ 2 * Var[Y; μ]`. Placeholders: `(c : ℝ) (Y : Ω → ℝ)`. The integrand
must literally be `fun ω => c * Y ω`; that is why the sample mean is restated first (Trap 1).

| Before | After |
|---|---|
| `⊢ P Var[fun ω => c * Y ω; μ]` | `⊢ P (c ^ 2 * Var[Y; μ])` |

**R10 · `rw [IndepFun.variance_sum hL hp]`** changes the **goal**: for pairwise independent `L²` summands the
variance of the sum is the sum of the variances. Statement: `(∀ i ∈ s, MemLp (Y i) 2 μ) →
(↑s).Pairwise (fun i j => Y i ⟂ᵢ[μ] Y j) → Var[∑ i ∈ s, Y i; μ] = ∑ i ∈ s, Var[Y i; μ]`. Placeholders:
`(s : Finset ℕ) (Y : ℕ → Ω → ℝ)`. In the exercise `hL` is `fun i _ => hL2 i` and `hp` comes from R11.

| Before | After |
|---|---|
| `⊢ P Var[∑ i ∈ s, Y i; μ]` | `⊢ P (∑ i ∈ s, Var[Y i; μ])` |

**R11 · `intro i _ j _ hij`, then `exact hr hij`** changes the **goal and the context**: `(↑s).Pairwise r`
unfolds to `∀ i ∈ ↑s, ∀ j ∈ ↑s, i ≠ j → r i j`; the two memberships are not needed (`_`), and
`hr : Pairwise r` applied to `hij : i ≠ j` gives `r i j`. As a term: `fun i _ j _ hij => hindep hij`.
Placeholders: `(r : ℕ → ℕ → Prop) (s : Finset ℕ)`.

| Before | After |
|---|---|
| `⊢ (↑s).Pairwise r` | `i : ℕ, hij : i ≠ j ⊢ r i j` |

**R12 · `apply Finset.sum_le_sum`** changes the **goal**: a sum is bounded termwise. Statement:
`(∀ i ∈ s, f i ≤ g i) → ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i`. Placeholders: `(s : Finset ℕ) (f g : ℕ → ℝ)`. In the
exercise, as a term inside a `calc` step: `Finset.sum_le_sum fun i _ => hvar i`.

| Before | After |
|---|---|
| `⊢ ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i` | `⊢ ∀ i ∈ s, f i ≤ g i` |

**R13 · `exact_mod_cast hk`** **closes** a goal that is `hk` up to casts: `(0 : ℝ) < ↑k` from `hk : 0 < k` in
`ℕ`. Placeholders: `(k : ℕ)`. `gcongr` and `field_simp` need such facts about `↑n` in the context.

| Before | After |
|---|---|
| `hk : 0 < k ⊢ 0 < ↑k` | no goals |

**R14 · `gcongr`** changes the **goal**: for an inequality whose two sides have the same shape ("generalized
congruence"), it reduces it to the inequality between the parts that differ, proving the side conditions
(`0 ≤ c ^ 2`, `0 < ε ^ 2`) itself, and closes the reduced goal when a hypothesis states it. Placeholders:
`(c a b : ℝ)`. In the exercise: `(↑n)⁻¹ ^ 2 * ∑ … ≤ (↑n)⁻¹ ^ 2 * (↑n * C)` from `hs`, and
`Var[…] / ε ^ 2 ≤ C / ↑n / ε ^ 2` from `hv`.

| Before | After |
|---|---|
| `h : a ≤ d ⊢ c ^ 2 * a ≤ c ^ 2 * b` | `h : a ≤ d ⊢ a ≤ b` |

**W1.** `Var[fun ω => 2 * Y ω; μ] ≤ 2 ^ 2 * C` from `hC : Var[Y; μ] ≤ C`: R9, then `gcongr` closes the rest
with `hC`.

| Before | After `rw [variance_const_mul]` |
|---|---|
| `⊢ Var[fun ω => 2 * Y ω; μ] ≤ 2 ^ 2 * C` | `⊢ 2 ^ 2 * Var[Y; μ] ≤ 2 ^ 2 * C` |

---

## Part 3 · `tail_bound` (milestone)

Statement: `μ {ω | ε ≤ dist ((∑ i ∈ Finset.range n, X i ω) / n) m} ≤ ENNReal.ofReal (C / (n * ε ^ 2))`.
Plan: the sample mean is `L²`; Chebyshev; replace its mean by `m` (milestone 1); `dist` → `|·|`; compare the
two `ENNReal.ofReal`s; bound the variance (milestone 2).

**R15 · `memLp_finsetSum' s hL`** changes the **context**: a finite sum of `L²` functions is `L²`. Statement:
`(∀ i ∈ s, MemLp (f i) p μ) → MemLp (∑ i ∈ s, f i) p μ`. Placeholders: `(s : Finset ℕ) (Y : ℕ → Ω → ℝ)`.
After `have h := memLp_finsetSum' s hL` the goal is unchanged and the context gains
`h : MemLp (∑ i ∈ s, Y i) 2 μ` (a sum of functions, R7).

**R16 · `hf.const_mul c`** (`MemLp.const_mul`) changes the **context**: `MemLp f p μ → MemLp (fun x => c * f x) p μ`.
Placeholders: `(f : Ω → ℝ) (c : ℝ)`. Chained with R15: `(memLp_finsetSum' _ hL).const_mul (↑n)⁻¹`.

| Before | After `have h := hf.const_mul c` |
|---|---|
| `⊢ G` | `h : MemLp (fun x => c * f x) 2 μ ⊢ G` |

**R17 · `convert h using 1`** changes the **goal**: it proves the goal from `h` up to the parts that differ,
which become new goals. `using 1` compares only the top level, so `MemLp g 2 μ` against `MemLp f 2 μ` leaves
`g = f` (finish with R6 → R7 → R8). Placeholders: `(f g : Ω → ℝ) (h : MemLp f 2 μ)`.

| Before | After |
|---|---|
| `h : MemLp f 2 μ ⊢ MemLp g 2 μ` | `h : MemLp f 2 μ ⊢ g = f` |

**R18 · `have h := meas_ge_le_variance_div_sq hY hc`** (Chebyshev's inequality) changes the **context**.
Statement: `MemLp Y 2 μ → 0 < c → μ {ω | c ≤ |Y ω - μ[Y]|} ≤ ENNReal.ofReal (Var[Y; μ] / c ^ 2)`, with
`[IsFiniteMeasure μ]`. Placeholders: `(Y : Ω → ℝ) (c : ℝ)`. The goal is unchanged (`⊢ G`); the context gains
`h : μ {ω | c ≤ |Y ω - ∫ (x : Ω), Y x ∂μ|} ≤ ENNReal.ofReal (Var[Y; μ] / c ^ 2)`. Note `μ[Y]` printed as the
integral `∫ (x : Ω), Y x ∂μ`: that is the term milestone 1 rewrites.

**R19 · `rw [e] at h`** changes the **context**: it rewrites the hypothesis `h` instead of the goal.
Placeholders: `(a b : ℝ) (e : a = b)`. In the exercise `e` is milestone 1, `sample_mean_mean μ X m hL2 hmean n hn`,
and it turns the integral in Chebyshev's `h` into `m`.

| Before | After |
|---|---|
| `h : P a ⊢ P b` | `h : P b ⊢ P b` |

**R20 · `simp only [Real.dist_eq]`** changes the **goal**: on `ℝ`, `dist x y = |x - y|`. Placeholders:
`(x y : ℝ)`. Needed because the goal says `dist` and Chebyshev says `|· - ·|`.

```lean-goal
⊢ P (dist x y)
⊢ P |x - y|
```

**R21 · `refine h.trans ?_`** (`le_trans`) changes the **goal**: to prove `a ≤ c` from `h : a ≤ b`, prove
`b ≤ c`. Placeholders: `{α : Type} [Preorder α] (a b c : α)` (`α` has a `≤`; `ℝ` and `ℝ≥0∞` qualify).

| Before | After |
|---|---|
| `h : a ≤ b ⊢ a ≤ c` | `h : a ≤ b ⊢ b ≤ c` |

**R22 · `apply ENNReal.ofReal_le_ofReal`** changes the **goal**: `ENNReal.ofReal` is monotone, so compare the
reals. Statement: `p ≤ q → ENNReal.ofReal p ≤ ENNReal.ofReal q`. Placeholders: `(p q : ℝ)`. With R21 in one
line: `refine h.trans (ENNReal.ofReal_le_ofReal ?_)`.

| Before | After |
|---|---|
| `⊢ ENNReal.ofReal p ≤ ENNReal.ofReal q` | `⊢ p ≤ q` |

**R23 · `rw [div_div]`** changes the **goal**: `a / b / c = a / (b * c)`. Placeholders:
`{α : Type} [DivisionCommMonoid α] (a b c : α)` (`α` has a commutative `*` and `/`; `ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ P (a / b / c)` | `⊢ P (a / (b * c))` |

**W2: Chebyshev for one variable at distance `2`.** `have h := meas_ge_le_variance_div_sq hY (by norm_num : (0 : ℝ) < 2)`
(R18), `refine h.trans (ENNReal.ofReal_le_ofReal ?_)` (R21, R22), `gcongr` with `hC : Var[Y; μ] ≤ C` (R14):

```lean-goal
⊢ μ {ω | 2 ≤ |Y ω - ∫ (x : Ω), Y x ∂μ|} ≤ ENNReal.ofReal (C / 2 ^ 2)
⊢ Var[Y; μ] / 2 ^ 2 ≤ C / 2 ^ 2
```

---

## Part 4 · `weak_law`

Statement: `TendstoInMeasure μ (fun n ω => (∑ i ∈ Finset.range n, X i ω) / n) atTop (fun _ => m)`. Plan: unfold
convergence in measure, fix `ε`, prove that the bound `ENNReal.ofReal (C / (n * ε ^ 2))` tends to `0`, and squeeze.

**R24 · `rw [tendstoInMeasure_iff_dist]`** changes the **goal**: convergence in measure becomes "for every
`ε > 0`, the measure of the `ε`-tail tends to `0`". Statement: `TendstoInMeasure μ f l g ↔ ∀ ε, 0 < ε →
Tendsto (fun i => μ {x | ε ≤ dist (f i x) (g x)}) l (𝓝 0)`. Placeholders: `(Z : ℕ → Ω → ℝ) (g : Ω → ℝ)`.
Then `intro ε hε`.

```lean-goal
⊢ TendstoInMeasure μ Z atTop g
⊢ ∀ (ε : ℝ), 0 < ε → Tendsto (fun i => μ {x | ε ≤ dist (Z i x) (g x)}) atTop (𝓝 0)
```

**R25 · `rw [← ENNReal.ofReal_zero]`** changes the **goal**: the limit `0 : ℝ≥0∞` is written as
`ENNReal.ofReal 0`, the form R26 needs. Statement: `ENNReal.ofReal 0 = 0`. Placeholders: `(u : ℕ → ℝ≥0∞)`.

| Before | After |
|---|---|
| `⊢ Tendsto u atTop (𝓝 0)` | `⊢ Tendsto u atTop (𝓝 (ENNReal.ofReal 0))` |

**R26 · `apply ENNReal.tendsto_ofReal`** changes the **goal**: `ENNReal.ofReal` is continuous, so a real limit
suffices. Statement: `Tendsto v f (𝓝 a) → Tendsto (fun n => ENNReal.ofReal (v n)) f (𝓝 (ENNReal.ofReal a))`.
Placeholders: `(v : ℕ → ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ Tendsto (fun n => ENNReal.ofReal (v n)) atTop (𝓝 (ENNReal.ofReal a))` | `⊢ Tendsto v atTop (𝓝 a)` |

**R27 · `tendsto_const_div_atTop_nhds_zero_nat c`** changes the **context** (with `have`): `c / n → 0`.
Statement: `Tendsto (fun n : ℕ => c / ↑n) atTop (𝓝 0)`. Placeholders: `(c : ℝ)`. In the exercise
`c = C / ε ^ 2`, so it gives `C / ε ^ 2 / ↑n`, which is not literally `C / (↑n * ε ^ 2)`: R28 bridges.

| Before | After `have h := tendsto_const_div_atTop_nhds_zero_nat c` |
|---|---|
| `⊢ G` | `h : Tendsto (fun n => c / ↑n) atTop (𝓝 0) ⊢ G` |

**R28 · `refine h.congr fun n => ?_`** (`Tendsto.congr`) changes the **goal and the context**: a limit of `u`
is a limit of every `v` equal to it termwise. Statement: `(∀ x, u x = v x) → Tendsto u l₁ l₂ → Tendsto v l₁ l₂`.
Placeholders: `(u v : ℕ → ℝ) (a : ℝ)`. In the exercise the leftover is `C / ε ^ 2 / ↑n = C / (↑n * ε ^ 2)`:
R23, then `rw [mul_comm]` (`mul_comm : a * b = b * a`; without arguments `rw` rewrites the first product
it finds, here `ε ^ 2 * ↑n`, and closes the goal by `rfl`).

| Before | After |
|---|---|
| `h : Tendsto u atTop (𝓝 a) ⊢ Tendsto v atTop (𝓝 a)` | `n : ℕ ⊢ u n = v n` |

**W3: an `ℝ≥0∞` limit through `ENNReal.ofReal`.** R25, R26, then R27 with `c = 3` closes it:

```lean-goal
⊢ Tendsto (fun n => ENNReal.ofReal (3 / ↑n)) atTop (𝓝 0)
⊢ Tendsto (fun n => ENNReal.ofReal (3 / ↑n)) atTop (𝓝 (ENNReal.ofReal 0))
⊢ Tendsto (fun a => 3 / ↑a) atTop (𝓝 0)
```

**R29 · `refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg hw ?_ ?_`** (the squeeze theorem) changes the
**goal list**: if `g → a` and `w → a` and eventually `g ≤ f ≤ w`, then `f → a`. Statement:
`Tendsto g b (𝓝 a) → Tendsto w b (𝓝 a) → (∀ᶠ n in b, g n ≤ f n) → (∀ᶠ n in b, f n ≤ w n) → Tendsto f b (𝓝 a)`,
in any order topology (`ℝ`, `ℝ≥0∞`). Placeholders: `(f g w : ℕ → ℝ≥0∞) (a : ℝ≥0∞)`. In the exercise `g` is the
constant `0` (R30), `w` the bound (`hlim`), the lower bound is R31 + R32 and the upper bound is R33 + R34.

| Before | After |
|---|---|
| `⊢ Tendsto f atTop (𝓝 a)` | `⊢ ∀ᶠ (b : ℕ) in atTop, g b ≤ f b`, `⊢ ∀ᶠ (b : ℕ) in atTop, f b ≤ w b` |

**R30 · `tendsto_const_nhds`** **closes** "a constant sequence tends to its value". Statement:
`Tendsto (fun _ => a) l (𝓝 a)`. Placeholders: `(a : ℝ≥0∞)`.

| Before | After |
|---|---|
| `⊢ Tendsto (fun x => a) atTop (𝓝 a)` | no goals |

**R31 · `apply Eventually.of_forall`** changes the **goal**: what holds for all `n` holds eventually. Statement:
`(∀ x, p x) → ∀ᶠ x in l, p x`. Placeholders: `(p : ℕ → Prop)`. Term form: `Eventually.of_forall fun _ => bot_le`.

| Before | After |
|---|---|
| `⊢ ∀ᶠ (n : ℕ) in atTop, p n` | `⊢ ∀ (x : ℕ), p x` |

**R32 · `bot_le`** **closes** `⊥ ≤ x`. In `ℝ≥0∞` the bottom element is `0`, so it closes `0 ≤ x` (a measure
is never negative). Placeholders: `(x : ℝ≥0∞)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ x` | no goals |

**R33 · `eventually_ge_atTop a`** changes the **context** (with `have`): all large `n` are `≥ a`. Statement:
`∀ᶠ x in atTop, a ≤ x`. Placeholders: `(a : ℕ)`, here `a = 1`. It supplies `n ≥ 1`, i.e. `0 < n`, for milestone 3.
The context gains `h : ∀ᶠ (x : ℕ) in atTop, 1 ≤ x`.

**R34 · `filter_upwards [h] with n hn`** changes the **goal and the context**: to prove `∀ᶠ n, q n` from
`h : ∀ᶠ n, p n`, fix `n` with `hn : p n` and prove `q n`. Placeholders: `(p q : ℕ → Prop)`. In the exercise:
`filter_upwards [eventually_ge_atTop 1] with n hn`, then milestone 3 with `hn`.

| Before | After |
|---|---|
| `⊢ ∀ᶠ (n : ℕ) in atTop, q n` | `n : ℕ, hn : p n ⊢ q n` |

**W4: the squeeze in `ℝ≥0∞`**, with `hw : Tendsto w atTop (𝓝 0)` and a bound valid for `n ≥ 1`:
`refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hw (Eventually.of_forall fun _ => bot_le) ?_`
(R29–R32), then `filter_upwards [eventually_ge_atTop 1] with n hn` (R33, R34).

| Before | After the `refine` | After `filter_upwards` |
|---|---|---|
| `⊢ Tendsto f atTop (𝓝 0)` | `⊢ ∀ᶠ (b : ℕ) in atTop, f b ≤ w b` | `hn : 1 ≤ n ⊢ f n ≤ w n` |

---

## Traps

- **The shape of the sample mean.** The statement writes `fun ω => (∑ i ∈ Finset.range n, X i ω) / n`.
  `variance_const_mul` (R9) wants `fun ω => c * Y ω`, and `IndepFun.variance_sum` (R10) wants
  `Var[∑ i ∈ s, Y i; μ]` with a sum of **functions**. Prove the restatement
  `(fun ω => (∑ …) / n) = fun ω => (↑n)⁻¹ * (∑ i ∈ Finset.range n, X i) ω` first (R6, R7, R8) and `rw` with it.
  The same restatement (by R17) turns R15 + R16 into `MemLp` of the sample mean.
- `μ[Y]` is printed as `∫ (x : Ω), Y x ∂μ`. After Chebyshev (R18) the integral in `h` is the term milestone 1
  is about; `rw [sample_mean_mean …] at h` (R19) replaces it by `m`.
- Chebyshev states `c ≤ |Y ω - μ[Y]|`, the goal `ε ≤ dist (…) m`: `simp only [Real.dist_eq]` (R20) before
  comparing.
- After R24 and `intro ε hε` the goal reads
  `Tendsto (fun i => μ {x | ε ≤ dist ((∑ i ∈ Finset.range i, X i x) / ↑i) m}) atTop (𝓝 0)`. The sequence
  index and the summation index are both printed `i`: in `Finset.range i` and `/ ↑i` it is the sequence index
  (`n`), in `X i x` the summand. The `n` you get from `filter_upwards … with n hn` (R34) is that sequence index.
- `Pairwise` (all of `ℕ`) is not `(↑s).Pairwise` (a finite set): R11 converts, `fun i _ j _ hij => hindep hij`.
- `eventually_ge_atTop 1` gives `hn : 1 ≤ n`, and milestone 3 asks `0 < n`. On `ℕ`, `0 < n` is by definition
  `1 ≤ n`, so `exact … n hn` is accepted as is.
- R27 gives `C / ε ^ 2 / ↑n`, the bound is `C / (↑n * ε ^ 2)`. These are different terms: use R28 and prove
  the termwise equation with `rw [div_div, mul_comm]`.
- Measures take values in `ℝ≥0∞`, not `ℝ`: write the real bound inside `ENNReal.ofReal`, compare with R22, and
  take limits with R25, R26. `0 ≤ μ S` in `ℝ≥0∞` is `bot_le` (R32).
- `gcongr` (R14) and `field_simp` (R5) need `0 < ↑n` or `↑n ≠ 0` derivable from the context; with `hn : 0 < n`
  (in `ℕ`) `field_simp` manages, and `have hn' : (0 : ℝ) < n := by exact_mod_cast hn` (R13) covers the rest.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `/ r` out of an integral | `rw [integral_div]` | R1 |
| `L²` → integrable | `(hL2 i).integrable one_le_two` | R2 |
| integral of a finite sum | `rw [integral_finsetSum _ (fun i _ => …)]` | R3 |
| sum of equal terms | `simp [hmean]` → `↑n * m` | R4 |
| cancel `↑n` | `field_simp` | R5 |
| equation of functions | `funext ω; simp [Finset.sum_apply]; ring` | R6–R8 |
| `Var (c · Y)` | `rw [variance_const_mul]` | R9 |
| `Var` of an independent sum | `rw [IndepFun.variance_sum (fun i _ => hL2 i) (fun i _ j _ hij => hindep hij)]` | R10, R11 |
| bound a sum termwise | `Finset.sum_le_sum fun i _ => hvar i` | R12 |
| `0 < ↑n` in `ℝ` | `by exact_mod_cast hn` | R13 |
| monotone step in an inequality | `gcongr` | R14 |
| sample mean is `L²` | `(memLp_finsetSum' _ (fun i _ => hL2 i)).const_mul (↑n)⁻¹`, then `convert … using 1` | R15–R17 |
| Chebyshev | `meas_ge_le_variance_div_sq hY hε` | R18 |
| rewrite a hypothesis | `rw [e] at h` | R19 |
| `dist` → `\|· - ·\|` | `simp only [Real.dist_eq]` | R20 |
| chain `≤` and compare `ofReal`s | `refine h.trans (ENNReal.ofReal_le_ofReal ?_)` | R21, R22 |
| `a / b / c = a / (b * c)` | `rw [div_div]` | R23 |
| convergence in measure | `rw [tendstoInMeasure_iff_dist]; intro ε hε` | R24 |
| `ℝ≥0∞` limit from a real one | `rw [← ENNReal.ofReal_zero]; apply ENNReal.tendsto_ofReal` | R25, R26 |
| `c / n → 0` | `tendsto_const_div_atTop_nhds_zero_nat c` | R27 |
| same limit, termwise-equal sequence | `refine h.congr fun n => ?_` | R28 |
| squeeze | `tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim (Eventually.of_forall fun _ => bot_le) ?_` | R29–R32 |
| eventually, for `n ≥ 1` | `filter_upwards [eventually_ge_atTop 1] with n hn` | R33, R34 |
| see the state | infoview | |
