# M099 · Central limit theorem for coin flips: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's measure-theoretic probability:
measures and "almost everywhere", expectation `P[f]` (a Lebesgue integral), variance `Var[X; P]`,
square-integrability `MemLp`, independence, identical distribution, the law of a random variable
(`HasLaw`), the real Gaussian `gaussianReal`, convergence in distribution, and the CLT lemma
`tendstoInDistribution_inv_sqrt_mul_sum_sub`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`refine`/as a term. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `Q` is "the rest of your goal" (`Q : α → Prop`). The step changes only the part inside `Q (…)`.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as
  `[MeasurableSpace α]` is a requirement on `α` (a *type class*); each entry says which ones it needs.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `{Ω Ω' : Type*}`, printed `Ω : Type u_1` | `Ω` is any type; `u_1` is a universe level Lean picked, read it as plain `Type` |
| `inst✝¹ : IsProbabilityMeasure P` | an unnamed instance hypothesis from a `[…]` binder; `✝` marks a name you cannot refer to, and the code finds it by itself |
| `[MeasurableSpace Ω]` | `Ω` carries a σ-algebra (which sets are measurable). `ℝ` has the Borel one built in |
| `P : Measure Ω` | a measure on `Ω`; `[IsProbabilityMeasure P]` says `P Ω = 1`, so `P` is a probability |
| `[IsFiniteMeasure μ]` | `μ Ω < ∞`; every probability measure is one |
| `X : ℕ → Ω → ℝ` | a sequence of real random variables: `X i` is the `i`-th, `X i ω` its value at outcome `ω` |
| `Measurable f` | preimages of Borel sets under `f` are measurable (`f` is a random variable) |
| `AEStronglyMeasurable f μ` | `f` equals a limit of simple functions outside a `μ`-null set; follows from `Measurable f` (R5) |
| `∀ᵐ x ∂μ, Q x` | `Q x` holds for `μ`-almost every `x`: the set where it fails has measure 0 |
| `∀ᶠ x in l, Q x` | `Q x` holds eventually along the filter `l` (`Filter.Eventually`); `∀ᵐ x ∂μ` is this with `l` the a.e. filter of `μ` (R1) |
| `Set.Icc a b` | the closed interval `[a, b] = {x \| a ≤ x ∧ x ≤ b}` (R3) |
| `MemLp f p μ` | `f` is in $L^p(\mu)$: measurable enough and $\int \lvert f\rvert^p\,d\mu < \infty$. `MemLp f 2 μ`: square-integrable. `p` has type `ℝ≥0∞` (`[0, ∞]`); the numeral `2` is read there |
| `P[f]`, printed `∫ (x : Ω), f x ∂P` | the expectation $\mathbb E_P[f] = \int f\,dP$ (Bochner integral). You write `P[X 0]`; Lean prints the integral |
| `f ^ 2` with `f : Ω → ℝ` | the function `ω ↦ f ω ^ 2` (operations on functions are pointwise, R7) |
| `Var[X; P]` | the variance $\int (X - \mathbb E_P X)^2\,dP$ |
| `iIndepFun X P` | the family `X 0, X 1, …` is mutually independent under `P` |
| `IdentDistrib (X i) (X 0) P P` | `X i` under `P` has the same law (distribution) as `X 0` under `P` |
| `ℝ≥0` | `NNReal`, the type of reals `≥ 0` |
| `x.toNNReal` | `max x 0` as an `ℝ≥0` (Mathlib's `Real.toNNReal`) |
| `gaussianReal m v` | the Gaussian measure $N(m, v)$ on `ℝ`; mean `m : ℝ`, variance `v : ℝ≥0` |
| `HasLaw Y μ P'` | the law of `Y` under `P'` is `μ`, i.e. the push-forward `P' ∘ Y⁻¹` equals `μ` |
| `TendstoInDistribution Z l Y (fun _ => P) P'` | `Z n` (on `(Ω, P)`) converges in distribution to `Y` (on `(Ω', P')`) along the filter `l`: their laws converge weakly |
| `Filter.atTop` | the filter "`n → ∞`" on `ℕ` |
| `Finset.range n`, `∑ k ∈ Finset.range n, f k` | `{0, …, n-1}` and `f 0 + … + f (n-1)` |
| `↑n`, `√↑n` | `n : ℕ` cast into `ℝ`, and its real square root `Real.sqrt` |
| `fun x => P` | the constant family `fun _ => P`: every `Z n` lives on the same space `(Ω, P)` |
| `case inl`, `case inr` | the two goals `rcases` makes from `A ∨ B` (left / right) |
| `case refine_1`, … | the goals `refine` makes, one per `?_`, in order |
| `?m.70` | a metavariable: a term Lean has not determined yet; the number varies (Traps) |
| `this : …` | the fact stored by an unnamed `have := t` |

---

## Part 1 · `clt_coin`

Statement: `X 0, X 1, …` are independent, identically distributed, measurable, and take only the values
0 and 1; `P[X 0] = p`; `Y` has law $N(0, p(1-p))$. Then
$(\sqrt n)^{-1}\bigl(\sum_{k<n} X_k - n p\bigr) \to Y$ in distribution (de Moivre–Laplace).

The CLT lemma (R10) already proves this with `P[X 0]` in place of `p` and `Var[X 0; P]` in place of
`p * (1 - p)`. You supply its two missing inputs: `MemLp (X 0) 2 P` (R1–R5) and
`Var[X 0; P] = p * (1 - p)` (R6–R8), then fit `hY` (R9) and replace the mean (R11).

### A pointwise fact → an almost-everywhere fact

**R1 · `Filter.Eventually.of_forall`** changes the **goal**: `∀ᵐ x ∂μ, Q x` becomes `∀ x, Q x` (every point
is in particular almost every point). Statement: `(∀ x, Q x) → ∀ᶠ x in l, Q x` for any filter `l`; `∀ᵐ x ∂μ` is the
case where `l` is the a.e. filter of `μ`. Placeholders: `{α : Type} [MeasurableSpace α] (μ : Measure α)
(Q : α → Prop)`. As a term: `Filter.Eventually.of_forall fun x => by …`.

| Before | After `apply Filter.Eventually.of_forall` |
|---|---|
| `⊢ ∀ᵐ (x : α) ∂μ, Q x` | `⊢ ∀ (x : α), Q x` |

**R2 · `rcases h with h | h`** changes the **goal list and the context**: `h : A ∨ B` is split into two
goals, one with `h : A` (`case inl`) and one with `h : B` (`case inr`). Placeholders:
`{α : Type} (x a b : α) (Q : α → Prop)`. Follow with `<;> simp [h]` to treat both cases alike.

| Before | After |
|---|---|
| `h : x = a ∨ x = b ⊢ Q x` | `h : x = a ⊢ Q x`, `h : x = b ⊢ Q x` |

**R3 · `Set.mem_Icc`** changes the **goal**. Statement: `x ∈ Set.Icc a b ↔ a ≤ x ∧ x ≤ b`. Placeholders:
`(x a b : ℝ)` (any `[Preorder α]` works). `simp` applies it by itself, so `simp [h]` with `h : x = 0` turns
`x ∈ Set.Icc 0 1` into `0 ≤ 0 ∧ 0 ≤ 1` and closes it.

| Before | After `rw [Set.mem_Icc]` |
|---|---|
| `⊢ x ∈ Set.Icc a b` | `⊢ a ≤ x ∧ x ≤ b` |

### Square-integrability

**R4 · `memLp_of_bounded`** changes the **goal list**. Statement: for `[IsFiniteMeasure μ]`,
`(∀ᵐ x ∂μ, f x ∈ Set.Icc a b) → AEStronglyMeasurable f μ → ∀ p, MemLp f p μ`: a bounded measurable function
is in every $L^p$. Placeholders: `{α : Type} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
(f : α → ℝ) (a b : ℝ)`. As a term: `memLp_of_bounded hb hm 2`.

| Before | After `refine memLp_of_bounded (a := a) (b := b) ?_ ?_ 2` |
|---|---|
| `⊢ MemLp f 2 μ` | `⊢ ∀ᵐ (x : α) ∂μ, f x ∈ Set.Icc a b`, `⊢ AEStronglyMeasurable f μ` |

**R5 · `Measurable.aestronglyMeasurable`** changes the **goal**. Statement: `Measurable f →
AEStronglyMeasurable f μ` (for `f` into `ℝ`, or any second-countable metrizable space). Placeholders:
`{α : Type} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)`. With `hm : Measurable f` the term is
`hm.aestronglyMeasurable`; for `hmeas : ∀ i, Measurable (X i)` it is `(hmeas 0).aestronglyMeasurable`.

| Before | After `apply Measurable.aestronglyMeasurable` |
|---|---|
| `⊢ AEStronglyMeasurable f μ` | `⊢ Measurable f` |

### Equations between functions

**R6 · `funext x`** changes the **goal and the context**: an equation of functions becomes the equation of
their values at a new point `x`. Placeholders: `{α : Type} (f g : α → ℝ)`.

| Before | After |
|---|---|
| `⊢ f = g` | `x : α ⊢ f x = g x` |

**R7 · `Pi.pow_apply`** changes the **goal**. Statement: `(f ^ n) x = f x ^ n`. Placeholders:
`{α : Type} (f : α → ℝ) (n : ℕ) (x : α)`. `simp` applies it by itself, so after R6 on `f ^ 2 = f`,
`simp [h]` with `h : f x = 0` (or `= 1`) closes `(f ^ 2) x = f x`.

| Before | After `rw [Pi.pow_apply]` |
|---|---|
| `⊢ Q ((f ^ n) x)` | `⊢ Q (f x ^ n)` |

### Variance

**R8 · `variance_eq_sub`** changes the **goal**. Statement: for `[IsProbabilityMeasure μ]`,
`MemLp ξ 2 μ → Var[ξ; μ] = μ[ξ ^ 2] - μ[ξ] ^ 2`, i.e. $\operatorname{Var}\xi = \mathbb E[\xi^2] - (\mathbb E\xi)^2$.
Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Ω → ℝ)
(hξ : MemLp ξ 2 μ)`. After it, `rw [hsq]` with `hsq : ξ ^ 2 = ξ` and `rw [hp]` with `hp : μ[ξ] = p`
leave a polynomial identity in `p` for `ring`.

| Before | After `rw [variance_eq_sub hξ]` |
|---|---|
| `⊢ Q Var[ξ; μ]` | `⊢ Q (∫ (x : Ω), (ξ ^ 2) x ∂μ - (∫ (x : Ω), ξ x ∂μ) ^ 2)` |

### Fitting a hypothesis, the CLT, closing

**R9 · `rwa [h]`** **closes** the goal: `rw [h]`, then `assumption` (a hypothesis that matches the new goal).
Here `h : v = w` turns the variance `v` in a Gaussian law into `w`, the form `hZ` has. Placeholders:
`{Ω' : Type} [MeasurableSpace Ω'] (μ' : Measure Ω') (Z : Ω' → ℝ) (v w : ℝ)`.

| Before | After |
|---|---|
| `hZ : HasLaw Z (gaussianReal 0 w.toNNReal) μ' ⊢ HasLaw Z (gaussianReal 0 v.toNNReal) μ'` | closed |

**R10 · `tendstoInDistribution_inv_sqrt_mul_sum_sub`** (the CLT) changes the **goal list**. Statement:
for probability measures `μ` on `Ω` and `μ'` on `Ω'`, `ξ : ℕ → Ω → ℝ` and `Z : Ω' → ℝ`,

```
HasLaw Z (gaussianReal 0 Var[ξ 0; μ].toNNReal) μ' → MemLp (ξ 0) 2 μ → iIndepFun ξ μ →
  (∀ i, IdentDistrib (ξ i) (ξ 0) μ μ) →
  TendstoInDistribution (fun n ω => (√↑n)⁻¹ * (∑ k ∈ Finset.range n, ξ k ω - ↑n * μ[ξ 0]))
    Filter.atTop Z (fun _ => μ) μ'
```

All of `Ω Ω' μ μ' ξ Z` are implicit: Lean reads them off the arguments, so its first argument must
already mention your `Y` and `P'`. As a term: `tendstoInDistribution_inv_sqrt_mul_sum_sub hZ h2 hind hid`;
`have := …` stores the conclusion as `this`.

| Before | After `refine tendstoInDistribution_inv_sqrt_mul_sum_sub ?_ ?_ ?_ ?_` |
|---|---|
| `⊢ TendstoInDistribution (fun n ω => (√↑n)⁻¹ * (∑ k ∈ Finset.range n, ξ k ω - ↑n * ∫ (x : Ω), ξ 0 x ∂μ)) Filter.atTop Z (fun x => μ) μ'` | `⊢ HasLaw Z (gaussianReal 0 Var[ξ 0; μ].toNNReal) μ'`, `⊢ MemLp (ξ 0) 2 μ`, `⊢ iIndepFun ξ μ`, `⊢ ∀ (i : ℕ), IdentDistrib (ξ i) (ξ 0) μ μ` |

**R11 · `simpa [h] using t`** **closes** the goal: it simplifies `t` and the goal with `h` (plus the
default `simp` set) and closes the goal with the simplified `t`. Use it when `t` is the goal except that
one side still has `μ[ξ]` where the other has `m`. Placeholders: `{Ω : Type} [MeasurableSpace Ω]
(μ : Measure Ω) (ξ : Ω → ℝ) (m : ℝ) (hm : μ[ξ] = m)`.

In the context: `hm : ∫ (x : Ω), ξ x ∂μ = m` and `t : Q (∫ (x : Ω), ξ x ∂μ)`.

| Before | After |
|---|---|
| `⊢ Q m` | closed |

### Worked combinations (W1–W3, on ±1-valued signs, not the exercise's coin flips)

**W1.** `f ω = -1 ∨ f ω = 1` for all `ω` gives `∀ᵐ ω ∂μ, f ω ∈ Set.Icc (-1 : ℝ) 1` by the term
`Filter.Eventually.of_forall fun ω => by rcases hf ω with h | h <;> simp [h]` (R1, R2, R3).

**W2.** Its variance: `memLp_of_bounded hb hm.aestronglyMeasurable 2` (R4, R5); `hsq : f ^ 2 = 1` by
`funext ω` and the same case split (R6, R7); then `rw [variance_eq_sub hL2, hsq, hm0]` (R8) leaves

```lean-goal
⊢ ∫ (x : Ω), 1 x ∂μ - m ^ 2 = 1 - m ^ 2
```

which `simp` closes (`1 x` is the constant function `1` at `x`, and a probability measure integrates `1`
to `1`).

**W3.** Mean 0, variance 1: first `hZ' : HasLaw Z (gaussianReal 0 Var[ξ 0; μ].toNNReal) μ'` from
`hZ : HasLaw Z (gaussianReal 0 1) μ'` by `simpa [hv] using hZ`, then
`have := tendstoInDistribution_inv_sqrt_mul_sum_sub hZ' h2 hind hid` (R10) and
`simpa [hm0] using this` (R11), which also removes the `- ↑n * 0`.

---

## Traps

- Lean prints `P[X 0]` as `∫ (x : Ω), X 0 x ∂P`. Your `hp` reads `hp : ∫ (x : Ω), X 0 x ∂P = p`; `rw [hp]`
  and `simpa [hp]` still find it.
- `X 0 ^ 2` is a power of a **function**, so `X 0 ^ 2 = X 0` is an equation of functions: prove it with
  `funext ω` first (R6), then the case split. It holds pointwise because the values are 0 or 1 (`0² = 0`,
  `1² = 1`); that is what turns `variance_eq_sub` into `p - p ^ 2`.
- `R8` rewrites `Var[X 0; P]` only where it appears literally: state `hvar` with `Var[X 0; P]` on the left.
- An inline `(by rwa [hvar])` as the CLT's first argument sees a goal like `HasLaw ?m.70 (gaussianReal 0
  Var[X 0; P].toNNReal) ?m.68` (the numbers vary): `Y` and `P'` are not yet known. `rwa`'s `assumption` step fills them from
  `hY`. A separate `have hY' : HasLaw Y (gaussianReal 0 Var[X 0; P].toNNReal) P' := by rwa [hvar]` is
  clearer.
- `have := t` (no name) stores `t` as `this`.
- `rcases h with h | h ; simp [h]` runs `simp` on the first case only. Use `<;>` (TACTIC_STATES).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| a.e. fact from a pointwise one | `Filter.Eventually.of_forall fun ω => by …` | R1 |
| split `h : A ∨ B` | `rcases h with h \| h <;> simp [h]` | R2 |
| `x ∈ Set.Icc a b` | `simp [h]`, or `rw [Set.mem_Icc]` | R3 |
| `MemLp f 2 μ` for bounded `f` | `memLp_of_bounded hb hm.aestronglyMeasurable 2` | R4, R5 |
| equation of functions | `funext ω` | R6 |
| `(f ^ n) x` → `f x ^ n` | `simp` / `rw [Pi.pow_apply]` | R7 |
| `Var[ξ; μ]` → `μ[ξ ^ 2] - μ[ξ] ^ 2` | `rw [variance_eq_sub hL2]` | R8 |
| polynomial identity in `p` | `ring` | TACTIC_STATES |
| rewrite, then close with a hypothesis | `rwa [h]` | R9 |
| the CLT | `tendstoInDistribution_inv_sqrt_mul_sum_sub hZ h2 hind hid` | R10 |
| conclusion up to `μ[ξ] = m` | `simpa [hm] using this` | R11 |
| see the state | infoview | |
