# M088 · Variance of a 0/1 variable: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033: `have`, `intro`, `rcases` on `∨`, `funext`, `simp`, `<;>`).
**New here:** Mathlib's measure-theoretic probability: measures, the integral `∫ x, f x ∂μ` (expectation),
"almost everywhere" (`∀ᵐ`), closed intervals `Set.Icc`, measurability notions, `MemLp` (the space $L^p$),
and the variance `Var[X; μ]`.

The mathematics. Let $X : \Omega \to \mathbb{R}$ take only the values $0$ and $1$, and let $p = E X$.
Pointwise $X(\omega)^2 = X(\omega)$ (since $0^2 = 0$, $1^2 = 1$), so $E[X^2] = E X = p$ and
$\operatorname{Var} X = E[X^2] - (E X)^2 = p - p^2 = p(1 - p)$.
The formula $\operatorname{Var} X = E[X^2] - (E X)^2$ needs $E[X^2] < \infty$ ($X \in L^2$); here that holds
because $X$ is bounded ($0 \le X \le 1$) on a probability space.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`, or `P : Prop → Prop`). The step changes only the part inside
  `P (…)`, wherever it sits in a larger goal. `G : Prop` is an arbitrary goal that a `have` leaves untouched.
- Placeholders are written as Lean binders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ)`.
  A bracket such as `[IsProbabilityMeasure μ]` is a requirement (a *type class* instance) that Lean finds by
  itself; the exercise provides it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Ω : Type*`, `[MeasurableSpace Ω]` | the sample space with its σ-algebra of measurable sets (`Type*` = a type in any universe) |
| `Ω : Type u_1` | how the infoview prints `Ω : Type*`: `u_1` is the universe variable that `*` introduced |
| `inst✝¹ : MeasurableSpace Ω`, `inst✝ : IsProbabilityMeasure μ` | the unnamed `[…]` arguments of the theorem; `✝` marks a name you cannot type. Lean uses them by itself |
| `μ : Measure Ω` | a measure on `Ω` (`MeasureTheory.Measure`) |
| `[IsProbabilityMeasure μ]` | `μ Ω = 1`. It implies `IsFiniteMeasure μ` (`μ Ω < ∞`), which R6 needs |
| `Measurable X` | preimages of measurable sets under `X` are measurable: `X` is a random variable |
| `AEStronglyMeasurable f μ` | `f` agrees `μ`-almost everywhere with a limit of simple functions; for `ℝ`-valued `f`, implied by `Measurable f` (R5) |
| `∫ (x : Ω), f x ∂μ` | the (Bochner) integral of `f` against `μ`, i.e. the expectation $E f$. It is `0` when `f` is not integrable |
| `μ[X]` | notation for `∫ x, X x ∂μ`. The infoview prints the `∫` form |
| `Var[X; μ]` | `ProbabilityTheory.variance X μ`, the variance $E[(X - E X)^2]$. Neither `simp` nor `ring` opens it; R9 does |
| `MemLp f 2 μ` | `f` is a.e.-strongly measurable and $\int \lvert f\rvert^2\,d\mu < \infty$, i.e. $f \in L^2(\mu)$. The exponent has type `ℝ≥0∞` (`ENNReal`, $[0, \infty]$); `2` is a numeral of that type |
| `∀ᵐ (x : Ω) ∂μ, p x` | `p x` holds for `μ`-almost every `x` (the set where it fails has measure `0`). It is `∀ᶠ x in ae μ, p x`, an "eventually" statement for the filter `ae μ` |
| `Set.Icc a b` | the closed interval `{t | a ≤ t ∧ t ≤ b}` (R3) |
| `f ^ 2`, `(f ^ 2) x` | the function `x ↦ f x ^ 2` (arithmetic acts pointwise on functions), applied to `x` (R8) |
| `1 x` | the constant function `1 : Ω → ℝ` applied to `x`; `simp` turns it into `1` |
| `case inl`, `case inr` | the two goals `rcases … with h \| h` makes: left side of `∨`, right side |

---

## Part 1 · `bernoulli_variance`

Statement: for a probability measure `μ`, a measurable `X : Ω → ℝ` with `X ω = 0 ∨ X ω = 1` for every `ω`,
`Var[X; μ] = μ[X] * (1 - μ[X])`. The plan: prove `X ∈ L²` from the bound `X ω ∈ [0, 1]`, prove the function
equation `X ^ 2 = X`, open the variance with R9, rewrite `X ^ 2` with R10, and let `ring` finish.

### An almost-everywhere bound

`memLp_of_bounded` (R6) wants the bound almost everywhere. Prove it everywhere and weaken.

**R1 · `apply Filter.Eventually.of_forall`** changes the **goal**. Lemma:
`Filter.Eventually.of_forall : (∀ x, p x) → ∀ᶠ x in F, p x` for any filter `F`; with `F = ae μ` this says
"everywhere implies almost everywhere". Term form: `Filter.Eventually.of_forall (fun x => …)`.
Placeholders: `(μ : Measure Ω) (p : Ω → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ᵐ (x : Ω) ∂μ, p x` | `⊢ ∀ (x : Ω), p x` |

Then `intro ω` (TACTIC_STATES) gives a goal at one point.

**R2 · `rcases hpq x with h | h`** changes the **goal list and the context**: `hpq x : p x ∨ q x` splits into
two goals, one with `h : p x`, one with `h : q x`. The `∀` hypothesis is first applied to the point `x`.
Placeholders: `(p q : Ω → Prop) (hpq : ∀ x, p x ∨ q x) (x : Ω)`.

| Before | After |
|---|---|
| `x : Ω ⊢ G` | `h : p x ⊢ G`, `h : q x ⊢ G` |

Follow it with `<;>` to run the same finishing tactic in both goals.

**R3 · `Set.mem_Icc`** changes the **goal**. Lemma: `t ∈ Set.Icc a b ↔ a ≤ t ∧ t ≤ b`. `simp` applies it by
itself (R4). Placeholders: `{α : Type} [Preorder α] (a b t : α)` (α has `≤`; `ℝ`, `ℕ`, `ℤ` qualify).

| Before | After `rw [Set.mem_Icc]` |
|---|---|
| `⊢ P (t ∈ Set.Icc a b)` | `⊢ P (a ≤ t ∧ t ≤ b)` |

**R4 · `simp [h]`** with `h : t = c`, `c` a numeral, **closes** `t ∈ Set.Icc a b` for numerals `a ≤ c ≤ b`:
it rewrites `t` to `c`, applies R3, and decides both inequalities. Placeholders: `(t : ℝ) (h : t = 2)`.

| Before | After `simp [h]` |
|---|---|
| `h : t = 2 ⊢ t ∈ Set.Icc 0 2` | no goals |

### From the bound to `MemLp`

**R5 · `Measurable.aestronglyMeasurable`** changes the **context**. Lemma: `Measurable f → AEStronglyMeasurable f μ`
(for values in a space such as `ℝ`). Write `hm.aestronglyMeasurable`. Placeholders: `(f : Ω → ℝ) (hm : Measurable f)`.

| Before | After `have hs : AEStronglyMeasurable f μ := hm.aestronglyMeasurable` |
|---|---|
| `hm : Measurable f ⊢ G` | `hs : AEStronglyMeasurable f μ ⊢ G` |

**R6 · `memLp_of_bounded`** changes the **context**. Lemma, on a finite measure (`[IsFiniteMeasure μ]`):
`memLp_of_bounded : (∀ᵐ x ∂μ, f x ∈ Set.Icc a b) → AEStronglyMeasurable f μ → ∀ (p : ℝ≥0∞), MemLp f p μ`.
A bounded function on a finite measure space lies in every $L^p$. `a`, `b` are read off the bound's type, so
state that type with explicit numerals: `Set.Icc (0 : ℝ) 1`. Placeholders:
`(f : Ω → ℝ) (a b : ℝ) (hb : ∀ᵐ x ∂μ, f x ∈ Set.Icc a b) (hs : AEStronglyMeasurable f μ)`.

| Before | After `have hL : MemLp f 2 μ := memLp_of_bounded hb hs 2` |
|---|---|
| `hs : AEStronglyMeasurable f μ ⊢ G` | `hL : MemLp f 2 μ ⊢ G` |

### The function equation `X ^ 2 = X`

**R7 · `funext x`** changes the **goal and the context**: an equation between functions becomes the equation at
a fresh point `x`. Placeholders: `(f g : Ω → ℝ)`.

| Before | After |
|---|---|
| `⊢ f ^ 2 = g` | `x : Ω ⊢ (f ^ 2) x = g x` |

Then R2 on the 0/1 hypothesis at `x`, and `simp [h]` in both goals: it applies R8, substitutes `h`, and
evaluates `0 ^ 2`, `1 ^ 2`.

**R8 · `Pi.pow_apply`** changes the **goal**. Lemma: `(f ^ n) x = f x ^ n`. `simp` applies it by itself.
Placeholders: `(f : Ω → ℝ) (x : Ω)`.

| Before | After `rw [Pi.pow_apply]` |
|---|---|
| `⊢ P ((f ^ 2) x)` | `⊢ P (f x ^ 2)` |

### The variance

**R9 · `variance_eq_sub`** changes the **goal**. Lemma (probability measure):
`variance_eq_sub : MemLp f 2 μ → Var[f; μ] = ∫ x, (f ^ 2) x ∂μ - (∫ x, f x ∂μ) ^ 2`, i.e.
$\operatorname{Var} f = E[f^2] - (E f)^2$. Placeholders: `(f : Ω → ℝ) (hf : MemLp f 2 μ)`.

| Before | After `rw [variance_eq_sub hf]` |
|---|---|
| `⊢ P Var[f; μ]` | `⊢ P (∫ (x : Ω), (f ^ 2) x ∂μ - (∫ (x : Ω), f x ∂μ) ^ 2)` |

**R10 · `rw [e]`** with a function equation `e : f ^ 2 = g` changes the **goal**: every `f ^ 2` is replaced, even
inside `∫ x, (f ^ 2) x ∂μ`. `rw` cannot rewrite a term that mentions the bound variable `x`, but the pattern
`f ^ 2` does not mention `x`, so it is reachable. Placeholders: `(f g : Ω → ℝ) (e : f ^ 2 = g)`.

| Before | After `rw [e]` |
|---|---|
| `⊢ P (∫ (x : Ω), (f ^ 2) x ∂μ)` | `⊢ P (∫ (x : Ω), g x ∂μ)` |

**R11 · `ring`** **closes** an identity of commutative rings. Each integral `∫ (x : Ω), X x ∂μ` is one unknown,
and integrals that differ only in the name of the bound variable count as the same unknown.

| Before | After |
|---|---|
| `⊢ u ^ 2 - v ^ 2 = (u - v) * (u + v)` | no goals |

### Worked combinations (W1–W3, on a ±1-valued `g`, not the exercise's `X`)

**W1: `MemLp g 2 μ` for `g ω = -1 ∨ g ω = 1`.** `have hb : ∀ᵐ ω ∂μ, g ω ∈ Set.Icc (-1 : ℝ) 1 := by` R1, `intro ω`,
R2 `<;>` R4; then `exact memLp_of_bounded hb hg.aestronglyMeasurable 2` (R6 with R5):

```lean-goal
⊢ MemLp g 2 μ
```

**W2: `g ^ 2 = 1`** (the constant function `1`). R7, R2, then `all_goals simp [h]`:

```lean-goal
⊢ g ^ 2 = 1
⊢ (g ^ 2) ω = 1 ω
```

**W3: `Var[g; μ] = 1 - (E g)²`.** R9, R10 with `hsq : g ^ 2 = 1`, then `simp` evaluates `∫ x, 1 x ∂μ = 1` on a
probability measure:

```lean-goal
⊢ Var[g; μ] = 1 - (∫ (ω : Ω), g ω ∂μ) ^ 2
⊢ ∫ (x : Ω), (g ^ 2) x ∂μ - (∫ (x : Ω), g x ∂μ) ^ 2 = 1 - (∫ (ω : Ω), g ω ∂μ) ^ 2
⊢ ∫ (x : Ω), 1 x ∂μ - (∫ (x : Ω), g x ∂μ) ^ 2 = 1 - (∫ (ω : Ω), g ω ∂μ) ^ 2
```

---

## Traps

- `variance_eq_sub` needs the proof `MemLp X 2 μ`; there is no way around it, and `Var[X; μ]` does not unfold
  by `simp`. Build `hL2` first.
- Write the bound's type out in the `have`: `have hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1`. R6 reads `a`, `b`
  off that type; without a stated type Lean cannot guess which interval you mean.
- State the square fact as a **function** equation `X ^ 2 = X`, not pointwise `∀ ω, X ω ^ 2 = X ω`. `rw` cannot
  use the pointwise form under `∫ x, …` (the term `X x ^ 2` mentions the bound `x`), and the goal shows
  `(X ^ 2) x`, not `X x ^ 2`.
- `rcases h01 ω with h | h` names both cases `h`; follow it with `<;> simp [h]` so the finishing step runs in both
  goals (`;` would run it in the first one only).
- The banned lemma `variance_of_ae_eq_zero_or_one` is Mathlib's version of this exact theorem.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `∀ᵐ x ∂μ, p x` from a pointwise proof | `apply Filter.Eventually.of_forall` then `intro ω` | R1 |
| split `X ω = 0 ∨ X ω = 1` | `rcases h01 ω with h \| h` | R2 |
| `t ∈ Set.Icc a b` ↔ `a ≤ t ∧ t ≤ b` | `Set.mem_Icc` (inside `simp`) | R3 |
| close `t ∈ Set.Icc 0 1` given `t = 0` or `t = 1` | `simp [h]` | R4 |
| `AEStronglyMeasurable X μ` | `hX.aestronglyMeasurable` | R5 |
| `MemLp X 2 μ` from a bound | `memLp_of_bounded hb hX.aestronglyMeasurable 2` | R6 |
| equation of functions | `funext ω` | R7 |
| `(f ^ n) x` → `f x ^ n` | `Pi.pow_apply` (inside `simp`) | R8 |
| `Var[X; μ]` → `E[X²] - (E X)²` | `rw [variance_eq_sub hL2]` | R9 |
| replace `X ^ 2` under `∫` | `rw [hsq]` with `hsq : X ^ 2 = X` | R10 |
| polynomial identity in the integrals | `ring` | R11 |
| see the state | infoview | |
