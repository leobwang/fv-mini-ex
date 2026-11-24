# M091 · Variance of an independent sum: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's measure-theoretic probability:
measures, the Bochner integral `∫ x, f x ∂μ` (expectation), `Integrable`, `MemLp` (square
integrability), `Var[X; μ]`, independence `X ⟂ᵢ[μ] Y`, and arithmetic on functions (`X + Y`, `X ^ 2`).
M089 uses the same integral rules; this file is self-contained.

The mathematics. For random variables $X, Y$ with $E[X^2], E[Y^2] < \infty$, write $\operatorname{Var} Z = E[Z^2] - (E Z)^2$
and expand $(X+Y)^2 = X^2 + 2XY + Y^2$. Linearity of $E$ gives
$E[(X+Y)^2] = E[X^2] + 2E[XY] + E[Y^2]$ and $E[X+Y] = E X + E Y$. Independence gives $E[XY] = E X \cdot E Y$, so
$\operatorname{Var}(X+Y) = E[X^2] + 2\,E X\,E Y + E[Y^2] - (E X + E Y)^2 = \operatorname{Var} X + \operatorname{Var} Y$.
In Lean, every use of linearity needs proofs that the pieces are integrable; collecting those is most of the work.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp only`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal that a `have` leaves untouched.
- Placeholders are written as Lean binders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g u v : Ω → ℝ)`.
  A bracket such as `[IsProbabilityMeasure μ]` is a requirement (a *type class* instance) that Lean finds
  by itself; the exercise provides it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Ω : Type*`, `[MeasurableSpace Ω]` | the sample space, with a σ-algebra of measurable sets (`Type*` = a type in any universe) |
| `μ : Measure Ω` | a measure on `Ω` |
| `[IsProbabilityMeasure μ]` | `μ Ω = 1`; it implies `IsFiniteMeasure μ`, which R1 needs |
| `X : Ω → ℝ` | a real random variable (measurability is part of `MemLp` / `Integrable`, not a separate hypothesis) |
| `∫ (x : Ω), f x ∂μ` | the integral of `f` against `μ` = the expectation $E f$. It is `0` when `f` is not integrable (a "junk value") |
| `μ[f]` | notation for `∫ x, f x ∂μ`. The infoview always prints the `∫` form |
| `∫ (x : Ω), (fun x => f x * g x) x ∂μ` | how `μ[fun x => f x * g x]` is printed: the function applied to `x`. It equals `∫ x, f x * g x ∂μ` by one beta step, and `rw` treats them as the same (W3) |
| `∫ (a : Ω), u a ∂μ` | the same integral as `∫ (x : Ω), u x ∂μ`; rewriting renames the bound variable |
| `Integrable f μ` | `f` is (a.e.-strongly) measurable and $\int \lvert f\rvert\,d\mu < \infty$, i.e. $f \in L^1(\mu)$ |
| `MemLp f 2 μ` | `f` is measurable and $\int \lvert f\rvert^2\,d\mu < \infty$, i.e. $f \in L^2(\mu)$. The exponent `2` has type `ℝ≥0∞` (`ENNReal`, the extended reals $[0, \infty]$), so `one_le_two` in R1 is the fact `(1 : ℝ≥0∞) ≤ 2` |
| `(∫ (x : Ω), f x ∂μ) * ∫ (x : Ω), g x ∂μ` | a product of two integrals. `∫ x, …` extends right up to its `∂μ`, so Lean parenthesizes an integral only when something follows it |
| `AEStronglyMeasurable f μ` | `f` agrees `μ`-almost everywhere with a limit of simple functions; for `ℝ`-valued `f` this is "a.e.-measurable" |
| `Var[X; μ]` | `ProbabilityTheory.variance X μ`, the variance $E[(X - E X)^2]$ |
| `X ⟂ᵢ[μ] Y` | `ProbabilityTheory.IndepFun X Y μ`: `X` and `Y` are independent under `μ` |
| `f + g`, `f * g`, `f ^ 2` | functions `Ω → ℝ` combined pointwise: `(f + g) x = f x + g x`, `(f * g) x = f x * g x`, `(f ^ 2) x = f x ^ 2` (R8) |
| `((u + v) ^ 2) x` | the function `(u + v) ^ 2` applied to `x`; R8 turns it into `(u x + v x) ^ 2` |

---

## Part 1 · `variance_add_indep`

Statement: for a probability measure `μ`, `X, Y ∈ L²(μ)` independent, `Var[X + Y; μ] = Var[X; μ] + Var[Y; μ]`.
The plan: collect the integrability and independence facts as `have`s, state the pointwise identity
`(X + Y)² = X² + 2XY + Y²` as an equation of functions, open the three variances, split the integrals, replace
`E[XY]`, and let `ring` finish.

### Facts from `MemLp` and independence

All of these change the **context** only.

**R1 · `MemLp.integrable`** changes the **context**. Lemma: `1 ≤ q → MemLp f q μ → Integrable f μ` on a finite
measure ($L^q \subset L^1$ when `μ` is finite). Write `hf.integrable one_le_two`; `one_le_two : 1 ≤ 2` is the side
condition. Placeholders: `(μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : MemLp f 2 μ)`.

| Before | After `have hi : Integrable f μ := hf.integrable one_le_two` |
|---|---|
| `hf : MemLp f 2 μ ⊢ G` | `hi : Integrable f μ ⊢ G` |

**R2 · `MemLp.aestronglyMeasurable`** changes the **context**. Lemma: `MemLp f p μ → AEStronglyMeasurable f μ`
(the measurability part of `MemLp`). R3 needs it for both variables. Placeholders: `(f : Ω → ℝ) (hf : MemLp f 2 μ)`.

| Before | After `have hm : AEStronglyMeasurable f μ := hf.aestronglyMeasurable` |
|---|---|
| `hf : MemLp f 2 μ ⊢ G` | `hm : AEStronglyMeasurable f μ ⊢ G` |

**R3 · `IndepFun.integral_mul_eq_mul_integral`** changes the **context**: it adds $E[fg] = E f \cdot E g$. Lemma:
`f ⟂ᵢ[μ] g → AEStronglyMeasurable f μ → AEStronglyMeasurable g μ → ∫ x, (f * g) x ∂μ = (∫ x, f x ∂μ) * ∫ x, g x ∂μ`.
Use dot notation on the independence hypothesis: `hfg.integral_mul_eq_mul_integral hfm hgm`. Left alone (`h₀`) the
product is the function `f * g`; stating the type in `fun` form (`h₁`) gives the same fact with the integrand
`fun x => f x * g x`, the form that R13 leaves in the goal. Placeholders: `(f g : Ω → ℝ) (hfg : f ⟂ᵢ[μ] g)
(hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)`.

| Before | After (goal unchanged) | The context gains |
|---|---|---|
| `hfg : f ⟂ᵢ[μ] g ⊢ G` | `hfg : f ⟂ᵢ[μ] g ⊢ G` | after `have h₀ := …`: `h₀ : ∫ (x : Ω), (f * g) x ∂μ = (∫ (x : Ω), f x ∂μ) * ∫ (x : Ω), g x ∂μ` |
| | | after `have h₁ : μ[fun x => f x * g x] = μ[f] * μ[g] := …`: `h₁ : ∫ (x : Ω), (fun x => f x * g x) x ∂μ = (∫ (x : Ω), f x ∂μ) * ∫ (x : Ω), g x ∂μ` |

### Integrability of the pieces

`(X + Y)² = X² + 2XY + Y²` has three pieces, and `integral_add` (R12) needs each one integrable, in the `fun`
form that appears in the integrand.

**R4 · `MemLp.integrable_sq`** changes the **context**. Lemma: `MemLp f 2 μ → Integrable (fun x => f x ^ 2) μ`
(the square of an $L^2$ function is in $L^1$). Placeholders: `(f : Ω → ℝ) (hf : MemLp f 2 μ)`.

| Before | After `have hs : … := hf.integrable_sq` |
|---|---|
| `hf : MemLp f 2 μ ⊢ G` | `hs : Integrable (fun x => f x ^ 2) μ ⊢ G` |

**R5 · `MemLp.integrable_mul`** changes the **context**. Lemma: `MemLp f p μ → MemLp g q μ → Integrable (f * g) μ`
when $1/p + 1/q = 1$ (Hölder's inequality; Lean proves that side condition for `p = q = 2` itself, as an instance).
Placeholders: `(f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)`.

| Before | After `have hp : Integrable (f * g) μ := hf.integrable_mul hg` |
|---|---|
| `hg : MemLp g 2 μ ⊢ G` | `hp : Integrable (f * g) μ ⊢ G` |

**R6 · `Integrable.const_mul`** changes the **context**. Lemma: `Integrable u μ → ∀ c, Integrable (fun x => c * u x) μ`.
Placeholders: `(u : Ω → ℝ) (hu : Integrable u μ) (c : ℝ)`. Chained after R5, `(hf.integrable_mul hg).const_mul 2`
proves `Integrable (fun x => 2 * (f x * g x)) μ`: `(f * g) x` and `f x * g x` agree by unfolding, so the stated
type is accepted.

| Before | After `have hc : … := hu.const_mul c` |
|---|---|
| `hu : Integrable u μ ⊢ G` | `hc : Integrable (fun x => c * u x) μ ⊢ G` |

**R7 · `Integrable.add`** changes the **context**. Lemma: `Integrable u μ → Integrable v μ → Integrable (u + v) μ`.
Without a stated type you get the sum of *functions* `u + v` (`h₀`); `rw [integral_add …]` then looks for the
integrand `fun a => (u + v) a` and fails. State the type in `fun` form (`h₁`). Placeholders:
`(u v : Ω → ℝ) (hu : Integrable u μ) (hv : Integrable v μ)`.

| Before | After `have h₀ := hu.add hv` | After `have h₁ : Integrable (fun x => u x + v x) μ := hu.add hv` |
|---|---|---|
| `hv : Integrable v μ ⊢ G` | `h₀ : Integrable (u + v) μ ⊢ G` | `h₁ : Integrable (fun x => u x + v x) μ ⊢ G` |

In the exercise, the left piece of `X² + 2XY + Y²` is `X² + 2XY` (`+` groups to the left), so you need
`Integrable (fun ω => X ω ^ 2 + 2 * (X ω * Y ω)) μ` from R4 and R6 via R7.

### Pointwise operations on functions

**R8 · `Pi.pow_apply`, `Pi.add_apply`** change the **goal**. Lemmas: `Pi.pow_apply : (u ^ n) x = u x ^ n` and
`Pi.add_apply : (u + v) x = u x + v x` (`Pi` is Mathlib's name for function types; these say that `^`, `+` on
functions act pointwise). Use them with `simp only [Pi.pow_apply, Pi.add_apply]`: `simp` rewrites under the bound
variable of `∫ x, …` and `fun x => …`, where `rw` cannot. Placeholders: `(u v : Ω → ℝ) (x : Ω)`.

| Before | After `simp only [Pi.pow_apply]` | After `simp only [Pi.add_apply]` |
|---|---|---|
| `⊢ P (((u + v) ^ 2) x)` | `⊢ P ((u + v) x ^ 2)` | `⊢ P ((u x + v x) ^ 2)` |

The integrand identity is proved with `funext ω` (TACTIC_STATES, "Extensionality"), R8, then `ring` (W1).

### Variance and the integral rules

**R9 · `MemLp.add`** gives `MemLp (f + g) 2 μ` (the **context** gains it if you use `have`). Lemma:
`MemLp f p μ → MemLp g p μ → MemLp (f + g) p μ`. It is the hypothesis R10 needs for `Var[f + g; μ]`; write it inline,
`variance_eq_sub (hf.add hg)`. Placeholders: `(f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)`.

| Before | After `have hs : MemLp (f + g) 2 μ := hf.add hg` |
|---|---|
| `hg : MemLp g 2 μ ⊢ G` | `hs : MemLp (f + g) 2 μ ⊢ G` |

**R10 · `rw [variance_eq_sub hf]`** changes the **goal**. Lemma (probability measure):
`MemLp f 2 μ → Var[f; μ] = ∫ x, (f ^ 2) x ∂μ - (∫ x, f x ∂μ) ^ 2`. Use it three times, once per variance, with the
matching `MemLp` proof. Placeholders: `[IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : MemLp f 2 μ)`.

| Before | After |
|---|---|
| `⊢ P Var[f; μ]` | `⊢ P (∫ (x : Ω), (f ^ 2) x ∂μ - (∫ (x : Ω), f x ∂μ) ^ 2)` |

**R11 · `rw [e]`** with an equation of functions changes the **goal**: the whole integrand is replaced. The integral
`∫ x, (F ^ 2) x ∂μ` integrates the function `fun x => (F ^ 2) x`, so an `e` whose left side is exactly that function
rewrites it. In the exercise, `F` is `X + Y` and the right side of `e` is the expanded square. Placeholders:
`(F : Ω → ℝ) (e : (fun x => (F ^ 2) x) = fun x => F x * F x)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : Ω), (F ^ 2) x ∂μ)` | `⊢ P (∫ (x : Ω), F x * F x ∂μ)` |

**R12 · `rw [integral_add hu hv]`** changes the **goal**. Lemma:
`Integrable u μ → Integrable v μ → ∫ a, u a + v a ∂μ = ∫ a, u a ∂μ + ∫ a, v a ∂μ`. `rw` looks for the integrand
`fun a => u a + v a` with `u`, `v` read off `hu`, `hv`, so their types must be in `fun` form (R7). For
`X² + 2XY + Y²` split the outer `+` first (pieces `X² + 2XY` and `Y²`), then the inner one. Placeholders:
`(u v : Ω → ℝ) (hu : Integrable u μ) (hv : Integrable v μ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : Ω), u x + v x ∂μ)` | `⊢ P (∫ (a : Ω), u a ∂μ + ∫ (a : Ω), v a ∂μ)` |

**R13 · `rw [integral_const_mul]`** changes the **goal**. Lemma: `∫ a, r * u a ∂μ = r * ∫ a, u a ∂μ` (no
integrability needed). Placeholders: `(u : Ω → ℝ) (r : ℝ)`. After it, the cross term is `2 * ∫ a, X a * Y a ∂μ`,
which `rw [hprod]` (the R3 fact) replaces by `2 * (μ[X] * μ[Y])`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : Ω), r * u x ∂μ)` | `⊢ P (r * ∫ (a : Ω), u a ∂μ)` |

### Finishing

After the rewrites, the goal still contains `(X + Y) x` inside `(∫ x, (X + Y) x ∂μ) ^ 2` and `(X ^ 2) x` on the
right. `simp only [Pi.add_apply, Pi.pow_apply]` (R8) on the whole goal turns them into `X x + Y x` and `X x ^ 2`,
`rw [integral_add hXi hYi]` (R12 with R1's facts) splits `E[X + Y]`, and `ring` closes the identity, treating each
`∫ …` as an unknown.

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: an integrand identity, `(f - g)² = f² - 2fg + g²`.** `funext x` gives a pointwise goal; R8 with
`Pi.sub_apply : (u - v) x = u x - v x` unfolds the function arithmetic; `ring` closes it:

```lean-goal
⊢ (fun x => ((f - g) ^ 2) x) = fun x => f x ^ 2 - 2 * (f x * g x) + g x ^ 2
⊢ ((f - g) ^ 2) x = f x ^ 2 - 2 * (f x * g x) + g x ^ 2
⊢ (f x - g x) ^ 2 = f x ^ 2 - 2 * (f x * g x) + g x ^ 2
```

**W2: split `E[f² + 3fg]`.** `i1` from R4, `i2` from R5 then R6, then R12 and R13:

```lean-goal
⊢ ∫ (x : Ω), f x ^ 2 + 3 * (f x * g x) ∂μ = ∫ (x : Ω), f x ^ 2 ∂μ + 3 * ∫ (x : Ω), f x * g x ∂μ
⊢ ∫ (a : Ω), f a ^ 2 ∂μ + ∫ (a : Ω), 3 * (f a * g a) ∂μ = ∫ (x : Ω), f x ^ 2 ∂μ + 3 * ∫ (x : Ω), f x * g x ∂μ
```

The last `rw [integral_const_mul]` makes both sides identical, and `rw` closes the goal with `rfl`.

**W3: using the independence fact.** `hp` from R2 and R3, then `rw [hp]` replaces `∫ x, f x * g x ∂μ`, and `ring`:

```lean-goal
⊢ 2 * ∫ (x : Ω), f x * g x ∂μ - (∫ (x : Ω), f x ∂μ) * ∫ (x : Ω), g x ∂μ = (∫ (x : Ω), f x ∂μ) * ∫ (x : Ω), g x ∂μ
⊢ 2 * ((∫ (x : Ω), f x ∂μ) * ∫ (x : Ω), g x ∂μ) - (∫ (x : Ω), f x ∂μ) * ∫ (x : Ω), g x ∂μ = (∫ (x : Ω), f x ∂μ) * ∫ (x : Ω), g x ∂μ
```

---

## Traps

- `rw [integral_add hf hg]` fires only if `hf : Integrable (fun ω => …) μ` has the integrand's exact `fun` shape.
  `i1.add i2` without a stated type is `Integrable (u + v) μ` (R7): state the type.
- Split `∫ (A + B + C)` from the outside: `+` groups to the left, so the first `integral_add` needs proofs for
  `A + B` and `C`, the second for `A` and `B`.
- `rw` cannot rewrite under `∫ x, …` or `fun x => …` (the bound `x`); use `simp only [Pi.add_apply, Pi.pow_apply]`.
- After `rw [variance_eq_sub …]` the goal says `(X ^ 2) x` and `(X + Y) x`. Run the `simp only` (R8) on the whole
  goal before `ring`, or `ring` sees `∫ x, (X ^ 2) x ∂μ` and `∫ a, X a ^ 2 ∂μ` as two different unknowns.
- `R1` needs a finite measure; `[IsProbabilityMeasure μ]` provides it. Without it, `hf.integrable one_le_two` fails
  to find an instance.
- `have h : T` with no `:= …` makes `T` your next goal instead of adding `h` (TACTIC_STATES, "Adding facts").

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `Integrable X μ` from `MemLp X 2 μ` | `hX.integrable one_le_two` | R1 |
| measurability from `MemLp` | `hX.aestronglyMeasurable` | R2 |
| $E[XY] = E X\,E Y$ | `have : μ[fun ω => X ω * Y ω] = μ[X] * μ[Y] := hXY.integral_mul_eq_mul_integral … …` | R3 |
| `Integrable (fun ω => X ω ^ 2) μ` | `hX.integrable_sq` | R4 |
| `Integrable (X * Y) μ` | `hX.integrable_mul hY` | R5 |
| `Integrable (fun ω => c * u ω) μ` | `hu.const_mul c` | R6 |
| `Integrable (fun ω => u ω + v ω) μ` | `have : Integrable (fun ω => u ω + v ω) μ := hu.add hv` | R7 |
| `((u + v) ^ 2) x → (u x + v x) ^ 2` | `simp only [Pi.pow_apply, Pi.add_apply]` | R8 |
| `MemLp (X + Y) 2 μ` | `hX.add hY` | R9 |
| `Var[Z; μ] → E[Z²] - (E Z)²` | `rw [variance_eq_sub hZ]` | R10 |
| replace an integrand | `rw [e]`, `e : (fun ω => …) = fun ω => …` (prove with `funext ω`) | R11 |
| `∫ (u + v) → ∫ u + ∫ v` | `rw [integral_add hu hv]` | R12 |
| `∫ r * u → r * ∫ u` | `rw [integral_const_mul]` | R13 |
| close an identity of expectations | `ring` | |
| see the state | infoview | |
