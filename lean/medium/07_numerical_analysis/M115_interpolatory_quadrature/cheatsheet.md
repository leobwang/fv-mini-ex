# M115 · Interpolatory quadrature is exact: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's polynomials `ℝ[X]` and their
evaluation, Lagrange interpolation (`Lagrange.interpolate`, `Lagrange.basis`), finite sums over a
`Finset`, the interval integral `∫ x in a..b, f x` and interval integrability, and `conv` mode.

**The math.** For distinct nodes `v i` (`i ∈ s`, `n = s.card` of them) the Lagrange basis polynomial
$L_i = \prod_{j \in s, j \ne i} \frac{X - v_j}{v_i - v_j}$ has degree $n-1$ and $L_i(v_j) = [i = j]$.
Every polynomial $p$ of degree $< n$ equals its interpolant: $p = \sum_{i \in s} p(v_i)\,L_i$. Integrate both
sides over $[a, b]$ and swap $\int$ with the finite $\sum$:
$\int_a^b p = \sum_i p(v_i) \int_a^b L_i = \sum_i w_i\, p(v_i)$ with weights $w_i = \int_a^b L_i$.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp only`/`apply`. It says what changes (**goal**,
**context**, or **goal list**), gives the lemma's statement, lists the placeholders with their types, then
shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Field F]` is a
  requirement on the type (a *type class*). Each entry says which familiar types meet it; `ℝ` meets all of
  them here.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `{ι : Type*}`, `ι : Type u_1` | `ι` is any type (the index type of the nodes); `Type*` lets it live in any universe level, which Lean names `u_1` |
| `ℝ[X]`, `F[X]` | polynomials in one variable `X` with coefficients in `ℝ` (or a field `F`); the notation needs `open Polynomial` |
| `eval x q` | the value $q(x)$. Source `q.eval x` prints as `eval x q`: **the point comes first** |
| `C c` | the constant polynomial $c$ (`Polynomial.C`) |
| `q.degree` | the degree of `q`, a value in `WithBot ℕ` (ℕ plus `⊥` for the zero polynomial) |
| `↑s.card` | the size of `s`, a natural number cast into `WithBot ℕ` so it can be compared with `q.degree` |
| `Finset ι`, `i ∈ s` | a finite set of indices of type `ι` and membership in it |
| `∑ i ∈ s, f i` | the finite sum $\sum_{i \in s} f(i)$ (`Finset.sum s f`) |
| `Set.InjOn v ↑s` | `v` is injective on `s` (the nodes are distinct); `↑s` is the `Finset` seen as a `Set` |
| `Lagrange.basis s v i` | $L_i$, the Lagrange basis polynomial for node `v i` |
| `(Lagrange.interpolate s v) r` | the interpolant $\sum_{i \in s} r(i) L_i$: the polynomial of degree $< n$ taking value `r i` at `v i`. It is a linear map applied to `r`, hence the parentheses |
| `∫ (x : ℝ) in a..b, f x` | the interval integral $\int_a^b f(x)\,dx$; for $b < a$ it is $-\int_b^a$ |
| `∂μ`, `MeasureTheory.volume` | the measure being integrated against; `volume` is Lebesgue measure on `ℝ`, the default when no `∂μ` is shown |
| `IntervalIntegrable f MeasureTheory.volume a b` | `f` is integrable on the interval between `a` and `b` |
| `Continuous f` | `f : ℝ → ℝ` is continuous |
| `x_1` | a bound variable `simp` renamed so it does not clash with the integral's `x` |
| `x✝`, `a✝`, `inst✝` | inaccessible names: a hypothesis bound by `_` (as in `fun i _ => …`) or a type-class argument |

---

## Part 1 · `interpolatory_quadrature_exact`

Statement: for nodes `v` injective on `s` and `p : ℝ[X]` with `p.degree < s.card`,
`∫ x in a..b, p.eval x = ∑ i ∈ s, (∫ x in a..b, (Lagrange.basis s v i).eval x) * p.eval (v i)`.
Only the left side changes for most of the proof; the right side is the target shape.

### Rewriting one side only

**R1 · `conv_lhs => rw [h]`** changes the **goal**: `conv_lhs` focuses on the left-hand side of an `=` and runs
`rw` there only; `conv_rhs` focuses on the right. A plain `rw [h]` rewrites every match on both sides.
Placeholders: `{α β : Type} (F G : α → β) (a b : α) (h : a = b)`.

| Before | After |
|---|---|
| `h : a = b ⊢ F a = G a` | `h : a = b ⊢ F b = G a` |

### Lagrange interpolation

**R2 · `Lagrange.eq_interpolate`** changes the **goal**: a polynomial becomes the interpolant of its own values
at the nodes. Statement: `Set.InjOn v ↑s → q.degree < ↑s.card → q = (Lagrange.interpolate s v) fun i => eval (v i) q`.
Pass both hypotheses: `rw [Lagrange.eq_interpolate hv hq]`. Placeholders:
`{F ι : Type} [Field F] [DecidableEq ι] (s : Finset ι) (v : ι → F) (q : F[X])`. `Field F`: `+ − × ÷`
with the usual laws (`ℝ`, `ℚ`, `ℂ`); `DecidableEq ι`: equality of indices can be decided (needed to build $L_i$).

| Before | After |
|---|---|
| `⊢ P q` | `⊢ P ((Lagrange.interpolate s v) fun i => eval (v i) q)` |

**R3 · `Lagrange.interpolate_apply`** changes the **goal**: the interpolant becomes its explicit sum over the
basis. Statement: `(Lagrange.interpolate s v) r = ∑ i ∈ s, C (r i) * Lagrange.basis s v i`. Placeholders as
in R2, plus `(r : ι → F)` (the values).

| Before | After |
|---|---|
| `⊢ P ((Lagrange.interpolate s v) r)` | `⊢ P (∑ i ∈ s, C (r i) * Lagrange.basis s v i)` |

### Evaluating polynomials

These sit under the integral's `fun x => …` in the exercise, where `rw` cannot reach (it does not rewrite
terms that mention a bound variable). Use `simp only [...]`, which does.

**R4 · `Polynomial.eval_finsetSum`** changes the **goal**: `eval` of a finite sum becomes the sum of `eval`s.
Statement: `eval x (∑ i ∈ s, g i) = ∑ i ∈ s, eval x (g i)`. Placeholders:
`{R ι : Type} [Semiring R] (s : Finset ι) (g : ι → R[X]) (x : R)`. `Semiring R`: `+` and `×` with `0`, `1`
(`ℕ`, `ℤ`, `ℝ`).

| Before | After |
|---|---|
| `⊢ P (eval x (∑ i ∈ s, g i))` | `⊢ P (∑ i ∈ s, eval x (g i))` |

**R5 · `Polynomial.eval_mul`** changes the **goal**: `eval` of a product becomes the product of `eval`s.
Statement: `eval x (q * r) = eval x q * eval x r`. Placeholders: `{R : Type} [CommSemiring R] (q r : R[X]) (x : R)`
(a semiring with commutative `×`: `ℕ`, `ℤ`, `ℝ`).

| Before | After |
|---|---|
| `⊢ P (eval x (q * r))` | `⊢ P (eval x q * eval x r)` |

**R6 · `Polynomial.eval_C`** changes the **goal**: a constant polynomial evaluates to its constant.
Statement: `eval x (C c) = c`. Placeholders: `{R : Type} [Semiring R] (c x : R)`.

| Before | After |
|---|---|
| `⊢ P (eval x (C c))` | `⊢ P c` |

### Swapping the integral and the sum

**R7 · `rw [intervalIntegral.integral_finsetSum]`** changes the **goal list**: `∫ ∑` becomes `∑ ∫`, and a side
goal asks that every summand be integrable. Statement:
`(∀ i ∈ s, IntervalIntegrable (f i) μ a b) → ∫ x in a..b, ∑ i ∈ s, f i x ∂μ = ∑ i ∈ s, ∫ x in a..b, f i x ∂μ`.
The side goal comes **second**; you can also pass its proof as the argument,
`rw [intervalIntegral.integral_finsetSum (fun i _ => …)]`. Placeholders:
`{ι : Type} (s : Finset ι) (f : ι → ℝ → ℝ) (a b : ℝ)`, `μ = MeasureTheory.volume`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ) in a..b, ∑ i ∈ s, f i x)` | `⊢ P (∑ i ∈ s, ∫ (x : ℝ) in a..b, f i x)`, `⊢ ∀ i ∈ s, IntervalIntegrable (f i) MeasureTheory.volume a b` |

The side goal starts with `∀ i ∈ s, …`: `intro i hi` first, then R8 → R9 → R10.

**R8 · `apply IntervalIntegrable.const_mul`** changes the **goal**: a constant factor does not affect
integrability. Statement: `IntervalIntegrable f μ a b → ∀ c, IntervalIntegrable (fun x => c * f x) μ a b`.
Placeholders: `(f : ℝ → ℝ) (c a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ IntervalIntegrable (fun x => c * f x) MeasureTheory.volume a b` | `⊢ IntervalIntegrable f MeasureTheory.volume a b` |

**R9 · `apply Continuous.intervalIntegrable`** changes the **goal**: a continuous function is integrable on
every bounded interval. Statement: `Continuous u → ∀ a b, IntervalIntegrable u μ a b` (for Lebesgue measure,
or any measure finite on bounded sets). Placeholders: `(f : ℝ → ℝ) (a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ IntervalIntegrable f MeasureTheory.volume a b` | `⊢ Continuous f` |

**R10 · `exact Polynomial.continuous q`** **closes** the goal: `x ↦ q(x)` is continuous. Statement:
`Polynomial.continuous q : Continuous fun x => eval x q`. Placeholders: `(q : ℝ[X])`.

| Before | After |
|---|---|
| `⊢ Continuous fun x => eval x q` | closed |

R8–R10 also compose as one term with dot notation (W4):
`((Polynomial.continuous q).intervalIntegrable a b).const_mul c`.

### Comparing the sums term by term

**R11 · `refine Finset.sum_congr rfl fun i hi => ?_`** changes the **goal and the context**: two sums over the
same `s` are equal if their terms are, for each `i ∈ s`. Statement:
`Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`; `rfl` proves `s = s`.
Placeholders: `{ι : Type} (s : Finset ι) (f g : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ ∑ i ∈ s, f i = ∑ i ∈ s, g i` | `i : ι, hi : i ∈ s ⊢ f i = g i` |

**R12 · `rw [intervalIntegral.integral_const_mul]`** changes the **goal**: a constant factor on the **left**
moves out of the integral. Statement: `∫ x in a..b, c * f x ∂μ = c * ∫ x in a..b, f x ∂μ`
(for a factor on the right: `intervalIntegral.integral_mul_const`). Placeholders: `(f : ℝ → ℝ) (c a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ) in a..b, c * f x)` | `⊢ P (c * ∫ (x : ℝ) in a..b, f x)` |

**R13 · `rw [mul_comm]`** changes the **goal**: swaps the factors of the first product `rw` finds. Statement:
`mul_comm a b : a * b = b * a`. If the goal becomes `t = t`, `rw` closes it by `rfl`. To pick a specific
product, give the factors: `rw [mul_comm a b]`. Placeholders: `{α : Type} [CommMonoid α] (a b : α)`
(commutative `×`: `ℕ`, `ℝ`).

| Before | After |
|---|---|
| `⊢ P (a * b)` | `⊢ P (b * a)` |

### Worked combinations (W1–W4, on objects that are not the exercise's)

**W1: a constant times a polynomial, integrated.** `simp only [eval_mul, eval_C]` (R5, R6) works under the
`∫`, then `rw [intervalIntegral.integral_const_mul]` (R12) closes it:

```lean-goal
⊢ ∫ (x : ℝ) in a..b, eval x (C c * q) = c * ∫ (x : ℝ) in a..b, eval x q
⊢ ∫ (x : ℝ) in a..b, c * eval x q = c * ∫ (x : ℝ) in a..b, eval x q
```

**W2: the integral of a sum of polynomials.** R4, then R7: the main goal closes by `rfl`, only the side goal
is left; `intro i _`, then R9 with R10 as one term:

```lean-goal
⊢ ∫ (x : ℝ) in a..b, eval x (∑ i ∈ s, g i) = ∑ i ∈ s, ∫ (x : ℝ) in a..b, eval x (g i)
⊢ ∫ (x : ℝ) in a..b, ∑ i ∈ s, eval x (g i) = ∑ i ∈ s, ∫ (x : ℝ) in a..b, eval x (g i)
⊢ ∀ i ∈ s, IntervalIntegrable (fun x => eval x (g i)) MeasureTheory.volume a b
⊢ IntervalIntegrable (fun x => eval x (g i)) MeasureTheory.volume a b
```

**W3: interpolating on one side only.** `conv_rhs => rw [Lagrange.eq_interpolate hv hq]` (R1, R2) rewrites the
`q` of the right side and leaves the `q` inside `eval (v i) q` on the left alone; then
`conv_rhs => rw [Lagrange.interpolate_apply]` (R3) makes both sides equal:

```lean-goal
⊢ eval x (∑ i ∈ s, C (eval (v i) q) * Lagrange.basis s v i) = eval x q
⊢ eval x (∑ i ∈ s, C (eval (v i) q) * Lagrange.basis s v i) = eval x ((Lagrange.interpolate s v) fun i => eval (v i) q)
```

**W4: integrability of `c * q(x)` in one term**: `((Polynomial.continuous q).intervalIntegrable a b).const_mul c`
(R10, R9, R8 read inside out).

---

## Traps

- A plain `rw [Lagrange.eq_interpolate hv hp]` rewrites **every** `p`, including the `p` inside
  `eval (v i) p` on the right, which then no longer has the shape you are aiming for. Use
  `conv_lhs => rw [...]` (R1).
- `rw [eval_finsetSum]` fails under `∫ x in a..b, …`: the term mentions the bound `x`. Use `simp only` (R4–R6).
- After `simp only`, the sum's index may print as `x_1`. `eval x (C c * L)` becomes `c * eval x L`: the
  constant is on the **left**, so R12 (`integral_const_mul`) applies, not `integral_mul_const`; the target
  has it on the right, hence R13.
- `eval x q` is $q(x)$: the point comes first. `eval (v i) p` is $p(v_i)$.
- R7's side goal comes second and is easy to forget; it is `∀ i ∈ s, …`, so `intro` before R8.
- `rw [mul_comm]` with no arguments rewrites the first product it finds, which may be the wrong one; give the
  factors if it does.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| rewrite the left side only | `conv_lhs => rw [h]` | R1 |
| `p` → its interpolant (deg `p` < number of nodes) | `Lagrange.eq_interpolate hv hp` | R2 |
| interpolant → `∑ i ∈ s, C (r i) * Lagrange.basis s v i` | `Lagrange.interpolate_apply` | R3 |
| push `eval` through `∑`, `*`, `C` under a binder | `simp only [eval_finsetSum, eval_mul, eval_C]` | R4–R6 |
| `∫ ∑ = ∑ ∫` | `rw [intervalIntegral.integral_finsetSum]` + integrability side goal | R7 |
| integrability of `c * q(x)` | `((Polynomial.continuous _).intervalIntegrable _ _).const_mul _` | R8–R10 |
| equal sums, term by term | `refine Finset.sum_congr rfl fun i hi => ?_` | R11 |
| `∫ c * f = c * ∫ f` | `rw [intervalIntegral.integral_const_mul]` | R12 |
| swap two factors | `rw [mul_comm]` / `rw [mul_comm a b]` | R13 |
| see the state | infoview | |
