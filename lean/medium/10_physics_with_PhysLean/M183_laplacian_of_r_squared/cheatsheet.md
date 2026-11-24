# M183 · Laplacian of r²: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's `d`-dimensional space `Space d`,
its partial derivatives `∂[μ]` and Laplacian `Δ`; Mathlib's Fréchet derivative `fderiv`, continuous linear
maps `E →L[ℝ] F`, the differentiability prover `fun_prop`, finite sums `∑`, and the cast `ℕ → ℝ`.

**The maths.** For $y \in \mathbb{R}^d$ let $r^2 = \|y\|^2 = \sum_j y_j^2$. Then
$\partial_i (r^2) = 2 y_i$ as a function of $y$, so $\partial_i \partial_i (r^2) = \partial_i (2 y_i) = 2$,
and $\Delta (r^2) = \sum_{i=0}^{d-1} \partial_i \partial_i (r^2) = 2d$ at every point $x$. In Mathlib the
derivative of $f$ at $x$ is a linear map $Df(x)$ (`fderiv ℝ f x`), and $\partial_\mu f(x) = Df(x)\,e_\mu$,
where $e_\mu$ is the $\mu$-th unit vector (`basis μ`). The constant factor comes out of the derivative,
$D(b \cdot a)(x) = b \cdot Da(x)$, and $\partial_i y_i = 1$.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal.
- Placeholders are written as Lean binders. `{E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]` says `E` is
  a real normed vector space; `Space d` and `ℝ` both qualify.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Space d` | physlib's `d`-dimensional space: a structure with one field `val : Fin d → ℝ` (the coordinates) |
| `Fin d` | the indices `{0, …, d-1}` |
| `y i`, prints `y.val i` | coordinate `i` of the point `y` (`y i` is accepted as input and unfolds to `y.val i`) |
| `‖y‖` | the Euclidean norm of `y`, so `‖y‖ ^ 2` is $r^2 = \sum_j y_j^2$ |
| `∂[μ] f`, prints `Space.deriv μ f` | the partial derivative $\partial f/\partial y_\mu$, itself a function `Space d → ℝ` |
| `Space.deriv μ f x` | its value at the point `x` |
| `Space.deriv i fun y => …` | the same, with the function written last (Lean drops the parentheses) |
| `Δ f` | `Space.laplacian f`, the Laplacian, a function `Space d → ℝ`; `Δ f x` is its value at `x` |
| `fderiv ℝ f x` | the Fréchet derivative $Df(x)$, a continuous linear map `Space d →L[ℝ] ℝ` |
| `(fderiv ℝ f x) v` | $Df(x)\,v$, the derivative of `f` at `x` along the vector `v` |
| `basis μ` | `Space.basis μ`, the unit vector $e_\mu$ (an orthonormal basis of `Space d`) |
| `E →L[ℝ] F` | continuous linear maps from `E` to `F` |
| `c • A` | scalar `c` times the linear map `A` (`(c • A) v = c • A v`); `n • a` with `n : ℕ` is `a + ⋯ + a` (`n` times) |
| `DifferentiableAt ℝ f x` | `f` is (Fréchet) differentiable at `x` |
| `∑ i, F i` | $\sum_{i \in \texttt{Fin } n} F_i$, a sum over all of `Fin n`; Lean may rename the bound variable (`∑ x, G x`) |
| `Finset.univ.card` | the number of elements of `Fin n` as a finite set; `Fintype.card (Fin n)` is the same count |
| `↑d` | the natural number `d` cast into `ℝ` (the `d` on the right of the spec is this cast) |
| `(fun x => …) x` | a function applied to a point, not yet simplified (β-reduction, done by any `simp`) |

---

## Part 1 · `laplacian_norm_sq`

Statement: `Δ (fun y : Space d => ‖y‖ ^ 2) x = 2 * d`: in `d` dimensions the Laplacian of $r^2$ is the
constant $2d$ at every point `x`. Prove two facts first (both with `have h : ∀ i : Fin d, … := by intro i; …`):
the first derivative as a **function**, `h1 : ∀ i, ∂[i] (fun y => ‖y‖ ^ 2) = fun y => 2 * y i` (R1, R2), and
the second derivative as a **number**, `h2 : ∀ i, ∂[i] (fun y => 2 * y i) x = 2` (R3–R8). Then unfold `Δ`
into a sum (R9), feed `h1`, `h2` to `simp` (R10–R12), and close the last equation (R13).

### Fact 1: the first derivative, as a function

**R1 · `funext y`** changes the **goal and the context**: an equation between functions becomes the
equation of their values at a new variable `y`. You need it because `h1` is an equation of functions
(`∂[i] f` is not applied to a point). Placeholders: `{α β : Type} (f g : α → β)`.

| Before | After |
|---|---|
| `⊢ f = g` | `y : α ⊢ f y = g y` |

**R2 · `Space.deriv_norm_sq`** changes the **goal** (with `rw`) or **closes** it (with `exact`). The lemma is
`∀ {d} (x : Space d) (i : Fin d), ∂[i] (fun x => ‖x‖ ^ 2) x = 2 * x.val i`, i.e. $\partial_i r^2 = 2 y_i$.
Note the argument order: point first, then index (`deriv_norm_sq y i`). Placeholders:
`{d : ℕ} (i : Fin d) (y : Space d)`.

| Before | After |
|---|---|
| `⊢ P (Space.deriv i (fun x => ‖x‖ ^ 2) y)` | `⊢ P (2 * y.val i)` |

**W1** runs the same pattern on the coordinate function: `funext y`, then `exact deriv_component_same i y`:

```lean-goal
⊢ (Space.deriv i fun y => y.val i) = fun x => 1
⊢ Space.deriv i (fun y => y.val i) y = 1
```

### Fact 2: the second derivative, as a number

**R3 · `rw [Space.deriv_eq]`** changes the **goal**. The lemma is `∂[μ] f x = fderiv ℝ f x (basis μ)`: a
partial derivative **at a point** is the Fréchet derivative applied to the unit vector $e_\mu$. Use it to get
to Mathlib's derivative rules. Placeholders: `{d : ℕ} (μ : Fin d) (f : Space d → ℝ) (x : Space d)`.

| Before | After |
|---|---|
| `⊢ P (Space.deriv μ f x)` | `⊢ P ((fderiv ℝ f x) (basis μ))` |

**R4 · `rw [fderiv_const_mul (by fun_prop)]`** changes the **goal**. The lemma is
`DifferentiableAt 𝕜 a x → ∀ b, fderiv 𝕜 (fun y => b * a y) x = b • fderiv 𝕜 a x`: a constant factor comes out of
the derivative. Without the argument, `rw` adds `DifferentiableAt ℝ a x` as a second goal (the **goal list**
grows); `(by fun_prop)` (R5) proves it on the spot. `𝕜` is the scalar field, here `ℝ`. Placeholders:
`{E : Type}` a real normed space, `(a : E → ℝ) (b : ℝ) (x : E)`.

| Before | After `rw [fderiv_const_mul]` |
|---|---|
| `⊢ P (fderiv ℝ (fun y => b * a y) x)` | `⊢ P (b • fderiv ℝ a x)`, `⊢ DifferentiableAt ℝ a x` |

**R5 · `fun_prop`** **closes** a differentiability goal built from coordinates, constants, `+`, `*`, … The
coordinate map $y \mapsto y_i$ is linear, hence differentiable. Placeholders: `{d : ℕ} (i : Fin d) (x : Space d)`.

| Before | After |
|---|---|
| `⊢ DifferentiableAt ℝ (fun y => y.val i) x` | no goals |

**R6 · `rw [_root_.smul_apply]`, then `rw [smul_eq_mul]`** change the **goal**: a scaled linear map applied
to a vector, then a scalar `•` between reals becomes `*`. Lemmas: `(r • f) x = r • f x` and `a • b = a * b`.
Placeholders: `{E : Type}` a real normed space, `(A : E →L[ℝ] ℝ) (c : ℝ) (v : E)`.

| Before | After `_root_.smul_apply` | After `smul_eq_mul` |
|---|---|---|
| `⊢ P ((c • A) v)` | `⊢ P (c • A v)` | `⊢ P (c * A v)` |

**R7 · `rw [← Space.deriv_eq]`** changes the **goal**: R3 right to left, folding the Fréchet derivative back
into a partial derivative so a `Space` lemma (R8) applies. Placeholders as in R3.

| Before | After |
|---|---|
| `⊢ P ((fderiv ℝ f x) (basis μ))` | `⊢ P (Space.deriv μ f x)` |

**R8 · `Space.deriv_component_same`** changes the **goal**. The lemma is `∂[μ] (fun x => x.val μ) x = 1`
($\partial y_\mu / \partial y_\mu = 1$). The general `Space.deriv_component` gives `if ν = μ then 1 else 0`.
Placeholders: `{d : ℕ} (μ : Fin d) (x : Space d)`.

| Before | After |
|---|---|
| `⊢ P (Space.deriv μ (fun y => y.val μ) x)` | `⊢ P 1` |

**W2** chains R3, R4 + R5, R6, R7, R8 by hand on $\partial_i (3 y_i) = 3$, then `ring` (R13):

```lean-goal
⊢ Space.deriv i (fun y => 3 * y.val i) x = 3
⊢ (3 • fderiv ℝ (fun y => y.val i) x) (basis i) = 3
⊢ 3 * (fderiv ℝ (fun y => y.val i) x) (basis i) = 3
⊢ 3 * Space.deriv i (fun y => y.val i) x = 3
⊢ 3 * 1 = 3
```

**W3** does R6–R8 and `3 * 1 = 3` in one call: after R3 and R4, `simp [← Space.deriv_eq]` closes the goal
(`simp` knows R6, R8 and `mul_one`; you only tell it the direction of R7).

### The Laplacian as a sum

**R9 · `rw [laplacian_eq_sum_snd_deriv]`** changes the **goal**. The lemma `Space.laplacian_eq_sum_snd_deriv`
is `Δ f = fun x => ∑ i, ∂[i] (∂[i] f) x`, an equation of **functions**, so the point `x` ends up applied to a
`fun`. Any later `simp` β-reduces that to `∑ i, Space.deriv i (Space.deriv i f) x`. Placeholders:
`{d : ℕ} (f : Space d → ℝ) (x : Space d)`.

| Before | After |
|---|---|
| `⊢ P (Δ f x)` | `⊢ P ((fun x => ∑ i, Space.deriv i (Space.deriv i f) x) x)` |

**R10 · `simp only [hFG]`** changes the **goal**: with `hFG : ∀ i, F i = G i` it rewrites every summand,
**under** the binder `i` of `∑`. `rw [hFG]` fails here: the summand mentions the bound `i`. In the exercise the
two facts play this role: `h1` turns the inner `∂[i] (fun y => ‖y‖ ^ 2)` into `fun y => 2 * y i`, then `h2`
turns each summand into `2`. Placeholders: `{n : ℕ} (F G : Fin n → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, F i)` | `⊢ P (∑ x, G x)` |

**R11 · `rw [Finset.sum_const]`, `rw [Finset.card_univ]`, `rw [Fintype.card_fin]`** change the **goal**: a sum
of a constant is (number of terms) `•` constant, and `Fin n` has `n` elements. Lemmas:
`∑ _x ∈ s, b = s.card • b`, `Finset.univ.card = Fintype.card α`, `Fintype.card (Fin n) = n`.
Placeholders: `{n : ℕ} (c : ℝ)`.

| Before | After `sum_const` | After `card_univ` | After `card_fin` |
|---|---|---|---|
| `⊢ P (∑ _i, c)` | `⊢ P (Finset.univ.card • c)` | `⊢ P (Fintype.card (Fin n) • c)` | `⊢ P (n • c)` |

**R12 · `rw [nsmul_eq_mul]`** changes the **goal**. The lemma is `n • a = ↑n * a`: the `n`-fold sum
becomes a product with the cast `↑n : ℝ`. Placeholders: `(n : ℕ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (n • a)` | `⊢ P (↑n * a)` |

`simp [h1, h2]` applies R9's β-reduction, R10, R11 and R12 by itself and stops at `↑d * 2 = 2 * ↑d`: `simp`
does not reorder factors.

**R13 · `ring`** **closes** an identity of commutative rings. It treats the cast `↑n` as an unknown, which is
all `↑n * a = a * ↑n` needs. Placeholders: `(n : ℕ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ ↑n * a = a * ↑n` | no goals |

**W4** runs `simp [hF]` (R10–R12) and then `ring` (R13) on an abstract table `hF : ∀ i, F i = 5`:

```lean-goal
⊢ ∑ i, F i = 5 * ↑n
⊢ ↑n * 5 = 5 * ↑n
```

---

## Traps

- `Space.deriv_eq` (R3) only rewrites a `∂` **applied to a point**. In `∂[i] (∂[i] f) x`, the inner `∂[i] f`
  is a function; that is why fact 1 is stated as an equation of functions (proved with `funext`, R1) and
  used by `simp`.
- `Space.deriv_norm_sq y i` takes the point first, then the index.
- Under `open Space`, a bare `smul_apply` is `Space.smul_apply` (about `(c • y).val i`), and `rw [smul_apply]`
  fails on `(c • A) v`. Write `_root_.smul_apply`, or let `simp` choose.
- `rw` cannot rewrite inside `∑ i, …` when the term mentions `i` (R10): use `simp [h1, h2]`.
- After `simp only [h1, h2]` the goal reads `∑ x, 2 = 2 * ↑d`: Lean reused the name `x` for the bound index
  of the sum. It is not the theorem's point `x`.
- In a `have h2 : ∀ i : Fin d, …` statement, write the point `x` of the theorem, not a new variable: the
  sum in R9 is evaluated at that `x`.
- `rw [fderiv_const_mul]` without `(by fun_prop)` leaves the `DifferentiableAt` side goal after the main one.
- The right side `2 * d` is `2 * ↑d` in `ℝ`; `simp` produces `↑d * 2`, so finish with `ring` (R13).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| state a fact for every index | `have h : ∀ i : Fin d, … := by intro i; …` | TACTIC_STATES |
| equation of functions → pointwise | `funext y` | R1 |
| $\partial_i r^2 = 2 y_i$ | `exact deriv_norm_sq y i` | R2 |
| `∂[μ] f x` → `fderiv ℝ f x (basis μ)` | `rw [Space.deriv_eq]` | R3 |
| constant factor out of `fderiv` | `rw [fderiv_const_mul (by fun_prop)]` | R4, R5 |
| differentiability side goal | `fun_prop` | R5 |
| `(c • A) v` → `c * A v` | `rw [_root_.smul_apply, smul_eq_mul]` | R6 |
| `fderiv … (basis μ)` → `∂[μ] …` | `rw [← Space.deriv_eq]` | R7 |
| $\partial_\mu y_\mu = 1$ | `rw [Space.deriv_component_same]` | R8 |
| R6–R8 at once | `simp [← Space.deriv_eq]` | W3 |
| `Δ f x` → sum of second partials | `rw [laplacian_eq_sum_snd_deriv]` | R9 |
| rewrite inside `∑`, sum a constant, `n • a` → `↑n * a` | `simp [h1, h2]` | R10–R12 |
| `↑d * 2 = 2 * ↑d` | `ring` | R13 |
| see the state | infoview | |
