# H109 · The Coulomb field is divergence free off the charge: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's `Space` (3D space), its partial
derivative `∂[i]` and divergence `∇ ⬝`; Mathlib's derivatives as linear maps (`fderiv`, `HasFDerivAt`),
one-variable derivatives (`HasDerivAt`), the chain and product rules, and the calculus of the norm `‖·‖`.

The mathematics. With $r = \lVert x\rVert$ and $x_i$ the $i$-th coordinate, the field is
$E_i(y) = y_i / \lVert y\rVert^3$. Away from $0$:
$\partial_i \lVert y\rVert = x_i / r$ (milestone 1), $\partial_i \lVert y\rVert^{-3} = -3x_i / r^5$ (milestone 2,
chain rule), $\partial_i E_i = r^{-3} - 3x_i^2/r^5$ (milestone 3, product rule), and
$\nabla\cdot E = \sum_i \partial_i E_i = 3/r^3 - 3(\sum_i x_i^2)/r^5 = 0$ because $\sum_i x_i^2 = r^2$.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{E : Type}` is any type. A bracket such as `[NormedSpace ℝ E]`
  is a requirement on `E` (a *type class*). Here: `[NormedAddCommGroup E]` means `E` has `+`, `-` and a norm
  `‖·‖`; `[NormedSpace ℝ E]` adds real scalars `c • v`; `[InnerProductSpace ℝ F]` adds an inner product
  `⟪u, v⟫_ℝ` whose norm is `‖·‖`. `ℝ`, `Space` and `EuclideanSpace ℝ (Fin 3)` meet all three.
- "context gains `h`" entries are written `have h := …`: the new hypothesis is exactly what the lemma
  produced, so you can read off its form before you use it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Space` | physlib's 3-dimensional space (`Space 3`; the dimension defaults to 3). A point `x : Space` has coordinates |
| `x.val 3 i` | coordinate `i : Fin 3` of `x`. `Space` is a structure with one field `val : Fin 3 → ℝ`; you write `x i` (a coercion to `x.val`), and Lean prints the default dimension argument `3` as well |
| `‖x‖` | the Euclidean norm $\sqrt{x_0^2 + x_1^2 + x_2^2}$ |
| `√a` | `Real.sqrt a` |
| `Space.deriv i f x` | `∂[i] f x`: the partial derivative of `f : Space → M` in direction `i` at `x` |
| `basis i` | `Space.basis i`, the unit vector along axis `i` |
| `E →L[ℝ] F`, `StrongDual ℝ E` | continuous linear maps `E → F`; `StrongDual ℝ E` is `E →L[ℝ] ℝ` |
| `fderiv ℝ f x` | the derivative of `f` at `x`, a linear map; `(fderiv ℝ f x) v` is the directional derivative along `v` |
| `HasFDerivAt f f' x` | "`f'` is the derivative of `f` at `x`" (a fact, not a value) |
| `HasDerivAt g g' a` | the same for `g : ℝ → ℝ`, with `g'` a number |
| `DifferentiableAt ℝ f x` | `f` has some derivative at `x` |
| `innerSL ℝ a`, `(innerSL ℝ) a` | the linear map `v ↦ ⟪a, v⟫_ℝ` |
| `⟪a, v⟫_ℝ` | the real inner product (dot product) |
| `2 • L` | `L + L`: a *natural-number* scalar `2 : ℕ` times a linear map |
| `c • L`, `c • v` | the real scalar `c` times a map or a vector |
| `c • f` (functions) | the pointwise product `fun y => c y • f y` |
| `↑3` | the natural number `3` cast into `ℝ` |
| `a ^ (3 - 1)` | natural-number subtraction in the exponent; it is `a ^ 2` by computation |
| `basis.repr y` | the point `y` as a vector in `EuclideanSpace ℝ (Fin 3)` |
| `v.ofLp i` | component `i` of a vector `v : EuclideanSpace ℝ (Fin 3)` (you may write `v i`) |
| `div F x` | `(∇ ⬝ F) x`, the divergence of `F : Space → EuclideanSpace ℝ (Fin 3)` at `x` |
| `∑ i, f i` | the sum over `i : Fin 3 = {0, 1, 2}` |
| `a⁻¹` | the inverse `1 / a` (in `ℝ`, `0⁻¹ = 0`, which is why every step needs `‖x‖ ≠ 0`) |
| `-3 * a / b` | `((-3) * a) / b`: `*` and `/` group to the left |
| `((fun y => e) x).ofLp i` | a function applied to `x` that is not yet evaluated (a *beta-redex*); `simp only` reduces it to `e` with `y := x` (R31) |
| `∑ x_1, Space.deriv x_1 (fun x => … x.val 3 x_1) x` | bound variables get new names: the sum index prints as `x_1`, and `fun x => …` is a fresh `x` inside the lambda, not the point `x`. Only the last `x` is the point |
| `HasStrictFDerivAt f f' a` | a stronger form of `HasFDerivAt`; `.hasFDerivAt` turns it into `HasFDerivAt` (R3) |

---

## Part 1 · `deriv_norm` (milestone 1)

Statement: for `x ≠ 0`, `∂[i] (fun y => ‖y‖) x = x i / ‖x‖`. Route: `‖y‖ = √(‖y‖²)`, and `‖y‖²` has a known
derivative.

### The fact behind everything

**R1 · `norm_pos_iff`** changes the **context**. The lemma is `0 < ‖a‖ ↔ a ≠ 0`; `.mpr` uses it right to
left. Placeholders: `{E : Type} [NormedAddCommGroup E] (a : E) (hx : a ≠ 0)`. Every milestone starts with
`have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx`; `positivity` and `field_simp` read `hn` from the context.

| Before | After `have h := norm_pos_iff.mpr hx` |
|---|---|
| `hx : a ≠ 0 ⊢ 0 < ‖a‖` | `h : 0 < ‖a‖ ⊢ 0 < ‖a‖` |

**R2 · `positivity`** **closes** a goal `0 < e`, `0 ≤ e` or `e ≠ 0` when `e` is built from pieces it knows
are positive (numerals, squares, norms, hypotheses `0 < a`). Use it as a side argument `(by positivity)`.
Placeholders: `(r : ℝ) (hr : 0 < r)`.

| Before | After |
|---|---|
| `hr : 0 < r ⊢ r ^ 3 ≠ 0` | no goals |

### The derivative of `‖y‖ ^ 2`, then of its square root

**R3 · `hasStrictFDerivAt_norm_sq` + `.hasFDerivAt`** changes the **context**. The lemma says
`HasStrictFDerivAt (fun x => ‖x‖ ^ 2) (2 • innerSL ℝ a) a`, i.e. $d(\lVert y\rVert^2) = 2\langle a, \cdot\rangle$;
`.hasFDerivAt` weakens "strict" to the ordinary `HasFDerivAt`. Placeholders:
`{F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (a : F)`. The `2` is a natural number: to state
the fact yourself, write `((2 : ℕ) • (innerSL ℝ) a)`.

| Before | After `have h := (hasStrictFDerivAt_norm_sq a).hasFDerivAt` |
|---|---|
| `⊢ HasFDerivAt (fun y => ‖y‖ ^ 2) (2 • (innerSL ℝ) a) a` | `h : HasFDerivAt (fun x => ‖x‖ ^ 2) (2 • (innerSL ℝ) a) a ⊢ HasFDerivAt (fun y => ‖y‖ ^ 2) (2 • (innerSL ℝ) a) a` |

**R4 · `HasFDerivAt.sqrt`** changes the **context**: from `hf : HasFDerivAt f f' a` and `hx : f a ≠ 0`,
`hf.sqrt hx : HasFDerivAt (fun y => √(f y)) ((1 / (2 * √(f a))) • f') a`, the rule
$(\sqrt f)' = f' / (2\sqrt f)$. Placeholders: `{E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
(f : E → ℝ) (f' : E →L[ℝ] ℝ) (a : E)`. In the exercise `hx` is `(by positivity)` (R2).

| Before | After `have h := hf.sqrt hx` |
|---|---|
| `hx : f a ≠ 0 ⊢ HasFDerivAt (fun y => √(f y)) ((1 / (2 * √(f a))) • f') a` | `h : HasFDerivAt (fun y => √(f y)) ((1 / (2 * √(f a))) • f') a ⊢ HasFDerivAt (fun y => √(f y)) ((1 / (2 * √(f a))) • f') a` |

### Making the function match: `√(‖y‖ ^ 2)` → `‖y‖`

R4 gives a fact about `fun y => √(‖y‖ ^ 2)`, but the goal is about `fun y => ‖y‖`. Prove the two functions
equal (R5–R7) and rewrite the fact (R8).

**R5 · `funext y`** changes the **goal and the context**: an equation of functions becomes an equation of
values at a new variable `y`. Placeholders: `{α β : Type} (f g : α → β)`.

| Before | After |
|---|---|
| `⊢ f = g` | `y : α ⊢ f y = g y` |

**R6 · `norm_nonneg`** changes the **context**: `norm_nonneg y : 0 ≤ ‖y‖`. Placeholders:
`{E : Type} [NormedAddCommGroup E] (y : E)`.

| Before | After `have h := norm_nonneg y` |
|---|---|
| `⊢ 0 ≤ ‖y‖` | `h : 0 ≤ ‖y‖ ⊢ 0 ≤ ‖y‖` |

**R7 · `Real.sqrt_sq`** changes the **goal**. The lemma is `0 ≤ a → √(a ^ 2) = a`; its argument is the proof
of `0 ≤ a`: `norm_nonneg y` (R6), or `hn.le` (`hn : 0 < a` weakened to `0 ≤ a`). Placeholders: `(a : ℝ)
(ha : 0 ≤ a)`. `exact Real.sqrt_sq (norm_nonneg y)` closes the goal of R5.

| Before | After `rw [Real.sqrt_sq ha]` |
|---|---|
| `ha : 0 ≤ a ⊢ P √(a ^ 2)` | `⊢ P a` |

**R8 · `rw [e] at h`** changes the **context**: it rewrites the hypothesis `h` with `e`, the goal is
untouched. Placeholders: `{α β : Type} (f g : α → β) (e : f = g) (Q : (α → β) → Prop)`.

| Before | After |
|---|---|
| `h : Q f ⊢ Q g` | `h : Q g ⊢ Q g` |

### From a derivative fact to the value `∂[i] f x`

**R9 · `Space.deriv_eq`** changes the **goal**: `∂[i] f x = fderiv ℝ f x (basis i)`, the derivative map applied
to the unit vector `basis i`. `rw [← Space.deriv_eq]` folds it back into `∂[i]` (used in Part 2 to reach
milestone 1). Placeholders: `(f : Space → ℝ) (i : Fin 3) (x : Space)`.

| Before | After |
|---|---|
| `⊢ P (Space.deriv i f x)` | `⊢ P ((fderiv ℝ f x) (basis i))` |

**R10 · `HasFDerivAt.fderiv`** changes the **goal**. The lemma is `HasFDerivAt f f' x → fderiv ℝ f x = f'`,
so `rw [hf.fderiv]` replaces the abstract derivative by the concrete map `f'`. The function in `hf` must
be the goal's function *literally* (hence R5–R8). Placeholders: `{E : Type} [NormedAddCommGroup E]
[NormedSpace ℝ E] (f : E → ℝ) (f' : E →L[ℝ] ℝ) (x v : E)`.

| Before | After |
|---|---|
| `hf : HasFDerivAt f f' x ⊢ P ((fderiv ℝ f x) v)` | `⊢ P (f' v)` |

### Evaluating the map at `basis i`

After R9, R10 the goal is `((1 / (2 * √(‖x‖ ^ 2))) • 2 • (innerSL ℝ) x) (basis i) = x.val 3 i / ‖x‖`.
`simp [Real.sqrt_sq hn.le]` evaluates it, using R11–R14 (and R7) by itself, and leaves
`‖x‖⁻¹ * 2⁻¹ * (2 * x.val 3 i) = x.val 3 i / ‖x‖` for R15.

**R11 · `_root_.smul_apply`** changes the **goal**: a scaled linear map applied to a vector. Write
`_root_.smul_apply`: under `open Space`, plain `smul_apply` means `Space.smul_apply` (coordinates of
`c • p` for a point `p`). Placeholders: `{E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
(L : E →L[ℝ] ℝ) (c : ℝ) (v : E)`.

| Before | After |
|---|---|
| `⊢ P ((c • L) v)` | `⊢ P (c • L v)` |

**R12 · `smul_eq_mul`, `nsmul_eq_mul`** change the **goal**: `a • b = a * b` for numbers, and
`n • b = ↑n * b` for `n : ℕ`. Placeholders: `(a b : ℝ) (n : ℕ)`. `rw [smul_eq_mul]` fixes `a`, `b` at the
first match and rewrites only that product; when the goal has two different `•` (Part 3), use
`simp only [smul_eq_mul]` (R31), which rewrites all of them.

| Before | After `rw [smul_eq_mul]` | After `rw [nsmul_eq_mul]` |
|---|---|---|
| `⊢ P (a • b + n • b)` | `⊢ P (a * b + n • b)` | `⊢ P (a * b + ↑n * b)` |

**R13 · `coe_innerSL_apply`** changes the **goal**: `innerSL ℝ a` applied to `v` is `⟪a, v⟫_ℝ`. It is stated
for the function `⇑(innerSL ℝ a)`, so use it with `simp only`, not `rw`. Placeholders:
`{F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (a v : F)`.

| Before | After `simp only [coe_innerSL_apply]` |
|---|---|
| `⊢ P (((innerSL ℝ) a) v)` | `⊢ P ⟪a, v⟫_ℝ` |

**R14 · `Space.inner_basis`** changes the **goal**: `⟪p, basis i⟫_ℝ = p i`, the inner product with a unit
vector picks a coordinate. Placeholders: `(p : Space) (i : Fin 3)`.

| Before | After |
|---|---|
| `⊢ P ⟪p, basis i⟫_ℝ` | `⊢ P (p.val 3 i)` |

**R15 · `field_simp`** changes the **goal**: it multiplies out every denominator it can prove nonzero (from
`0 < r` or `r ≠ 0` in the context, so have `hn` there) and cancels. The result is a polynomial equation,
which `field_simp` may close itself (Parts 1, 2) or leave for `ring` (Part 3) or `nlinarith` (Part 4).
Placeholders: `(r a b : ℝ) (hr : 0 < r)`.

| Before | After |
|---|---|
| `hr : 0 < r ⊢ (r ^ 3)⁻¹ - a / r ^ 5 = b` | `⊢ r ^ 2 - a = r ^ 5 * b` |

---

## Part 2 · `deriv_inv_norm_cube` (milestone 2)

Statement: for `x ≠ 0`, `∂[i] (fun y => (‖y‖ ^ 3)⁻¹) x = -3 * x i / ‖x‖ ^ 5`. Chain rule: the outer function
is `g r = (r ^ 3)⁻¹` on `ℝ`, the inner one is `‖·‖`; then milestone 1 for `∂[i] ‖·‖`.

**R16 · `DifferentiableAt.norm`** changes the **context**: `DifferentiableAt.norm ℝ differentiableAt_id hx`
proves that `fun y => ‖y‖` is differentiable at `x ≠ 0` (the norm of the identity map `id`, nonzero at `x`).
The field `ℝ` is an explicit argument. State the type, `have hd : DifferentiableAt ℝ (fun y : Space => ‖y‖) x
:= …`, or Lean shows `‖id y‖`. Placeholders: `{F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
(x : F) (hx : x ≠ 0)`.

| Before | After |
|---|---|
| `hx : x ≠ 0 ⊢ DifferentiableAt ℝ (fun y => ‖y‖) x` | `h : DifferentiableAt ℝ (fun y => ‖y‖) x ⊢ DifferentiableAt ℝ (fun y => ‖y‖) x` |

**R17 · `hasDerivAt_pow`** changes the **context**: `hasDerivAt_pow n a : HasDerivAt (fun x => x ^ n)
(↑n * a ^ (n - 1)) a`, i.e. $(x^n)' = n x^{n-1}$. Placeholders: `(n : ℕ) (a : ℝ)`.

| Before | After `have h := hasDerivAt_pow 3 a` |
|---|---|
| `⊢ HasDerivAt (fun x => x ^ 3) (3 * a ^ (3 - 1)) a` | `h : HasDerivAt (fun x => x ^ 3) (↑3 * a ^ (3 - 1)) a ⊢ HasDerivAt (fun x => x ^ 3) (3 * a ^ (3 - 1)) a` |

**R18 · `HasDerivAt.fun_inv`** changes the **context**: from `hc : HasDerivAt c c' a` and `hx : c a ≠ 0`,
`hc.fun_inv hx : HasDerivAt (fun r => (c r)⁻¹) (-c' / c a ^ 2) a`, i.e. $(1/c)' = -c'/c^2$. Placeholders:
`(c : ℝ → ℝ) (c' a : ℝ)`. With R17: `(hasDerivAt_pow 3 ‖x‖).fun_inv (by positivity)` is the derivative of
`g r = (r ^ 3)⁻¹` at `r = ‖x‖`.

| Before | After `have h := hc.fun_inv hx` |
|---|---|
| `hx : c a ≠ 0 ⊢ HasDerivAt (fun r => (c r)⁻¹) (-c' / c a ^ 2) a` | `h : HasDerivAt (fun i => (c i)⁻¹) (-c' / c a ^ 2) a ⊢ HasDerivAt (fun r => (c r)⁻¹) (-c' / c a ^ 2) a` |

**R19 · `DifferentiableAt.hasFDerivAt`** changes the **context**: `hd.hasFDerivAt : HasFDerivAt f
(fderiv ℝ f x) x`, so a differentiability fact becomes a derivative fact whose derivative is the abstract
`fderiv ℝ f x`. Placeholders: `{E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (x : E)`.

| Before | After `have h := hd.hasFDerivAt` |
|---|---|
| `hd : DifferentiableAt ℝ f x ⊢ HasFDerivAt f (fderiv ℝ f x) x` | `h : HasFDerivAt f (fderiv ℝ f x) x ⊢ HasFDerivAt f (fderiv ℝ f x) x` |

**R20 · `HasDerivAt.comp_hasFDerivAt`** changes the **context**: the chain rule for `g : ℝ → ℝ` after
`f : E → ℝ`. `hg.comp_hasFDerivAt x hf : HasFDerivAt (g ∘ f) (g' • f') x` from `hg : HasDerivAt g g' (f x)`
and `hf : HasFDerivAt f f' x`. Write it as `have h : HasFDerivAt (fun y => g (f y)) (g' • f') x := …` so the
function is the lambda that R10 must match (`g ∘ f` is the same function, but `rw` does not see that).
Placeholders: `{E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (g : ℝ → ℝ)
(f' : E →L[ℝ] ℝ) (g' : ℝ) (x : E)`.

| Before | After |
|---|---|
| `hf : HasFDerivAt f f' x ⊢ HasFDerivAt (fun y => g (f y)) (g' • f') x` | `h : HasFDerivAt (fun y => g (f y)) (g' • f') x ⊢ HasFDerivAt (fun y => g (f y)) (g' • f') x` |

In the exercise: `g' = -(↑3 * ‖x‖ ^ 2) / (‖x‖ ^ 3) ^ 2` (R18 after R17), `f' = fderiv ℝ (fun y => ‖y‖) x` (R19
after R16). After R9, R10, the goal is that scalar times `(fderiv ℝ (fun y => ‖y‖) x) (basis i)`; R11, R12
make it a product, `rw [← Space.deriv_eq]` (R9) turns the second factor into `∂[i] (fun y => ‖y‖) x`, and
milestone 1 replaces that by `x i / ‖x‖`. R15 finishes.

**W2** in the guide is the same chain on `r ↦ r ^ 2`:

```lean-goal
⊢ Space.deriv i (fun y => ‖y‖ ^ 2) x = 2 * ‖x‖ * Space.deriv i (fun y => ‖y‖) x
⊢ 2 * ‖x‖ ^ (2 - 1) * Space.deriv i (fun y => ‖y‖) x = 2 * ‖x‖ * Space.deriv i (fun y => ‖y‖) x
```

---

## Part 3 · `deriv_summand` (milestone 3)

Statement: for `x ≠ 0`, `∂[i] (fun y => (‖y‖ ^ 3)⁻¹ * y i) x = (‖x‖ ^ 3)⁻¹ - 3 * x i ^ 2 / ‖x‖ ^ 5`. Product
rule, then milestone 2 for one factor and R26 for the other.

**R21 · `pow_pos`, `.ne'`** change the **context**: `pow_pos hr n : 0 < r ^ n`, and `.ne'` turns `0 < b` into
`b ≠ 0`. Placeholders: `(r : ℝ) (hr : 0 < r) (n : ℕ)`.

| Before | After `have h := (pow_pos hr 3).ne'` |
|---|---|
| `hr : 0 < r ⊢ r ^ 3 ≠ 0` | `h : r ^ 3 ≠ 0 ⊢ r ^ 3 ≠ 0` |

**R22 · `DifferentiableAt.pow`, `DifferentiableAt.inv`** change the **context**: `hd.pow n` is
differentiability of `f ^ n`, and `(hd.pow n).inv hne` of `(f ^ n)⁻¹`, given `hne : f x ^ n ≠ 0` (R21).
`f ^ n`, `(f ^ n)⁻¹` are pointwise operations on functions, so a `have` stated with `fun y => (f y ^ n)⁻¹`
accepts the proof. Placeholders: `{E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (x : E)`.

| Before | After |
|---|---|
| `hne : f x ^ 3 ≠ 0 ⊢ DifferentiableAt ℝ (fun y => (f y ^ 3)⁻¹) x` | `h : DifferentiableAt ℝ (fun y => (f y ^ 3)⁻¹) x ⊢ DifferentiableAt ℝ (fun y => (f y ^ 3)⁻¹) x` |

**R23 · `fun_prop`** **closes** a `DifferentiableAt` goal for a function built from coordinates, constants,
`+`, `*`, … (it does not know about `‖·‖` at `x ≠ 0`; that is R16). Placeholders: `(x : Space) (i j : Fin 3)`.

| Before | After |
|---|---|
| `⊢ DifferentiableAt ℝ (fun y => 2 * y.val 3 i + y.val 3 j) x` | no goals |

**R24 · `change`** changes the **goal** to a definitionally equal one you write out. Here a product of two
functions written as a lambda becomes `c • f`, the shape R25 needs. Placeholders: `(c f : Space → ℝ)`. In
the exercise: `change ∂[i] ((fun y : Space => (‖y‖ ^ 3)⁻¹) • fun y : Space => y i) x = _` (the `_` keeps the
right side).

| Before | After |
|---|---|
| `⊢ P fun y => c y * f y` | `⊢ P (c • f)` |

**R25 · `Space.deriv_smul`** changes the **goal**: the product rule
`∂[u] (c • f) x = c x • ∂[u] f x + ∂[u] c x • f x`, with arguments `hc : DifferentiableAt ℝ c x`,
`hf : DifferentiableAt ℝ f x` (R22, R23). Placeholders: `(c f : Space → ℝ) (u : Fin 3) (x : Space)`.

| Before | After `rw [Space.deriv_smul hc hf]` |
|---|---|
| `hc : DifferentiableAt ℝ c x ⊢ P (Space.deriv u (c • f) x)` | `⊢ P (c x • Space.deriv u f x + Space.deriv u c x • f x)` |

**R26 · `Space.deriv_component_same`** changes the **goal**: `∂[i] (fun y => y i) x = 1`.
Placeholders: `(i : Fin 3) (x : Space)`.

| Before | After |
|---|---|
| `⊢ P (Space.deriv i (fun y => y.val 3 i) x)` | `⊢ P 1` |

**R27 · `ring`** **closes** an identity of commutative rings. After R12 and R15 the goal of Part 3 is of this
kind. Placeholders: `(r a : ℝ)`.

| Before | After |
|---|---|
| `⊢ r ^ 2 + -(3 * a ^ 2) = r ^ 2 - 3 * a ^ 2` | no goals |

**W3** in the guide runs R24, R25, R26, R12 on `y ↦ yᵢ · yᵢ`:

```lean-goal
⊢ Space.deriv i ((fun y => y.val 3 i) • fun y => y.val 3 i) x = 2 * x.val 3 i
⊢ x.val 3 i • 1 + 1 • x.val 3 i = 2 * x.val 3 i
⊢ x.val 3 i * 1 + 1 * x.val 3 i = 2 * x.val 3 i
```

---

## Part 4 · `coulomb_div_free`

Statement: for `x ≠ 0`, `(∇ ⬝ (fun y => (‖y‖ ^ 3)⁻¹ • basis.repr y)) x = 0`. Unfold the divergence, simplify
each component to the function of milestone 3, substitute it, expand the sum and use `∑ xᵢ² = ‖x‖²`.

**R28 · `unfold Space.div`** changes the **goal**: the divergence becomes its definition, the sum of the
partial derivatives of the components. Placeholders: `(F : Space → EuclideanSpace ℝ (Fin 3)) (x : Space)`.

| Before | After |
|---|---|
| `⊢ P (div F x)` | `⊢ P (∑ i, Space.deriv i (fun x => (F x).ofLp i) x)` |

**R29 · `PiLp.smul_apply`** changes the **goal**: a component of a scaled vector. Placeholders:
`(c : ℝ) (v : EuclideanSpace ℝ (Fin 3)) (i : Fin 3)`.

| Before | After |
|---|---|
| `⊢ P ((c • v).ofLp i)` | `⊢ P (c • v.ofLp i)` |

**R30 · `Space.basis_repr_apply`** changes the **goal**: the components of `basis.repr p` are the coordinates
of `p`. Placeholders: `(p : Space) (i : Fin 3)`.

| Before | After |
|---|---|
| `⊢ P ((basis.repr p).ofLp i)` | `⊢ P (p.val 3 i)` |

**R31 · `simp only [e]`** changes the **goal**: it rewrites with `e : ∀ i, f i = g i` *under binders* such as
`∑ i, …` and `fun y => …`, where `rw` fails, and beta-reduces `(fun y => …) x`. Use it for R29, R30, R12
(`simp only [PiLp.smul_apply, Space.basis_repr_apply, smul_eq_mul]`) and then for milestone 3
(`simp only [deriv_summand _ x hx, …]`). Placeholders: `(f g : Fin 3 → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (∑ x, g x)` |

**R32 · `Fin.sum_univ_three`** changes the **goal** (or, with `at h`, a hypothesis): a sum over `Fin 3`
becomes three terms. Placeholders: `{β : Type} [AddCommMonoid β] (f : Fin 3 → β)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1 + f 2)` |

**R33 · `Space.norm_sq_eq`** changes the **goal** with `rw`, or the **context** with `have`: the lemma is
`Space.norm_sq_eq p : ‖p‖ ^ 2 = ∑ i, p i ^ 2`. In the exercise the sum is not in the goal, so use
`have h := Space.norm_sq_eq x` and then `rw [Fin.sum_univ_three] at h` (R8, R32), giving
`h : ‖x‖ ^ 2 = x.val 3 0 ^ 2 + x.val 3 1 ^ 2 + x.val 3 2 ^ 2`. Placeholders: `(p : Space)`.

| Before | After `rw [Space.norm_sq_eq]` |
|---|---|
| `⊢ P (‖p‖ ^ 2)` | `⊢ P (∑ i, p.val 3 i ^ 2)` |

**R34 · `nlinarith [h]`** **closes** a polynomial equation or inequality that follows from the listed facts by
adding and multiplying them (`linarith` is the linear version). After R15 the goal of Part 4 says
$3r^2 - 3(x_0^2 + x_1^2 + x_2^2) = r^5 \cdot 0$, which follows from `h`. Placeholders: `(r a b : ℝ)`.

| Before | After |
|---|---|
| `h : r ^ 2 = a ^ 2 + b ^ 2 ⊢ r ^ 2 - a ^ 2 + (r ^ 2 - b ^ 2) = r ^ 2` | no goals |

**W1** in the guide evaluates a derivative fact at `basis i` with R3, R9, R10, and `simp` (R11–R14):

```lean-goal
⊢ Space.deriv i (fun y => ‖y‖ ^ 2) x = 2 * x.val 3 i
⊢ (2 • (innerSL ℝ) x) (basis i) = 2 * x.val 3 i
```

---

## Traps

- Every derivative fact here needs `x ≠ 0`. Start each milestone with `have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx`
  (R1): `positivity` and `field_simp` find their nonzero facts in the context, not in `hx`.
- `rw [h.fderiv]` (R10) needs the function in `h` to be the goal's function as written. `.sqrt` gives
  `fun y => √(‖y‖ ^ 2)` (fix it with R5, R7, R8), and `.comp_hasFDerivAt` gives `g ∘ f` (state the `have`
  with the lambda, R20).
- `hasDerivAt_pow 3` says `↑3 * a ^ (3 - 1)`. When you state the composite in a `have`, write `↑3 * ‖x‖ ^ 2`:
  Lean accepts it (`3 - 1` computes to `2`) and later goals stay readable.
- The `2` in `2 • innerSL ℝ x` is a natural number: in a `have`, write `(2 : ℕ) • …` so your statement uses
  the same scalar as the lemma's (a real `2` gives an equal map, but not the same term).
- Under `open Space`, `smul_apply` is `Space.smul_apply`; for a linear map write `_root_.smul_apply` (R11).
- In Part 3, after the product rule the goal has two different products `c₁ • 1` and `c₂ • x i`:
  `rw [smul_eq_mul]` rewrites only the first, and `field_simp`/`ring` then fail on the leftover `•`.
  Use `simp only [smul_eq_mul]` (R12, R31).
- The summand `fun y => (‖y‖ ^ 3)⁻¹ * y i` is not syntactically `c • f`; `Space.deriv_smul` matches only
  after `change` (R24).
- `rw` cannot rewrite inside `∑ i, …` (the `i` is bound); use `simp only` (R31).
- `t1 ; t2` runs `t2` on the first goal only; `t1 <;> t2` on all goals (TACTIC_STATES, "Structure").

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `0 < ‖x‖` from `x ≠ 0` | `have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx` | R1 |
| side goal `0 < e`, `e ≠ 0` | `(by positivity)` | R2 |
| derivative of `‖y‖ ^ 2` | `(hasStrictFDerivAt_norm_sq x).hasFDerivAt` | R3 |
| derivative of `√(f y)` | `hf.sqrt (by positivity)` | R4 |
| equal functions | `funext y`; `exact Real.sqrt_sq (norm_nonneg y)` | R5, R6, R7 |
| rewrite a hypothesis | `rw [e] at h` | R8 |
| `∂[i] f x` as a derivative map | `rw [Space.deriv_eq]` (back: `rw [← Space.deriv_eq]`) | R9 |
| replace `fderiv` by a known map | `rw [h.fderiv]` | R10 |
| evaluate `(c • L) v`, `•` on numbers | `_root_.smul_apply`, `smul_eq_mul`, `nsmul_eq_mul` | R11, R12 |
| evaluate `innerSL`, `⟪p, basis i⟫_ℝ` | `simp` (uses `coe_innerSL_apply`, `Space.inner_basis`) | R13, R14 |
| clear denominators | `field_simp` (needs `hn` in context) | R15 |
| `‖·‖` differentiable at `x ≠ 0` | `DifferentiableAt.norm ℝ differentiableAt_id hx` | R16 |
| derivative of `r ^ n`, of `(c r)⁻¹` | `hasDerivAt_pow n a`, `hc.fun_inv (by positivity)` | R17, R18 |
| chain rule `ℝ → ℝ` after `E → ℝ` | `hg.comp_hasFDerivAt x hd.hasFDerivAt` | R19, R20 |
| `r ^ n ≠ 0` | `(pow_pos hn n).ne'` | R21 |
| differentiable `(f ^ n)⁻¹` | `(hd.pow n).inv hne` | R22 |
| differentiable coordinates etc. | `by fun_prop` | R23 |
| product as `c • f` | `change ∂[i] ((fun y => …) • fun y => …) x = _` | R24 |
| product rule | `rw [Space.deriv_smul hc hf]` | R25 |
| `∂[i] (fun y => y i) x = 1` | `rw [Space.deriv_component_same]` | R26 |
| polynomial identity | `ring` | R27 |
| divergence → sum | `unfold Space.div` | R28 |
| components of `c • basis.repr y` | `simp only [PiLp.smul_apply, Space.basis_repr_apply, smul_eq_mul]` | R29, R30, R31 |
| sum over `Fin 3` | `Fin.sum_univ_three` | R32 |
| `‖x‖ ^ 2 = ∑ i, x i ^ 2` | `have h := Space.norm_sq_eq x` | R33 |
| polynomial goal from `h` | `nlinarith [h]` | R34 |
| see the state | infoview | |
