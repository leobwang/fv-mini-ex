# H110 · Plane waves solve the wave equation: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `rw`, `simp`, `simp only`, `have`,
`funext`, `ring`, `norm_num`, anonymous functions `fun x => …`. **New here:** Mathlib's Fréchet
derivative `fderiv` and the one-variable `deriv`, `iteratedDeriv`, `ContDiff`, `Differentiable`,
continuous linear maps `E →L[ℝ] F`, the `fun_prop` tactic, real inner products `⟪·,·⟫_ℝ`,
`EuclideanSpace`; and physlib's `Time`, `Space d`, `Direction d`, the derivatives `∂ₜ`, `∂[i]`, the
Laplacians `Δ`, `Δᵥ`, `planeWave` and `WaveEquation`.

**The physics, in symbols.** `d : ℕ` is the space dimension, `t` a time, `x ∈ ℝ^d` a point, `c : ℝ`
the wave speed, `s ∈ ℝ^d` a unit vector (`‖s‖ = 1`, the direction of travel) and `f₀ : ℝ → ℝ^d` a
twice continuously differentiable profile. The plane wave is $f(t, x) = f_0(\langle x, s\rangle - c t)$.
Write $\xi = \langle x, s\rangle - c t$ and $f_0', f_0''$ for the first and second derivatives.
- Time: $\partial_t f = -c\, f_0'(\xi)$, so $\partial_t^2 f = c^2 f_0''(\xi)$ (two chain rules, each pulls out $-c$).
- Space: $\partial_i f = s_i\, f_0'(\xi)$, so $\partial_i^2 f = s_i^2 f_0''(\xi)$ and
  $\Delta f = \sum_i \partial_i^2 f = \|s\|^2 f_0''(\xi) = f_0''(\xi)$.
- Hence $c^2 \Delta f - \partial_t^2 f = c^2 f_0'' - c^2 f_0'' = 0$: physlib's `WaveEquation`.

The milestones are exactly these steps: two chain rules for a general `g` (Parts 1, 2), used with
`g = f₀` and `g = deriv f₀` to get $\partial_t^2 f$ (Part 3) and $\Delta f$ (Part 4); Part 5 subtracts.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal.
- Placeholders are written as Lean binders. `{F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]` means
  "`F` is a real normed vector space" (a type with `+`, `-`, `0`, a norm `‖·‖` and real scalars `•`);
  `ℝ`, `Time`, `Space d` and `EuclideanSpace ℝ (Fin d)` all qualify. `[InnerProductSpace ℝ E]` adds a
  real inner product `⟪·,·⟫_ℝ`; `Space d` and `EuclideanSpace ℝ (Fin d)` qualify.
- Fact-building entries (`hg y`, `hf.differentiable …`) are shown as `have h := …`, so the context gains
  `h` and you see its type. `hf.differentiable` is dot notation for `ContDiff.differentiable hf`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `t : Time` | a time; a structure wrapping one real number `t.val : ℝ`. `Time.val : Time → ℝ` is that projection as a function (as in `fderiv ℝ Time.val t`, R10) |
| `x : Space d` | a point of `ℝ^d`; a structure wrapping `x.val : Fin d → ℝ`. `x.val i` is its `i`-th coordinate |
| `s : Direction d` | a unit vector: `s.unit : Space d` with the proof `s.norm : ‖s.unit‖ = 1` |
| `EuclideanSpace ℝ (Fin d)` | `ℝ^d` as the values of the field `f₀`; `v.ofLp j` is the `j`-th component of `v` |
| `WithLp.toLp 2 u` | the vector of `EuclideanSpace ℝ (Fin d)` whose components are `u : Fin d → ℝ` |
| `⟪x, y⟫_ℝ` | the real inner (dot) product $\sum_i x_i y_i$ |
| `‖p‖` | the Euclidean norm of `p` |
| `planeWave f₀ c s t x` | `f₀ (⟪x, s.unit⟫_ℝ - c * t.val)` (R23); `planeWave f₀ c s t` is the field at time `t` (R30) |
| `fderiv ℝ f x` | the derivative of `f : E → F` at `x`, a continuous linear map `E →L[ℝ] F` |
| `(fderiv ℝ f x) v` | that map applied to the direction `v`: the directional derivative of `f` at `x` along `v` |
| `E →L[ℝ] F` | continuous `ℝ`-linear maps from `E` to `F` |
| `L ∘SL M` | composition of continuous linear maps (`L.comp M`), so `(L ∘SL M) v = L (M v)` (R6) |
| `ContinuousLinearMap.id ℝ E` | the identity map of `E` |
| `_root_.deriv f x` | for `f : ℝ → F`, the ordinary derivative $f'(x) \in F$. Printed with `_root_.` because `Space.deriv` and `Time.deriv` are open as well |
| `iteratedDeriv n f` | the `n`-th derivative $f^{(n)}$ as a function (R20, R21) |
| `∂ₜ f t` | physlib's time derivative `Time.deriv f t = fderiv ℝ f t 1` (R1) |
| `∂[i] f x`, printed `Space.deriv i f x` | physlib's partial derivative $\partial_i f(x)$ `= fderiv ℝ f x (Space.basis i)` (R12) |
| `Space.basis i` | the `i`-th standard unit vector of `Space d` |
| `Δ f` | physlib's Laplacian of a scalar field `f : Space d → ℝ`: $\sum_i \partial_i\partial_i f$ (R37) |
| `Δᵥ F x` | the vector Laplacian: the Laplacian of each component of `F : Space d → EuclideanSpace ℝ (Fin d)` (R35) |
| `ContDiff ℝ 2 f` | `f` is twice continuously differentiable ($C^2$). The `2` lives in `WithTop ℕ∞` (ℕ plus ∞ and ω) |
| `Differentiable ℝ f`, `DifferentiableAt ℝ f x` | differentiable everywhere; at `x`. The first is `∀ x, DifferentiableAt ℝ f x` (R3) |
| `c • v` | the real number `c` times the vector `v` |
| `-c • v`, `a • b • v` | `(-c) • v` and `a • (b • v)`: `-` binds tighter than `•`, and `•` groups to the right (R26) |
| `WaveEquation f t x c` | `c ^ 2 • Δᵥ (f t) x - ∂ₜ (fun t => ∂ₜ (fun t => f t x) t) t = 0` (R43) |
| `∑ i, f i` | the sum over all `i : Fin d` |
| `∑ x_1, …` | the same sum; Lean renamed the bound index to `x_1` because `x` is already in the context |

---

## Part 1 · `time_deriv_comp`

Statement: for differentiable `g : ℝ → EuclideanSpace ℝ (Fin d)` and `a c : ℝ`,
`∂ₜ (fun τ : Time => g (a - c * τ.val)) t = -c • deriv g (a - c * t.val)`, i.e.
$\frac{d}{dt} g(a - c t) = -c\, g'(a - c t)$.

### The time derivative as a linear map

**R1 · `rw [Time.deriv_eq]`** changes the **goal**: `∂ₜ f t` becomes the derivative map of `f` at `t`
applied to the unit time step `1`. Lemma: `∂ₜ f t = (fderiv ℝ f t) 1`. Placeholders:
`{F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Time → F) (t : Time)`.

| Before | After |
|---|---|
| `⊢ P (∂ₜ f t)` | `⊢ P ((fderiv ℝ f t) 1)` |

**R2 · `change G'`** changes the **goal** to `G'`, which must be equal to the goal by unfolding
definitions. Here it writes `fun x => g (f x)` as `g ∘ f`, the form the chain rule R5 matches.
Write `_` for the parts that stay (`change fderiv ℝ (g ∘ fun τ : Time => …) t 1 = _`).
Placeholders: `{E F G : Type} (f : E → F) (g : F → G)`.

| Before | After |
|---|---|
| `⊢ P fun x => g (f x)` | `⊢ P (g ∘ f)` |

**R3 · `hg y`** changes the **context**: from `hg : Differentiable ℝ g` (which is `∀ y, DifferentiableAt ℝ g y`)
you get differentiability at the point `y`. Inside a `rw [fderiv_comp _ (hg _) …]` write `hg _` and Lean
finds the point. Placeholders: `(g : F → G) (y : F)`, `F G` real normed spaces.

| Before | After |
|---|---|
| `⊢ DifferentiableAt ℝ g y` | `h : DifferentiableAt ℝ g y ⊢ DifferentiableAt ℝ g y` |

**R4 · `fun_prop`** **closes** a goal `Differentiable ℝ f` or `DifferentiableAt ℝ f x` when `f` is built
from pieces it knows: `+`, `-`, `*`, `•`, composition, constants, `Time.val`, `⟪·,·⟫_ℝ`, and functions
whose differentiability is a hypothesis in the context. Example: with `hf : Differentiable ℝ f`, it closes
`⊢ DifferentiableAt ℝ (fun τ => a • f (b * τ.val)) t`. It fails (no partial progress) when a piece is
missing, typically because the hypothesis such as `h1 : Differentiable ℝ f₀` is not in the context yet.

### The chain rule

**R5 · `rw [fderiv_comp x hg hf]`** changes the **goal**. Lemma (chain rule):
`DifferentiableAt ℝ g (f x) → DifferentiableAt ℝ f x → fderiv ℝ (g ∘ f) x = fderiv ℝ g (f x) ∘SL fderiv ℝ f x`.
Placeholders: `{E F G : Type}` real normed spaces, `(f : E → F) (g : F → G) (x : E)`. Write `_` for `x`
and give the two hypotheses as `(hg _)` (R3) and `(by fun_prop)` (R4).

| Before | After |
|---|---|
| `⊢ P (fderiv ℝ (g ∘ f) x)` | `⊢ P (fderiv ℝ g (f x) ∘SL fderiv ℝ f x)` |

**R6 · `rw [ContinuousLinearMap.comp_apply]`** changes the **goal**: a composed map applied to `v` becomes
the outer map applied to the inner result. Placeholders: `(L : F →L[ℝ] G) (M : E →L[ℝ] F) (v : E)`.

| Before | After |
|---|---|
| `⊢ P ((L ∘SL M) v)` | `⊢ P (L (M v))` |

**R7 · `rw [fderiv_eq_smul_deriv]`** changes the **goal**. For a function of **one real variable**
`f : ℝ → F`, the derivative map is "multiply by the ordinary derivative":
`(fderiv ℝ f x) y = y • deriv f x`. Placeholders: `(f : ℝ → F) (x y : ℝ)`.
Use it on the outer derivative `fderiv ℝ g (…)` after R6.

| Before | After |
|---|---|
| `⊢ P ((fderiv ℝ f x) y)` | `⊢ P (y • _root_.deriv f x)` |

### The inner function `τ ↦ a - c * τ.val`

**R8 · `rw [fderiv_const_sub]`** changes the **goal**. Lemma: `fderiv ℝ (fun y => c - f y) x = -fderiv ℝ f x`.
Placeholders: `(f : E → F) (c : F) (x : E)`. No differentiability hypothesis needed.

| Before | After |
|---|---|
| `⊢ P (fderiv ℝ (fun y => c - f y) x)` | `⊢ P (-fderiv ℝ f x)` |

**R9 · `rw [fderiv_const_mul ha]`** changes the **goal**. Lemma:
`DifferentiableAt ℝ a x → fderiv ℝ (fun y => b * a y) x = b • fderiv ℝ a x`. Placeholders:
`(a : E → ℝ) (b : ℝ) (x : E)`; `ha` is usually `(by fun_prop)`.

| Before | After |
|---|---|
| `⊢ P (fderiv ℝ (fun y => b * a y) x)` | `⊢ P (b • fderiv ℝ a x)` |

**R10 · `Time.fderiv_val`** changes the **goal**: the derivative of `Time.val` in the direction `1` is `1`.
Lemma: `(fderiv ℝ Time.val t) 1 = 1`. `simp` applies it by itself. Placeholders: `(t : Time)`.

| Before | After |
|---|---|
| `⊢ P ((fderiv ℝ Time.val t) 1)` | `⊢ P 1` |

**R11 · `_root_.neg_apply`, `_root_.smul_apply`** change the **goal**: evaluating a negated or scaled
linear map, `(-L) v = -L v` and `(c • L) v = c • L v`. `simp` applies both by itself. To `rw` with them,
write the `_root_.` prefix: with `open Space`, plain `smul_apply` means `Space.smul_apply` (coordinates of
`c • p` for a point `p`). Placeholders: `(L : E →L[ℝ] F) (c : ℝ) (v : E)`.

| Before | After `rw [_root_.neg_apply]` | After `rw [_root_.smul_apply]` |
|---|---|---|
| `⊢ P ((-(c • L)) v)` | `⊢ P (-(c • L) v)` | `⊢ P (-(c • L v))` |

After R8, R9 the milestone's goal is `(-(c • fderiv ℝ Time.val t)) 1 • deriv g (…) = -c • deriv g (…)`;
a plain `simp` closes it with R11, R10 and `neg_smul`.

**W1: the chain without the constant.** `∂ₜ (fun τ => g (c * τ.val)) t = c • deriv g (c * t.val)`, by
R1, R2, R5, R6, R7, R9, then `simp`:

```lean-goal
⊢ ∂ₜ (fun τ => g (c * τ.val)) t = c • _root_.deriv g (c * t.val)
⊢ (fderiv ℝ (fun τ => g (c * τ.val)) t) 1 = c • _root_.deriv g (c * t.val)
⊢ (fderiv ℝ (g ∘ fun τ => c * τ.val) t) 1 = c • _root_.deriv g (c * t.val)
⊢ (fderiv ℝ g (c * t.val) ∘SL fderiv ℝ (fun τ => c * τ.val) t) 1 = c • _root_.deriv g (c * t.val)
⊢ (fderiv ℝ g (c * t.val)) ((fderiv ℝ (fun τ => c * τ.val) t) 1) = c • _root_.deriv g (c * t.val)
⊢ (fderiv ℝ (fun τ => c * τ.val) t) 1 • _root_.deriv g (c * t.val) = c • _root_.deriv g (c * t.val)
⊢ (c • fderiv ℝ Time.val t) 1 • _root_.deriv g (c * t.val) = c • _root_.deriv g (c * t.val)
```

---

## Part 2 · `space_deriv_comp`

Statement: for differentiable `g`, `u : Space d`, `b : ℝ`,
`∂[i] (fun y : Space d => g (⟪y, u⟫_ℝ - b)) x = u i • deriv g (⟪x, u⟫_ℝ - b)`, i.e.
$\partial_i\, g(\langle y, u\rangle - b) = u_i\, g'(\langle x, u\rangle - b)$. In the infoview `u i` shows as
`u.val i`. Same shape as Part 1: R12 instead of R1, then R2, R5 (R3, R4), R6, R7, then the inner function.

**R12 · `rw [Space.deriv_eq]`** changes the **goal**: the partial derivative `∂[i] f x` becomes the
derivative map applied to the unit vector `Space.basis i`. Lemma:
`Space.deriv i f x = (fderiv ℝ f x) (Space.basis i)`. Placeholders: `(f : Space d → F) (i : Fin d) (x : Space d)`.
`rw [← Space.deriv_eq]` goes back (used in Part 4).

| Before | After |
|---|---|
| `⊢ P (Space.deriv i f x)` | `⊢ P ((fderiv ℝ f x) (Space.basis i))` |

**R13 · `rw [fderiv_sub_const]`** changes the **goal**. Lemma: `fderiv ℝ (fun y => f y - c) x = fderiv ℝ f x`.
Placeholders: `(f : E → F) (c : F) (x : E)`.

| Before | After |
|---|---|
| `⊢ P (fderiv ℝ (fun y => f y - c) x)` | `⊢ P (fderiv ℝ f x)` |

**R14 · `rw [fderiv_inner_apply ℝ hf hg]`** changes the **goal**: the product rule for the inner product,
`(fderiv ℝ (fun y => ⟪f y, g y⟫_ℝ) x) v = ⟪f x, (fderiv ℝ g x) v⟫_ℝ + ⟪(fderiv ℝ f x) v, g x⟫_ℝ`.
The scalar field `ℝ` is an **explicit** first argument; `hf hg` are `DifferentiableAt` facts, usually
`(by fun_prop) (by fun_prop)`. Placeholders: `{E G : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]`,
`G` a real normed space, `(f g : G → E) (x v : G)`. In the milestone `f = fun y => y` and `g = fun y => u`.

| Before | After |
|---|---|
| `⊢ P ((fderiv ℝ (fun y => ⟪f y, g y⟫_ℝ) x) v)` | `⊢ P (⟪f x, (fderiv ℝ g x) v⟫_ℝ + ⟪(fderiv ℝ f x) v, g x⟫_ℝ)` |

After R14 the milestone's goal is
`(⟪x, (fderiv ℝ (fun y => u) x) (Space.basis i)⟫_ℝ + ⟪(fderiv ℝ (fun y => y) x) (Space.basis i), u⟫_ℝ) • … = u.val i • …`.
A plain `simp` closes it with R15, R16, R17 (and `inner_zero_right`, `zero_add`).

**R15 · `fderiv_fun_const`** changes the **goal**: a constant function has derivative `0`.
Lemma: `(fderiv ℝ fun x => u) = 0`. Placeholders: `(u : F)`.

| Before | After |
|---|---|
| `⊢ P (fderiv ℝ fun x => u)` | `⊢ P 0` |

**R16 · `fderiv_fun_id`** changes the **goal**: the identity function has the identity map as derivative.
Placeholders: `(x : E)`.

| Before | After |
|---|---|
| `⊢ P (fderiv ℝ (fun y => y) x)` | `⊢ P (ContinuousLinearMap.id ℝ E)` |

**R17 · `Space.basis_inner`** changes the **goal**: the inner product with the `i`-th unit vector picks
the `i`-th coordinate. Lemma: `⟪Space.basis i, p⟫_ℝ = p.val i`. Placeholders: `(p : Space d) (i : Fin d)`.

| Before | After |
|---|---|
| `⊢ P ⟪Space.basis i, p⟫_ℝ` | `⊢ P (p.val i)` |

**W2: a scalar profile, no constant.** For `g : ℝ → ℝ`,
`∂[i] (fun y => g ⟪y, u⟫_ℝ) x = u.val i * deriv g ⟪x, u⟫_ℝ` by R12, R2, R5, R6, R7, R14, then `simp`:

```lean-goal
⊢ (fderiv ℝ (g ∘ fun y => ⟪y, u⟫_ℝ) x) (Space.basis i) = u.val i * _root_.deriv g ⟪x, u⟫_ℝ
⊢ (fderiv ℝ (fun y => ⟪y, u⟫_ℝ) x) (Space.basis i) • _root_.deriv g ⟪x, u⟫_ℝ = u.val i * _root_.deriv g ⟪x, u⟫_ℝ
⊢ (⟪x, (fderiv ℝ (fun y => u) x) (Space.basis i)⟫_ℝ + ⟪(fderiv ℝ (fun y => y) x) (Space.basis i), u⟫_ℝ) • _root_.deriv g ⟪x, u⟫_ℝ = u.val i * _root_.deriv g ⟪x, u⟫_ℝ
```

---

## Part 3 · `time_deriv_time_deriv`

Statement: for `hf₀ : ContDiff ℝ 2 f₀`,
`∂ₜ (fun τ => ∂ₜ (fun τ => planeWave f₀ c s τ x) τ) t = c ^ 2 • iteratedDeriv 2 f₀ (⟪x, s.unit⟫_ℝ - c * t.val)`,
i.e. $\partial_t^2 f = c^2 f_0''(\xi)$. Uses Part 1 twice: with `g = f₀`, then with `g = deriv f₀`.

### Differentiability from `C²`

**R18 · `hf.differentiable (by simp)`** changes the **context**. Lemma `ContDiff.differentiable`:
`ContDiff ℝ n f → n ≠ 0 → Differentiable ℝ f`; `simp` proves `2 ≠ 0`. Placeholders: `(f : ℝ → F)`.

| Before | After |
|---|---|
| `⊢ Differentiable ℝ f` | `h : Differentiable ℝ f ⊢ Differentiable ℝ f` |

**R19 · `hf.differentiable_iteratedDeriv 1 (by norm_num)`** changes the **context**. Lemma
`ContDiff.differentiable_iteratedDeriv`: `ContDiff ℝ n f → ↑m < n → Differentiable ℝ (iteratedDeriv m f)`;
`norm_num` proves `↑1 < 2`. So a `C²` function has a differentiable first derivative.

| Before | After |
|---|---|
| `⊢ Differentiable ℝ (iteratedDeriv 1 f)` | `h : Differentiable ℝ (iteratedDeriv 1 f) ⊢ Differentiable ℝ (iteratedDeriv 1 f)` |

**R20 · `rw [iteratedDeriv_one]`** changes the **goal**: `iteratedDeriv 1 f = deriv f`.

| Before | After |
|---|---|
| `⊢ P (iteratedDeriv 1 f)` | `⊢ P (_root_.deriv f)` |

**R21 · `rw [iteratedDeriv_succ]`** changes the **goal**: `iteratedDeriv (n + 1) f = deriv (iteratedDeriv n f)`.
Lean matches `2` against `n + 1`, so `rw [iteratedDeriv_succ, iteratedDeriv_one]` turns
`iteratedDeriv 2 f` into `deriv (deriv f)`.

| Before | After |
|---|---|
| `⊢ P (iteratedDeriv 2 f)` | `⊢ P (_root_.deriv (iteratedDeriv 1 f))` |

**R22 · `simpa [l] using e`** **closes** the goal: it simplifies both `e` and the goal with `simp [l]` and
then closes the goal with the simplified `e`. With `l = iteratedDeriv_one` and `e` from R19 it closes
`⊢ Differentiable ℝ (_root_.deriv f)`.

### Two time derivatives

**R23 · `simp only [planeWave_eq]`** changes the **goal**: `planeWave f₀ c s t x` becomes
`f₀ (⟪x, s.unit⟫_ℝ - c * t.val)`. Placeholders: `(f₀ : ℝ → EuclideanSpace ℝ (Fin d)) (c : ℝ) (s : Direction d) (t : Time) (x : Space d)`.

| Before | After |
|---|---|
| `⊢ P (planeWave f₀ c s t x)` | `⊢ P (f₀ (⟪x, s.unit⟫_ℝ - c * t.val))` |

**R24 · `simp only [h]`** changes the **goal**: it rewrites with `h` also **under a `fun` binder**, where
`rw [h]` fails (the instance `f y` mentions the bound `y`, and `rw` cannot abstract it). In the milestone
the inner `∂ₜ (fun τ => …) τ` sits inside `fun τ => …`, so apply Part 1 there with
`simp only [planeWave_eq, time_deriv_comp f₀ h1]`. Placeholders: `(f g : ℝ → ℝ) (hfg : ∀ y, f y = g y)`.

| Before | After |
|---|---|
| `⊢ P fun y => f y * 2` | `⊢ P fun y => g y * 2` |

**R25 · `rw [Time.deriv_smul _ _ hf]`** changes the **goal**: a constant factor comes out of `∂ₜ`.
Lemma: `Differentiable ℝ f → ∂ₜ (fun t => k • f t) t = k • ∂ₜ (fun t => f t) t`, only for
`f : Time → EuclideanSpace ℝ (Fin d)`; `hf` is usually `(by fun_prop)`. Placeholders: `(k : ℝ) (t : Time)`.

| Before | After |
|---|---|
| `⊢ P (∂ₜ (fun τ => k • f τ) t)` | `⊢ P (k • ∂ₜ (fun t => f t) t)` |

**R26 · `rw [smul_smul]`** changes the **goal**: two scalings merge, `a • b • v = (a * b) • v`.
Placeholders: `(a b : ℝ) (v : F)`.

| Before | After |
|---|---|
| `⊢ P (a • b • v)` | `⊢ P ((a * b) • v)` |

**R27 · `ring_nf`** **closes** `⊢ (-a * -a) • v = a ^ 2 • v`: it puts the scalar on each side in ring normal
form (`-a * -a` and `a ^ 2` both become `a ^ 2`), after which the sides agree. The goal is an equation of
vectors, not of numbers, so `ring` itself cannot prove it: it falls back to `ring_nf` and says
"Try this: ring_nf".

---

## Part 4 · `laplacianVec_planeWave`

Statement: `Δᵥ (planeWave f₀ c s t) x = iteratedDeriv 2 f₀ (⟪x, s.unit⟫_ℝ - c * t.val)`, i.e.
$\Delta f = f_0''(\xi)$. Uses Part 2 twice: with `g = f₀` (first derivative `hd`), with `g = deriv f₀`
(second derivative `hdd`).

### The second partial derivative `∂ᵢ∂ᵢ f`

After `rw [hd]` and R12 the goal holds `fderiv ℝ (fun y => s.unit.val i • deriv f₀ (…)) x (Space.basis i)`.

**R28 · `rw [fderiv_fun_const_smul hf]`** changes the **goal**: a constant scalar comes out of `fderiv`.
Lemma: `DifferentiableAt ℝ f x → fderiv ℝ (fun y => c • f y) x = c • fderiv ℝ f x`; `hf` is usually
`(by fun_prop)`. Placeholders: `(f : E → F) (c : ℝ) (x : E)`. Then R11 (`_root_.smul_apply`) moves `c`
outside the application, and `rw [← Space.deriv_eq]` (R12 backwards) turns what is left into `∂[i] … x`, the
form Part 2 matches.

| Before | After |
|---|---|
| `⊢ P (fderiv ℝ (fun y => c • f y) x)` | `⊢ P (c • fderiv ℝ f x)` |

**R29 · `rw [pow_two]`** changes the **goal**: `a ^ 2 = a * a`. Use it so the right side's `s.unit.val i ^ 2`
matches the `s.unit.val i * s.unit.val i` that R26 produces on the left.

| Before | After |
|---|---|
| `⊢ P (a ^ 2)` | `⊢ P (a * a)` |

**R30 · `unfold planeWave`** changes the **goal**: the name becomes its body, so `fun_prop` (R4) can see
the pieces. Needed for `hF : Differentiable ℝ (planeWave f₀ c s t)`.

| Before | After |
|---|---|
| `⊢ P (planeWave f₀ c s t)` | `⊢ P fun x => f₀ (⟪x, s.unit⟫_ℝ - c * t.val)` |

### The unit vector: `∑ i, sᵢ² = 1`

**R31 · `rw [← Space.norm_sq_eq]`** changes the **goal**. Lemma: `‖p‖ ^ 2 = ∑ i, p.val i ^ 2`; right to left
it folds the sum of squared coordinates into the squared norm. Placeholders: `(p : Space d)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, p.val i ^ 2)` | `⊢ P (‖p‖ ^ 2)` |

**R32 · `rw [s.norm]`** changes the **goal**: `s.norm : ‖s.unit‖ = 1` is the field of `s : Direction d`.

| Before | After |
|---|---|
| `⊢ P ‖s.unit‖` | `⊢ P 1` |

**R33 · `rw [one_pow]`** changes the **goal**: `1 ^ n = 1`.

| Before | After |
|---|---|
| `⊢ P (1 ^ n)` | `⊢ P 1` |

**W3.** With `hu : ‖u‖ = 2`: R31, `rw [hu]`, `norm_num`.

```lean-goal
⊢ ∑ i, u.val i ^ 2 = 4
⊢ ‖u‖ ^ 2 = 4
⊢ 2 ^ 2 = 4
```

### Component by component

**R34 · `ext j`** changes the **goal and the context**: two vectors of `EuclideanSpace ℝ (Fin d)` are equal
when all components are. Placeholders: `(v w : EuclideanSpace ℝ (Fin d))`.

| Before | After |
|---|---|
| `⊢ v = w` | `j : Fin d ⊢ v.ofLp j = w.ofLp j` |

**R35 · `simp only [laplacianVec]`** changes the **goal**: `Δᵥ` is defined componentwise, as the vector of
the scalar Laplacians of the components. Placeholders: `(F : Space d → EuclideanSpace ℝ (Fin d)) (x : Space d)`.

| Before | After |
|---|---|
| `⊢ P (Δᵥ F x)` | `⊢ P (WithLp.toLp 2 fun i => Δ (fun x => (F x).ofLp i) x)` |

**R36 · `PiLp.toLp_apply`** changes the **goal**: the `i`-th component of `WithLp.toLp 2 u` is `u i`.
Placeholders: `(u : Fin d → ℝ) (i : Fin d)`.

| Before | After |
|---|---|
| `⊢ P ((WithLp.toLp 2 u).ofLp i)` | `⊢ P (u i)` |

**R37 · `laplacian_eq_sum_snd_deriv`** changes the **goal**: the scalar Laplacian is the sum of the second
partial derivatives. Lemma: `Δ f = fun x => ∑ i, Space.deriv i (Space.deriv i f) x`. Placeholders:
`(f : Space d → ℝ)`. Inside `simp only` the resulting `(fun x => …) x` is substituted at once.

| Before | After |
|---|---|
| `⊢ P (Δ f)` | `⊢ P fun x => ∑ i, Space.deriv i (Space.deriv i f) x` |

After `ext j; simp only [laplacianVec, laplacian_eq_sum_snd_deriv, PiLp.toLp_apply]` the milestone's goal is
`∑ i, ∂[i] (∂[i] fun x => (planeWave f₀ c s t x).ofLp j) x = (iteratedDeriv 2 f₀ (…)).ofLp j`:
the derivatives act on the `j`-th component, but `hdd` is about the whole vector. R38 moves `j` out.

**R38 · `rw [Space.deriv_euclid hF]`** changes the **goal**: the derivative of a component is the component of
the derivative. Lemma: `Differentiable ℝ F → ∂[i] (fun y => (F y).ofLp j) x = (∂[i] (fun y => F y) x).ofLp j`.
Placeholders: `(F : Space d → EuclideanSpace ℝ (Fin d)) (hF : Differentiable ℝ F) (i j : Fin d) (x : Space d)`.
For the inner `∂[i]` it sits under `fun`, so state it as an equation of functions first
(`hc`, by `funext` and `exact Space.deriv_euclid hF y`); for the outer one use `Space.deriv_euclid (hF' _)`.

| Before | After |
|---|---|
| `⊢ P (Space.deriv i (fun y => (F y).ofLp j) x)` | `⊢ P ((Space.deriv i (fun x => F x) x).ofLp j)` |

**R39 · `PiLp.smul_apply`** changes the **goal**: `(c • v).ofLp j = c • v.ofLp j`.
Placeholders: `(c : ℝ) (v : EuclideanSpace ℝ (Fin d)) (j : Fin d)`.

| Before | After |
|---|---|
| `⊢ P ((c • v).ofLp j)` | `⊢ P (c • v.ofLp j)` |

**R40 · `smul_eq_mul`** changes the **goal**: for two numbers, `a • b = a * b`.

| Before | After |
|---|---|
| `⊢ P (a • b)` | `⊢ P (a * b)` |

**R41 · `← Finset.sum_mul`** changes the **goal**. Lemma: `(∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a`; right to
left it pulls the common factor `a` (here the `j`-th component of `f₀''(ξ)`) out of the sum, leaving
`∑ i, s.unit.val i ^ 2`, which `hsum` rewrites to `1`. Placeholders: `(f : Fin d → ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i * a)` | `⊢ P ((∑ i, f i) * a)` |

**R42 · `one_mul`** changes the **goal**: `1 * a = a`.

| Before | After |
|---|---|
| `⊢ P (1 * a)` | `⊢ P a` |

---

## Part 5 · `planeWave_solves`

Statement: `WaveEquation (planeWave f₀ c s) t x c`. Unfold it, substitute Parts 4 and 3, and the two sides
are the same vector `c ^ 2 • f₀''(ξ)`.

**R43 · `rw [WaveEquation]`** changes the **goal**: the predicate becomes its defining equation.
Placeholders: `(f : Time → Space d → EuclideanSpace ℝ (Fin d)) (t : Time) (x : Space d) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ WaveEquation f t x c` | `⊢ c ^ 2 • Δᵥ (f t) x - ∂ₜ (fun t => ∂ₜ (fun t => f t x) t) t = 0` |

**R44 · `rw [sub_self]`** changes the **goal**: `a - a = 0`. After it the goal is `0 = 0`, which `rw` closes
by itself.

| Before | After |
|---|---|
| `⊢ P (a - a)` | `⊢ P 0` |

---

## Traps

- `rw [h]` cannot rewrite under `fun τ => …` when the match mentions `τ` (R24). Inside `∂ₜ (fun τ => …)` and
  `∂[i] (fun y => …)`, use `simp only [h]`, or prove an equation of functions with `funext` first.
- `fderiv_comp` matches only `fderiv ℝ (g ∘ f) x`. The goal has `fun τ => g (…)`, so state the composition
  with `change` first (R2); `rw` does not see through `fun` to `∘`.
- `deriv` alone means `Space.deriv` or `Time.deriv` here (both namespaces are open). Write `_root_.deriv` in
  your own statements, as the infoview does. Likewise `_root_.smul_apply` (R11).
- `fun_prop` uses only what is in the context: prove `h1 : Differentiable ℝ f₀` and
  `h2 : Differentiable ℝ (deriv f₀)` before calling it. On `planeWave f₀ c s t` it may need `unfold planeWave`
  first (R30).
- `exact` sees through definitions, `rw` does not: `exact space_deriv_comp f₀ h1 _ _ i y` proves a goal about
  `∂[i] (planeWave f₀ c s t) y` because `planeWave` unfolds to the composed function definitionally.
- A `have` belongs to one proof: `h1`, `h2` must be proved again in each milestone that needs them.
- `ring` proves equations of numbers, not of vectors; for `(-c * -c) • v = c ^ 2 • v` write `ring_nf` (R27).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `∂ₜ f t` / `∂[i] f x` → `fderiv` | `rw [Time.deriv_eq]` / `rw [Space.deriv_eq]` | R1, R12 |
| `fun x => g (f x)` → `g ∘ f` | `change fderiv ℝ (g ∘ fun τ : Time => …) t 1 = _` | R2 |
| chain rule | `rw [fderiv_comp _ (hg _) (by fun_prop), ContinuousLinearMap.comp_apply]` | R5, R3, R4, R6 |
| one-variable derivative | `rw [fderiv_eq_smul_deriv]` | R7 |
| `c - f`, `f - c`, `b * a`, `c • f` | `fderiv_const_sub`, `fderiv_sub_const`, `fderiv_const_mul (by fun_prop)`, `fderiv_fun_const_smul (by fun_prop)` | R8, R13, R9, R28 |
| product rule for `⟪f, g⟫_ℝ` | `rw [fderiv_inner_apply ℝ (by fun_prop) (by fun_prop)]` | R14 |
| finish the chain rules | `simp` | R10, R11, R15–R17 |
| `C²` → differentiable `f`, `f'` | `hf.differentiable (by simp)`, `simpa [iteratedDeriv_one] using hf.differentiable_iteratedDeriv 1 (by norm_num)` | R18–R20, R22 |
| `iteratedDeriv 2 f` → `deriv (deriv f)` | `rw [iteratedDeriv_succ, iteratedDeriv_one]` | R21, R20 |
| unfold the plane wave | `simp only [planeWave_eq]` / `unfold planeWave` | R23, R30 |
| rewrite under `fun` | `simp only [h]` | R24 |
| scalar out of `∂ₜ` | `rw [Time.deriv_smul _ _ (by fun_prop)]` | R25 |
| `a • b • v` → `(a * b) • v` | `rw [smul_smul]` | R26 |
| scalars agree up to algebra | `ring_nf` | R27 |
| `∑ i, sᵢ² = 1` | `rw [← Space.norm_sq_eq, s.norm, one_pow]` | R31–R33 |
| vector equation → components | `ext j` | R34 |
| unfold `Δᵥ`, `Δ` | `simp only [laplacianVec, laplacian_eq_sum_snd_deriv, PiLp.toLp_apply]` | R35–R37 |
| component out of `∂[i]` | `Space.deriv_euclid hF` | R38 |
| collect `∑ i, sᵢ² * a` | `simp only [PiLp.smul_apply, smul_eq_mul, ← Finset.sum_mul, hsum, one_mul]` | R39–R42 |
| unfold the wave equation; finish | `rw [WaveEquation, …, sub_self]` | R43, R44 |
| see the state | infoview | |
