# M182 · The curl of a gradient vanishes: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's 3D space `Space`, its partial
derivatives `∂[μ]`, `grad` (`∇`) and `curl` (`∇ ⨯`); Mathlib's Fréchet derivative `fderiv`, continuous
linear maps `E →L[ℝ] F`, the vector type `EuclideanSpace ℝ (Fin 3)`, smoothness `ContDiff`, and the
symmetry of second derivatives `IsSymmSndFDerivAt` (Schwarz's theorem).

**The maths.** For $f : \mathbb{R}^3 \to \mathbb{R}$ of class $C^2$, component $i$ of $\nabla \times \nabla f$
is $\partial_{i+1}\partial_{i+2} f - \partial_{i+2}\partial_{i+1} f$ (indices mod 3), and mixed partials
commute (Schwarz), so every component is $0$. In Mathlib, the derivative of $f$ at $x$ is a linear map
$Df(x) : \mathbb{R}^3 \to \mathbb{R}$ (`fderiv ℝ f x`), and $\partial_\mu f(x) = Df(x)\,e_\mu$ where $e_\mu$ is
the $\mu$-th basis vector (`basis μ`). The second derivative $D^2 f(x)$ (`fderiv ℝ (fderiv ℝ f) x`) is a
bilinear map, and $\partial_\mu \partial_\nu f(x) = D^2 f(x)\,e_\mu\,e_\nu$. Schwarz says
$D^2 f(x)\,v\,w = D^2 f(x)\,w\,v$.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. `G : Prop` is a goal the step does not touch.
- Placeholders are written as Lean binders. `{E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]` says `E` is
  a real normed vector space; `Space`, `ℝ` and `EuclideanSpace ℝ (Fin 3)` all qualify.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Space` | `Space 3`, physlib's 3D space: a point with coordinates `Fin 3 → ℝ` |
| `Fin 3` | the indices `{0, 1, 2}`; `i + 1`, `i + 2` wrap around mod 3 |
| `∂[μ] g` (prints `Space.deriv μ g`) | the partial derivative $\partial g/\partial x_\mu$, a function `Space → ℝ`; `Space.deriv μ g x` is its value at `x` |
| `∇ f` | `Space.grad f`: the vector field $x \mapsto (\partial_0 f(x), \partial_1 f(x), \partial_2 f(x))$ |
| `∇ ⨯ F` (prints `curl F`) | `Space.curl F`, the curl of the vector field `F : Space → EuclideanSpace ℝ (Fin 3)` |
| `EuclideanSpace ℝ (Fin 3)` | $\mathbb{R}^3$ as a vector type (Lean name: `PiLp 2 (fun _ => ℝ)`, the Euclidean norm on `Fin 3 → ℝ`) |
| `WithLp.toLp 2 g` | the vector whose components are `g : Fin 3 → ℝ` (wraps a function as a vector) |
| `v.ofLp i` | component `i` of the vector `v` (unwraps); `WithLp.ofLp 0 i` is component `i` of the zero vector |
| `have fi := e; body` | inside a term: `body` with the local name `fi` standing for `e` (left over from `unfold`) |
| `E →L[ℝ] F` | continuous linear maps from `E` to `F` |
| `fderiv ℝ g x` | the Fréchet derivative $Dg(x)$, a map `E →L[ℝ] F`; `(fderiv ℝ g x) v` is the derivative along `v` |
| `fderiv ℝ (fderiv ℝ g) x` | the second derivative $D^2 g(x)$: `((fderiv ℝ (fderiv ℝ g) x) v) w` is $D^2 g(x)\,v\,w$ |
| `fun x => f x` | the function `f` itself, written out (η-expanded); R1 and `unfold` produce this form, and `rw`/`simp`/`exact` treat it as `f` |
| `fderiv ℝ fun x => f x` | `fderiv ℝ (fun x => f x)`, i.e. `fderiv ℝ f`: Lean drops the parentheses around a final `fun` argument |
| `basis μ` | `Space.basis μ`, the unit vector $e_\mu$ (an orthonormal basis of `Space`) |
| `A ∘SL B` | composition of continuous linear maps (`∘L` when written; `SL` is the general "semilinear" form) |
| `A.flip v w` | `A w v`: a two-argument map with its arguments swapped |
| `ContDiff ℝ 2 f` | `f` is $C^2$ (twice continuously differentiable) everywhere |
| `ContDiffAt ℝ 2 f x` | `f` is $C^2$ near the point `x` |
| `DifferentiableAt ℝ g x` | `g` is (Fréchet) differentiable at `x` |
| `IsSymmSndFDerivAt ℝ f x` | the second derivative of `f` at `x` is symmetric: $D^2 f(x)\,v\,w = D^2 f(x)\,w\,v$ |
| `minSmoothness ℝ 2` | the smoothness Schwarz needs over `ℝ`; it equals `2` (`simp` knows this) |

---

## Part 1 · milestone `mixed_partials` (a helper lemma you write above the spec)

Statement: `∀ (i j : Fin 3) (x : Space), ∂[i] (∂[j] f) x = ∂[j] (∂[i] f) x` for `f` with `ContDiff ℝ 2 f`.
Mixed partial derivatives commute. Translate both sides into `fderiv` (R1, R2), differentiate the inner
"derivative along a fixed vector" with the product rule (R3, R4), clean up (R5–R7), and close with Schwarz
(R8–R10).

### Partial derivatives → `fderiv`

**R1 · `rw [deriv_eq_fderiv_fun μ g]`** changes the **goal**. The lemma `Space.deriv_eq_fderiv_fun` is
`∂[μ] g = fun x => fderiv ℝ (fun x => g x) x (basis μ)`: an equation between **functions**, so it rewrites
the inner `∂[μ] g`, which is not applied to a point. Giving `μ g` explicitly picks which occurrence.
Placeholders: `(μ ν : Fin 3) (g : Space → ℝ) (x : Space)`.

| Before | After |
|---|---|
| `⊢ P (Space.deriv ν (Space.deriv μ g) x)` | `⊢ P (Space.deriv ν (fun x => (fderiv ℝ (fun x => g x) x) (basis μ)) x)` |

**R2 · `rw [Space.deriv_eq]`** changes the **goal**. The lemma is `∂[μ] g x = fderiv ℝ g x (basis μ)`: the
**value** at `x`. Each `rw` rewrites the first applied `∂` it finds (and every identical copy).
Placeholders: `(μ : Fin 3) (g : Space → ℝ) (x : Space)`.

| Before | After |
|---|---|
| `⊢ P (Space.deriv μ g x)` | `⊢ P ((fderiv ℝ g x) (basis μ))` |

### The product rule for an application

**R3 · `rw [fderiv_clm_apply hc hu]`** changes the **goal** (or the **goal list**, without `hc hu`: then `rw`
adds `DifferentiableAt ℝ c x` and `DifferentiableAt ℝ u x` as side goals). The lemma is
`DifferentiableAt ℝ c x → DifferentiableAt ℝ u x →
fderiv ℝ (fun y => c y (u y)) x = c x ∘L fderiv ℝ u x + (fderiv ℝ c x).flip (u x)`:
the derivative of "apply a varying linear map `c y` to a varying vector `u y`".
In Part 1, `c = fderiv ℝ (fun x => f x)` and `u = fun _ => basis j` (a constant).
Placeholders: `{E F G : Type}`, three real normed spaces, `(c : E → F →L[ℝ] G) (u : E → F) (x : E)`.

| Before | After |
|---|---|
| `⊢ P (fderiv ℝ (fun y => (c y) (u y)) x)` | `⊢ P (c x ∘SL fderiv ℝ u x + (fderiv ℝ c x).flip (u x))` |

**R4 · `fun_prop`** **closes** a differentiability goal such as `DifferentiableAt ℝ (fun y => fderiv ℝ f y) x`
or `DifferentiableAt ℝ (fun _ => v) x`. It finds `hf : ContDiff ℝ 2 f` in the context by itself: $f \in C^2$
makes $Df$ a $C^1$ map, hence differentiable. Write the two arguments of R3 as `(by fun_prop) (by fun_prop)`.
Placeholders: `{E : Type}` a real normed space, `(f : E → ℝ) (hf : ContDiff ℝ 2 f) (x v : E)`.

### Cleaning up (`simp` does R5–R7 in one call)

**R5 · `simp only [fderiv_fun_const, Pi.zero_apply]`** changes the **goal**. `fderiv_fun_const` is
`fderiv ℝ (fun _ => c) = 0` (as a function of the point), and `Pi.zero_apply` evaluates that `0` at `x`.
Placeholders: `{E : Type}` a real normed space, `(v x : E)`.

| Before | After |
|---|---|
| `⊢ P (fderiv ℝ (fun x => v) x)` | `⊢ P 0` |

**R6 · `rw [ContinuousLinearMap.comp_zero]`, then `rw [zero_add]`** change the **goal**: `A ∘L 0 = 0` and
`0 + B = B`. Placeholders: `{E F : Type}` real normed spaces, `(A B : E →L[ℝ] F)`.

| Before | After `comp_zero` | After `zero_add` |
|---|---|---|
| `⊢ P (A ∘SL 0 + B)` | `⊢ P (0 + B)` | `⊢ P B` |

**R7 · `rw [ContinuousLinearMap.flip_apply]`** changes the **goal**. The lemma is `(A.flip v) w = (A w) v`.
Placeholders: `{E F G : Type}` real normed spaces, `(A : E →L[ℝ] F →L[ℝ] G) (v : F) (w : E)`.

| Before | After |
|---|---|
| `⊢ P ((A.flip v) w)` | `⊢ P ((A w) v)` |

After R1–R7 the milestone's goal is $D^2 f(x)\,e_i\,e_j = D^2 f(x)\,e_j\,e_i$; the infoview prints it as
`((fderiv ℝ (fderiv ℝ fun x => f x) x) (basis i)) (basis j) = ((fderiv ℝ (fderiv ℝ fun x => f x) x) (basis j)) (basis i)`.
That is R10's goal with `f` η-expanded, so R10 closes it as is.

### Schwarz's theorem

**R8 · `have hx : ContDiffAt ℝ 2 f x := hf.contDiffAt`** changes the **context**. `ContDiff.contDiffAt`
turns "C² everywhere" into "C² near `x`". Placeholders: `{E : Type}` a real normed space,
`(f : E → ℝ) (hf : ContDiff ℝ 2 f) (x : E)`.

| Before | After |
|---|---|
| `⊢ G` | `hx : ContDiffAt ℝ 2 f x ⊢ G` |

**R9 · `have hs := hx.isSymmSndFDerivAt (by simp)`** changes the **context**. The lemma
`ContDiffAt.isSymmSndFDerivAt` is `ContDiffAt 𝕜 n f x → minSmoothness 𝕜 2 ≤ n → IsSymmSndFDerivAt 𝕜 f x`;
over `ℝ`, `minSmoothness ℝ 2 = 2`, so `(by simp)` proves `minSmoothness ℝ 2 ≤ 2`.
Placeholders: `(f : E → ℝ) (x : E) (hx : ContDiffAt ℝ 2 f x)`.

| Before | After |
|---|---|
| `hx : ContDiffAt ℝ 2 f x ⊢ G` | `hs : IsSymmSndFDerivAt ℝ f x ⊢ G` |

**R10 · `exact hs.eq v w`** **closes** the goal. `IsSymmSndFDerivAt.eq` is
`IsSymmSndFDerivAt 𝕜 f x → ∀ v w, fderiv 𝕜 (fderiv 𝕜 f) x v w = fderiv 𝕜 (fderiv 𝕜 f) x w v`.
`hs.eq _ _` lets Lean read off `v w` from the goal. Placeholders: `(f : E → ℝ) (x v w : E)`.

| Before | After |
|---|---|
| `hs : IsSymmSndFDerivAt ℝ f x ⊢ ((fderiv ℝ (fderiv ℝ f) x) v) w = ((fderiv ℝ (fderiv ℝ f) x) w) v` | no goals |

**W3** chains R8 → R9 → R10 as one term on an arbitrary normed space `E`:
`(hg.contDiffAt.isSymmSndFDerivAt (by simp)).eq v w`.

---

## Part 2 · `curl_grad_eq_zero`

Statement: `(∇ ⨯ (∇ f)) x = 0` for `f : Space → ℝ` with `ContDiff ℝ 2 f`: the curl of the gradient of a C²
scalar field is the zero vector at every point `x`. Unfold both operators (R11, R12), compare components
(R13–R15), use the milestone once (R16) and finish (R17).

### Curl and gradient → components

**R11 · `unfold Space.curl`** changes the **goal**: `curl F x` becomes the vector with component `i` equal to
`∂[i+1] F_{i+2} - ∂[i+2] F_{i+1}`, where `fi i` is the function `y ↦ (F y).ofLp i` (component `i` of `F`).
Placeholders: `(F : Space → EuclideanSpace ℝ (Fin 3)) (x : Space)`.

| Before | After |
|---|---|
| `⊢ P (curl F x)` | `⊢ P (have fi := fun i x => (F x).ofLp i; WithLp.toLp 2 fun i => Space.deriv (i + 1) (fi (i + 2)) x - Space.deriv (i + 2) (fi (i + 1)) x)` |

**R12 · `unfold Space.grad`** changes the **goal**: `∇ f x` becomes the vector of partials. Unfold both in
one call: `unfold Space.curl Space.grad`. Placeholders: `(f : Space → ℝ) (x : Space)`.

| Before | After |
|---|---|
| `⊢ P (∇ f x)` | `⊢ P (WithLp.toLp 2 fun i => Space.deriv i f x)` |

**R13 · `ext i`** changes the **goal and the context**. It uses `PiLp.ext`: two vectors of
`EuclideanSpace ℝ (Fin 3)` are equal when every component is. Placeholders: `(v w : EuclideanSpace ℝ (Fin 3))`.

| Before | After |
|---|---|
| `⊢ v = w` | `i : Fin 3 ⊢ v.ofLp i = w.ofLp i` |

**R14 · `simp only []`** changes the **goal**: even with no lemmas, `simp only` inlines a `have … ;` and
cancels `ofLp` against `toLp`, `(WithLp.toLp 2 g).ofLp i = g i`. Placeholders: `(g : Fin 3 → ℝ) (i : Fin 3)`.

| Before | After |
|---|---|
| `⊢ P ((have k := g; WithLp.toLp 2 k).ofLp i)` | `⊢ P (g i)` |

**R15 · `PiLp.zero_apply`** changes the **goal**: component `i` of the zero vector is `0`. In the exercise,
`simp only [PiLp.zero_apply]` does R14 and R15 in one call. Placeholders: `(i : Fin 3)`.

| Before | After |
|---|---|
| `⊢ P (WithLp.ofLp 0 i)` | `⊢ P 0` |

**W1** (curl of a constant field) runs R11, R13, then `simp only [PiLp.zero_apply]` (R14 + R15), and reaches

```lean-goal
⊢ Space.deriv (i + 1) (fun x => v.ofLp (i + 2)) x - Space.deriv (i + 2) (fun x => v.ofLp (i + 1)) x = 0
```

which `simp [Space.deriv_eq]` (R2, R5) closes. In the exercise you reach the same shape with `∂[_] f` in
place of the constant `v.ofLp _`: a difference of two mixed partials, `∂[i+1] ∂[i+2] f - ∂[i+2] ∂[i+1] f`.

### Finishing

**R16 · `rw [hg]` with a `∀`-lemma** changes the **goal**. For `hg : ∀ a b, g a b = g b a`, `rw` picks `a, b`
from the **first** match, then rewrites every copy of that one instance (here: only the first term). So it
turns the first term of a difference into the second, which is exactly what you need. In the exercise,
`hg` is your milestone `mixed_partials f hf`, and `rw` matches `fun x => ∂[j] f x` against `∂[j] f`
(they are the same function, η). Placeholders: `(g : Fin 3 → Fin 3 → ℝ) (i : Fin 3)`.

| Before | After |
|---|---|
| `⊢ P (g (i + 1) (i + 2) - g (i + 2) (i + 1))` | `⊢ P (g (i + 2) (i + 1) - g (i + 2) (i + 1))` |

**R17 · `simp`** **closes** `a - a = 0` (lemma `sub_self`), also when one copy is written `fun y => g y`
and the other `g`. Placeholders: `(μ : Fin 3) (g : Space → ℝ) (x : Space)`.

| Before | After |
|---|---|
| `⊢ Space.deriv μ g x - Space.deriv μ (fun y => g y) x = 0` | no goals |

**W2** runs R16 then R17 on a symmetric table:

```lean-goal
⊢ g (i + 1) (i + 2) - g (i + 2) (i + 1) = 0
⊢ g (i + 2) (i + 1) - g (i + 2) (i + 1) = 0
```

---

## Traps

- physlib already proves this exact statement and the commuting of `∂[i]`, `∂[j]`; both lemmas are on the
  `BANNED:` line, together with the search tactics (`exact?`, `apply?`, …). Prove Schwarz for `∂[i]`
  yourself (Part 1).
- `Space.deriv_eq` (R2) only rewrites a `∂` **applied to a point**. The inner `∂[j] f` in `∂[i] (∂[j] f) x` is a
  bare function: rewrite it with `deriv_eq_fderiv_fun j f` (R1). Give `j f` explicitly, or `rw` picks the
  first `∂` it can match.
- R3's two differentiability arguments become side goals if you omit them; write `(by fun_prop)` for each
  so the main goal stays first.
- `∇ ⨯ (∇ f)` prints as `curl (∇ f)`, and `∂[μ] g` as `Space.deriv μ g`: search the infoview for those names.
- After `ext i`, `simp` (bare or `simp only [PiLp.zero_apply]`) stops at the difference of two mixed
  partials: it does not know Schwarz. That difference is where the milestone comes in (R16).
- `rw [mixed_partials f hf]` fixes `i, j` from the first match (R16), so it rewrites the first term only.
  Without `hf`, `rw [mixed_partials]` adds the side goal `ContDiff ℝ 2 f` after the main goal.
- The milestone must come **before** the spec theorem in the file, and needs `hf` (Schwarz fails without C²).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| inner `∂[j] f` (a function) → `fderiv` | `rw [deriv_eq_fderiv_fun j f]` | R1 |
| `∂[μ] g x` → `fderiv ℝ g x (basis μ)` | `rw [Space.deriv_eq]` | R2 |
| derivative of `fun y => c y (u y)` | `rw [fderiv_clm_apply (by fun_prop) (by fun_prop)]` | R3, R4 |
| differentiability side goal | `fun_prop` | R4 |
| derivative of a constant, `A ∘L 0 + B`, `A.flip v w` | `simp` | R5–R7 |
| C² everywhere → C² at `x` | `hf.contDiffAt` | R8 |
| C² at `x` → symmetric second derivative | `hx.isSymmSndFDerivAt (by simp)` | R9 |
| $D^2 f(x)\,v\,w = D^2 f(x)\,w\,v$ | `exact hs.eq _ _` | R10 |
| unfold curl and grad | `unfold Space.curl Space.grad` | R11, R12 |
| vector equation → component `i` | `ext i` | R13 |
| clean `have`, `toLp`/`ofLp`, zero component | `simp only [PiLp.zero_apply]` | R14, R15 |
| use the milestone on the first term | `rw [mixed_partials f hf]` | R16 |
| `a - a = 0` (up to η) | `simp` | R17 |
| see the state | infoview | |
