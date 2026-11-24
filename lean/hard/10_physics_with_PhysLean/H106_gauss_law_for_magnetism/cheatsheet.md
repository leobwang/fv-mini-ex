# H106 · Gauss's law for magnetism from the vector potential: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's `Space`, its partial derivatives
`∂[μ]`, divergence `∇ ⬝` and curl `∇ ⨯`, the electromagnetic potential and its magnetic field; Mathlib's
Fréchet derivative `fderiv`, the smoothness classes `ContDiff`/`Differentiable`, the tactic `fun_prop`, and
index arithmetic in `Fin 3`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`, or another type in place of `ℝ`). The step changes only the
  part inside `P (…)`, wherever it sits in a larger goal. `G : Prop` is an arbitrary goal that a step leaves
  alone.
- Placeholders are written as Lean binders. `{E : Type}` is any type. A bracket such as `[NormedSpace ℝ E]` is
  a requirement on `E` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

`∂[μ]` is a macro, so the infoview never shows it: you write `∂[μ] f x`, Lean prints `Space.deriv μ f x`.
The same holds for the component `F x i`, printed `(F x).ofLp i`.

| You see | It means |
|---|---|
| `Space` | physlib's 3-dimensional space of positions, `Space 3` ≅ ℝ³ |
| `Time` | physlib's type of times (a copy of ℝ) |
| `EuclideanSpace ℝ (Fin 3)` | ℝ³ with the Euclidean norm: the values of a vector field `F : Space → EuclideanSpace ℝ (Fin 3)` |
| `(F x).ofLp i` | component `i` of the vector `F x`; you type it as `F x i` (`ofLp` unwraps the vector to a function `Fin 3 → ℝ`) |
| `Space.deriv μ f x` | `∂[μ] f x`, the partial derivative ∂f/∂x_μ at the point `x` (`μ : Fin 3`) |
| `Space.deriv μ f` | the function `x ↦ ∂f/∂x_μ (x)`; `Space.deriv u (Space.deriv v f)` is ∂_u ∂_v f |
| `Space.div F x` | `(∇ ⬝ F) x = ∑ i, ∂[i] (F · i) x`, the divergence |
| `curl F x` | `(∇ ⨯ F) x`; component `i` is `∂[i+1] F_{i+2} - ∂[i+2] F_{i+1}` (indices mod 3) |
| `∑ i, f i`, `∑ x_1, …` | a sum over all of `Fin 3`; `x_1` is a bound variable Lean renamed to avoid clashing with `x` |
| `i + 1`, `i + 2` with `i : Fin 3` | addition mod 3: `1 + 2 = 0`, `2 + 2 = 1` |
| `fderiv ℝ f x` | the Fréchet derivative Df(x) of `f` at `x`: a continuous linear map |
| `Space →L[ℝ] ℝ` | the type of continuous ℝ-linear maps from `Space` to `ℝ` (where `fderiv ℝ f x` lives) |
| `(fderiv ℝ f x) v` | Df(x) applied to `v`: the directional derivative of `f` at `x` along `v` |
| `Space.basis μ` | the standard basis vector e_μ of `Space`, so `(fderiv ℝ f x) (Space.basis μ)` = ∂f/∂x_μ |
| `ContDiff ℝ n f` | `f` is Cⁿ: `n` times continuously differentiable |
| `n : ℕ∞ω`, `∞`, `2` | smoothness orders. `ℕ∞ω = WithTop ℕ∞`; `∞` (from `open ContDiff`) is C^∞; a numeral `2` is C²; `ω` (the top) would be analytic |
| `Differentiable ℝ f` | `f` is differentiable everywhere; by definition `∀ x, DifferentiableAt ℝ f x` |
| `SpeedOfLight` | a structure: a real `val` with a proof `0 < val` |
| `ElectromagneticPotential` | a structure wrapping the 4-potential A^μ, a map `SpaceTime → Lorentz.Vector` |
| `V.val 3` | the underlying map of `V` (the `3` is the spatial dimension); `ContDiff ℝ ∞ V` means it is smooth |
| `vectorPotential c V t` | the spatial part **A**(t, ·) : `Space → EuclideanSpace ℝ (Fin 3)` at time `t` |
| `magneticField c V` | **B** : `Time → Space → EuclideanSpace ℝ (Fin 3)`, defined as ∇ × **A** |

---

## Part 1 · `deriv_sub_deriv` (milestone)

Statement: for a C² field `f` and indices `u v w`, the partial `∂[u]` of the function
`x ↦ ∂[v] f_w x - ∂[w] f_v x` is `∂[u] (∂[v] f_w) - ∂[u] (∂[w] f_v)` (an equation between functions
`Space → ℝ`). The only analytic content: both first derivatives are differentiable, because `f` is C².

### Smoothness facts

**R1 · `contDiff_euclidean.mp hF i`** changes the **context**. The lemma is
`contDiff_euclidean : ContDiff ℝ n F ↔ ∀ i, ContDiff ℝ n (fun x => F x i)`: a vector field is Cⁿ iff each
component is. `.mp` is the `→` direction. Placeholders: `{E ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]`
(`E` a real normed space, such as `Space`), `[Fintype ι]` (finitely many components, such as `Fin 3`),
`{n : ℕ∞ω} (F : E → EuclideanSpace ℝ ι) (hF : ContDiff ℝ n F) (i : ι)`. Use it in a `have`.

| Before | After `have hi : … := contDiff_euclidean.mp hF i` |
|---|---|
| `⊢ G` | `hi : ContDiff ℝ n fun x => (F x).ofLp i ⊢ G` |

**R2 · `rw [Space.deriv_eq_fderiv_fun]`** changes the **goal**. The lemma is
`Space.deriv_eq_fderiv_fun : ∂[μ] f = fun x => (fderiv ℝ f x) (Space.basis μ)` (as functions). Use it on
`Differentiable ℝ (∂[μ] f)`: `fun_prop` cannot see inside `∂[μ]`, but can read `fderiv`.
Placeholders: `(f : Space → ℝ) (μ : Fin 3)`.

| Before | After |
|---|---|
| `⊢ Differentiable ℝ (Space.deriv μ f)` | `⊢ Differentiable ℝ fun x => (fderiv ℝ (fun x => f x) x) (Space.basis μ)` |

**R3 · `fun_prop`** **closes** a goal stating that a function is continuous / differentiable / Cⁿ, by
decomposing the function and using the tagged lemmas plus the hypotheses in the context. Here: a C² function
has a C¹ derivative, so `x ↦ (fderiv ℝ f x) v` is differentiable. It needs a `ContDiff` hypothesis in the
context: the component fact from R1, or the field's own `hf : ContDiff ℝ 2 f` (fun_prop also knows that the
components of a C² vector field are C²). Placeholders: `(f : Space → ℝ) (hf : ContDiff ℝ 2 f) (μ : Fin 3)`.

| Before | After |
|---|---|
| `hf : ContDiff ℝ 2 f ⊢ Differentiable ℝ fun x => (fderiv ℝ f x) (Space.basis μ)` | no goal |

### Pointwise: from `∂` to `fderiv`

**R4 · `ext x`** changes the **goal and the context**: an equation of functions becomes an equation of their
values at a new point `x` (lemma `funext`). Placeholders: `(F G : Space → ℝ)`.

| Before | After |
|---|---|
| `⊢ F = G` | `x : Space ⊢ F x = G x` |

**R5 · `Pi.sub_apply`** changes the **goal**. The lemma is `(f - g) x = f x - g x`: a difference of
functions, applied. `rw` rewrites one pattern; `simp only [Pi.sub_apply]` rewrites every such term at once.
Placeholders: `(f g : Space → ℝ) (x : Space)`.

| Before | After |
|---|---|
| `⊢ P ((f - g) x)` | `⊢ P (f x - g x)` |

**R6 · `rw [Space.deriv_eq]`** changes the **goal**. The lemma is
`Space.deriv_eq : ∂[μ] f x = (fderiv ℝ f x) (Space.basis μ)`. `rw` instantiates `μ f x` with the **first**
match and rewrites only copies of that one term; for three different `∂` terms write it three times.
Placeholders: `(f g : Space → ℝ) (μ : Fin 3) (x : Space)`; below, the `g` term is untouched.

| Before | After |
|---|---|
| `⊢ P (Space.deriv μ f x) (Space.deriv μ g x)` | `⊢ P ((fderiv ℝ f x) (Space.basis μ)) (Space.deriv μ g x)` |

**R7 · `hg x`** changes the **context**. `Differentiable ℝ g` is by definition
`∀ x, DifferentiableAt ℝ g x`, so applying `hg` to a point gives differentiability there. You usually write
`hg x` directly as an argument (R8). Placeholders: `(g : Space → ℝ) (hg : Differentiable ℝ g) (x : Space)`.

| Before | After `have hx : DifferentiableAt ℝ g x := hg x` |
|---|---|
| `⊢ G` | `hx : DifferentiableAt ℝ g x ⊢ G` |

**R8 · `rw [fderiv_fun_sub hf hg]`** changes the **goal**. The lemma is
`fderiv_fun_sub : DifferentiableAt ℝ f x → DifferentiableAt ℝ g x → fderiv ℝ (fun y => f y - g y) x = fderiv ℝ f x - fderiv ℝ g x`:
the derivative of a difference is the difference of derivatives, **at a point where both are differentiable**.
Placeholders: `(f g : Space → ℝ) (x : Space) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)`;
here `P : (Space →L[ℝ] ℝ) → Prop`.

| Before | After |
|---|---|
| `⊢ P (fderiv ℝ (fun y => f y - g y) x)` | `⊢ P (fderiv ℝ f x - fderiv ℝ g x)` |

**R9 · `rfl`** **closes** `(L₁ - L₂) v = L₁ v - L₂ v`: subtraction of maps is defined pointwise, so both
sides are the same by definition (the named lemma is `ContinuousLinearMap.sub_apply`). Placeholders:
`(L₁ L₂ : Space →L[ℝ] ℝ) (v : Space)`.

| Before | After |
|---|---|
| `⊢ (L₁ - L₂) v = L₁ v - L₂ v` | no goal |

**W1: the whole chain on a difference of two differentiable functions** `g k : Space → ℝ` (not first
derivatives, as in the exercise). R4, then R5 and R6 three times in one `rw`, then R8 with `(hg x) (hk x)`
(R7), then R9:

```lean-goal
⊢ (Space.deriv u fun x => g x - k x) = Space.deriv u g - Space.deriv u k
⊢ Space.deriv u (fun x => g x - k x) x = (Space.deriv u g - Space.deriv u k) x
⊢ (fderiv ℝ (fun x => g x - k x) x) (Space.basis u) = (fderiv ℝ g x) (Space.basis u) - (fderiv ℝ k x) (Space.basis u)
⊢ (fderiv ℝ g x - fderiv ℝ k x) (Space.basis u) = (fderiv ℝ g x) (Space.basis u) - (fderiv ℝ k x) (Space.basis u)
```

In the exercise the two functions are `∂[v] f_w` and `∂[w] f_v`, and their differentiability comes from
R1 → R2 → R3.

---

## Part 2 · `div_curl_eq_zero` (milestone)

Statement: for a C² field `f : Space → EuclideanSpace ℝ (Fin 3)`, `(∇ ⬝ (∇ ⨯ f)) x = 0`. Unfold both operators
into six second partial derivatives, split them with Part 1, and pair them off with Schwarz's theorem
(∂_u ∂_v = ∂_v ∂_u for C² functions).

### Unfolding `∇ ⬝` and `∇ ⨯`

**R10 · `simp only [Space.div]`** changes the **goal**: the divergence becomes its defining sum. Placeholders:
`(F : Space → EuclideanSpace ℝ (Fin 3)) (x : Space)`.

| Before | After |
|---|---|
| `⊢ P (Space.div F x)` | `⊢ P (∑ x_1, Space.deriv x_1 (fun x => (F x).ofLp x_1) x)` |

**R11 · `simp only [Space.curl]`** changes the **goal**: component `i` of the curl becomes
`∂[i+1] F_{i+2} - ∂[i+2] F_{i+1}`, with symbolic `Fin 3` indices. Placeholders:
`(F : Space → EuclideanSpace ℝ (Fin 3)) (x : Space) (i : Fin 3)`.

| Before | After |
|---|---|
| `⊢ P ((curl F x).ofLp i)` | `⊢ P (Space.deriv (i + 1) (fun x => (F x).ofLp (i + 2)) x - Space.deriv (i + 2) (fun x => (F x).ofLp (i + 1)) x)` |

**R12 · `Fin.sum_univ_three`** changes the **goal**. The lemma is `∑ i, f i = f 0 + f 1 + f 2`.
Placeholders: `{β : Type} [AddCommMonoid β] (f : Fin 3 → β)` (β has `+` and `0`; `ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1 + f 2)` |

**R13 · `simp only [Fin.isValue, Fin.reduceAdd, zero_add]`** changes the **goal**: numeral index arithmetic in
`Fin 3` is computed mod 3. `Fin.reduceAdd` is a *simproc* (a simp step that computes) for `a + b` of
numerals; `zero_add : 0 + a = a` catches `0 + 1`; `Fin.isValue` only normalises how numerals are stored.
Placeholders: `{β : Type} (a : Fin 3 → β)`.

| Before | After |
|---|---|
| `⊢ P (a (0 + 1)) (a (1 + 2)) (a (2 + 2))` | `⊢ P (a 1) (a 0) (a 1)` |

R10–R13 go in one `simp only [Space.div, Space.curl, Fin.sum_univ_three, Fin.isValue, Fin.reduceAdd, zero_add]`.
The result has three terms `∂[i] (fun x => ∂[i+1] f_{i+2} x - ∂[i+2] f_{i+1} x) x` for `i = 0, 1, 2`, which is
exactly the left side of Part 1 applied at `x`: `rw [deriv_sub_deriv f hf]` three times, then
`simp only [Pi.sub_apply]` (R5) to apply the differences at `x`.

**W3: R12, R13 on a cyclic sum**, then R15:

```lean-goal
⊢ ∑ i, (a (i + 1) - a i) = 0
⊢ a (0 + 1) - a 0 + (a (1 + 1) - a 1) + (a (2 + 1) - a 2) = 0
⊢ a 1 - a 0 + (a 2 - a 1) + (a 0 - a 2) = 0
```

### Schwarz and the cancellation

**R14 · `rw [Space.deriv_commute _ hf]`** changes the **goal**. The lemma is
`Space.deriv_commute : ContDiff ℝ 2 f → ∂[u] (∂[v] f) = ∂[v] (∂[u] f)` (Schwarz). `u v` are implicit, so `rw`
takes them from the **first** term `∂[?u] (∂[?v] f)` with this `f` that it meets, swaps it (and identical
copies), and leaves the already-swapped partner alone. Placeholders:
`(f : Space → ℝ) (hf : ContDiff ℝ 2 f) (u v : Fin 3) (x : Space)`. One `rw` per component `f_i`, each with its
own `hc i : ContDiff ℝ 2 (fun x => f x i)` from R1.

| Before | After |
|---|---|
| `⊢ P (Space.deriv u (Space.deriv v f) x)` | `⊢ P (Space.deriv v (Space.deriv u f) x)` |

**R15 · `ring`** **closes** an identity that holds in every commutative ring. Each `Space.deriv … x` is an
opaque real number to it, so once the six terms have matching names, `a - b + (c - a) + (b - c) = 0` is all
that is left. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ a - b + (c - a) + (b - c) = 0` | no goal |

**W2: mixed partials of a scalar field cancel.** `g : Space → ℝ`, `hg : ContDiff ℝ 2 g`; R14 swaps the
first term into the second, then R15:

```lean-goal
⊢ Space.deriv 0 (Space.deriv 1 g) x - Space.deriv 1 (Space.deriv 0 g) x = 0
⊢ Space.deriv 1 (Space.deriv 0 g) x - Space.deriv 1 (Space.deriv 0 g) x = 0
```

---

## Part 3 · `gauss_magnetic`

Statement: for a smooth electromagnetic potential `V`, the magnetic field has zero divergence,
`(∇ ⬝ V.magneticField c t) x = 0`. Rewrite **B** as ∇ × **A** (R16) and apply Part 2 to **A** at time `t`;
its C² hypothesis comes from `fun_prop` (R17).

**R16 · `rw [ThreeDimension.magneticField_eq_3D]`** changes the **goal**. The lemma is
`magneticField c V = fun t x => (∇ ⨯ vectorPotential c V t) x`. Placeholders: `(c : SpeedOfLight)
(V : ElectromagneticPotential)`, `P : (Time → Space → EuclideanSpace ℝ (Fin 3)) → Prop`. In the exercise the
result is applied to `t`, and stays as an unreduced `(fun t x => …) t`; `exact` accepts that as it is.

| Before | After |
|---|---|
| `⊢ P (magneticField c V)` | `⊢ P fun t x => curl (vectorPotential c V t) x` |

**R17 · `fun_prop`** **closes** `ContDiff ℝ n (vectorPotential c V t)` for any numeral `n` from
`hV : ContDiff ℝ ∞ V`: physlib tags `vectorPotential_contDiff_of_smooth` with `@[fun_prop]`, and `fun_prop`
then fixes the time argument. Inside a term write it as `(by fun_prop)`. Placeholders:
`(V : ElectromagneticPotential) (hV : ContDiff ℝ ∞ V) (c : SpeedOfLight) (t : Time)`; the guide uses `n = 1`,
the exercise needs `n = 2`.

| Before | After |
|---|---|
| `hV : ContDiff ℝ ∞ (V.val 3) ⊢ ContDiff ℝ 1 (vectorPotential c V t)` | no goal |

---

## Traps

- The BANNED names (`Space.div_of_curl_eq_zero`, `magneticField_div_eq_zero`, `deriv_coord_2nd_sub`,
  `deriv_coord_2nd_add`, `curl_of_curl`, `gaussLawMagnetic`) are physlib's own proofs of these facts; the
  checker rejects them anywhere outside the spec.
- You type `∂[μ] f x` and `F x i`; the infoview shows `Space.deriv μ f x` and `(F x).ofLp i`. They are the
  same terms.
- Part 1 is an equation of **functions**: `rw [Space.deriv_eq]` finds nothing until `ext x` (R4) has applied
  both sides to a point.
- `fderiv_fun_sub` wants `DifferentiableAt … x`: pass `(h1 x)`, not `h1` (R7).
- `fun_prop` uses the context: it proves smoothness only from `ContDiff` facts it finds there (`hf`, or a
  component fact from R1). It also cannot see inside `∂[μ]`: rewrite with `Space.deriv_eq_fderiv_fun` (R2)
  first, or it fails on `Differentiable ℝ (∂[v] …)`.
- `Space.deriv_commute` (R14) needs the C² fact of the **component** it swaps, `hc i`, not `hf`.
- `rw [Space.deriv_eq]` and `rw [Space.deriv_commute _ h]` rewrite only the first match (and its identical
  copies). Repeat them; a second `rw [Space.deriv_commute _ (hc i)]` with the same `i` swaps the pair back.
- `Fin 3` arithmetic wraps: `1 + 2 = 0`, `2 + 2 = 1`. Leave it to `Fin.reduceAdd` (R13) rather than reading
  indices off by hand.
- `ContDiff ℝ ∞` is smooth; `∞` needs `open ContDiff` (already in the file). The milestone takes
  `ContDiff ℝ 2`; R17 turns the first into the second.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| C² of a component | `have hc : ∀ i : Fin 3, ContDiff ℝ 2 (fun x => f x i) := fun i => contDiff_euclidean.mp hf i` | R1 |
| `Differentiable ℝ (∂[v] g)` from `ContDiff ℝ 2 g` | `rw [Space.deriv_eq_fderiv_fun]; fun_prop` | R2, R3 |
| function equation → pointwise | `ext x` | R4 |
| `(f - g) x → f x - g x` | `rw [Pi.sub_apply]` / `simp only [Pi.sub_apply]` | R5 |
| `∂[μ] f x → fderiv ℝ f x (basis μ)` | `rw [Space.deriv_eq]` (once per term) | R6 |
| `DifferentiableAt` at a point | `h x` | R7 |
| derivative of a difference | `rw [fderiv_fun_sub (h1 x) (h2 x)]` | R8 |
| `(L₁ - L₂) v = L₁ v - L₂ v` | `rfl` | R9 |
| unfold `∇ ⬝`, `∇ ⨯`, the `Fin 3` sum, the indices | `simp only [Space.div, Space.curl, Fin.sum_univ_three, Fin.isValue, Fin.reduceAdd, zero_add]` | R10–R13 |
| Schwarz | `rw [Space.deriv_commute _ (hc i)]` | R14 |
| cancel the six terms | `ring` | R15 |
| **B** = ∇ × **A** | `rw [ThreeDimension.magneticField_eq_3D]` | R16 |
| `ContDiff ℝ 2 (V.vectorPotential c t)` | `(by fun_prop)` | R17 |
| see the state | infoview | |
