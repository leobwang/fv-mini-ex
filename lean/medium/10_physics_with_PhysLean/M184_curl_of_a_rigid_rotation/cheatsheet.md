# M184 · Curl of a rigid rotation: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's 3D space `Space`, its partial
derivatives `∂[μ]`, its curl `∇ ⨯` and the cross product `⨯ₑ₃`; Mathlib's `EuclideanSpace ℝ (Fin 3)`
(vectors as a `WithLp` wrapper), the Fréchet derivative `fderiv` and its linearity lemmas, continuous
linear maps `→L[ℝ]`, vector literals `![a, b, c]`, and the closers `fun_prop` and `ring`.

The physics: a body rotating rigidly with angular velocity `ω ∈ ℝ³` has velocity `v(y) = ω × y` at the
point `y`. Its components are `v₀ = ω₁y₂ − ω₂y₁`, `v₁ = ω₂y₀ − ω₀y₂`, `v₂ = ω₀y₁ − ω₁y₀`. The curl is
`(∇ × v)ᵢ = ∂ᵢ₊₁ vᵢ₊₂ − ∂ᵢ₊₂ vᵢ₊₁` (indices mod 3), and `∂ⱼ yₖ = δⱼₖ` (the Kronecker delta: `1` if `j = k`,
else `0`). So `(∇ × v)₀ = ∂₁(ω₀y₁ − ω₁y₀) − ∂₂(ω₂y₀ − ω₀y₂) = ω₀ + ω₀ = 2ω₀`, and likewise for `i = 1, 2`.
The vorticity of a rigid rotation is `2ω`, at every point. Every component of `v` has the shape
`a · yₖ − b · yₗ` with constants `a, b`; the proof differentiates that shape once (the milestone) and
lets `simp` do the rest.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[CommRing R]` is a
  requirement on the type (a *type class*). Here every placeholder has a concrete type (`ℝ`, `Space`,
  `Fin 3`, …), so no bracket is needed.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Space` | physlib's 3D space, `Space 3`: a structure with one field `val : Fin 3 → ℝ`, the coordinates of a point |
| `p.val 3 i` | coordinate `i` of the point `p : Space`. You write `p.val i`; Lean also prints the dimension `3` |
| `EuclideanSpace ℝ (Fin 3)` | ℝ³ with the Euclidean norm. Technically `WithLp 2 (Fin 3 → ℝ)`: a wrapper around plain functions `Fin 3 → ℝ` |
| `v.ofLp i` | component `i` of `v : EuclideanSpace ℝ (Fin 3)` (unwrap, then apply to `i`) |
| `WithLp.toLp 2 f`, `WithLp.equiv 2 (Fin 3 → ℝ)` | wrap `f : Fin 3 → ℝ` into a vector; `equiv` unwraps and `equiv.symm` wraps (R14) |
| `WithLp.ofLp 0 i` | component `i` of the zero vector |
| `basis`, `basis μ` | the standard orthonormal basis of `Space`; `basis μ` is the unit vector `e_μ` |
| `basis.repr y` | the coordinates of the point `y` as a vector in `EuclideanSpace ℝ (Fin 3)`; `(basis.repr y).ofLp i = y.val i` (R17) |
| `Space.deriv μ f x` | the partial derivative `∂f/∂y_μ` at `x`. You write `∂[μ] f x`; Lean prints `Space.deriv μ f x` |
| `fderiv ℝ f x` | the Fréchet derivative of `f` at `x`: the best linear approximation, a map `Space →L[ℝ] ℝ` |
| `(fderiv ℝ f x) v` | the directional derivative of `f` at `x` along `v`; along `basis μ` it is `∂[μ] f x` (R1) |
| `E →L[ℝ] F` | continuous ℝ-linear maps from `E` to `F`; they add and scale pointwise (R5, R6) |
| `DifferentiableAt ℝ f x` | `f` is (Fréchet) differentiable at `x`; side condition of R2, R4, closed by `fun_prop` (R3) |
| `curl F` | `∇ ⨯ F`, the curl of the vector field `F : Space → EuclideanSpace ℝ (Fin 3)` (R12) |
| `crossProduct a b` | the cross product `a ⨯₃ b` of plain vectors `a b : Fin 3 → ℝ` (R15) |
| `fun a b => (WithLp.equiv …).symm (…)` | what the notation `a ⨯ₑ₃ b` (cross product on `EuclideanSpace`) unfolds to (R14) |
| `![a, b, c]` | the vector literal `Fin 3 → α` with entries `a, b, c` (R16) |
| `i + 1`, `2 + 2` (in `Fin 3`) | addition mod 3: `2 + 2 = 1` (R13) |
| `if ν = μ then 1 else 0` | the Kronecker delta `δ_νμ` (R9) |
| `c • v` | scalar `c` times the vector (or linear map) `v`; `2 • ω` is `(2 : ℝ) • ω` |
| `(fun i => i) ⟨0, ⋯⟩` | the index `0`, printed this way after `fin_cases` |
| `case «0»` | the goal for component 0 |

---

## Part 1 · `curl_rotation`

Statement: `(∇ ⨯ (fun y : Space => ω ⨯ₑ₃ basis.repr y)) x = (2 : ℝ) • ω`, an equation between two vectors of
`EuclideanSpace ℝ (Fin 3)`. The proof has two steps:

1. **Milestone** (a helper theorem you write above `curl_rotation`): the partial derivative of a function
   `y ↦ a · yₖ − b · yₗ`,
   `∂[j] (fun y : Space => a * y.val k - b * y.val l) x = a * (if j = k then 1 else 0) - b * (if j = l then 1 else 0)`.
   `simp` cannot do this itself: differentiating a difference or a product needs differentiability side
   conditions (W2 shows where `simp` stops). Proof: R1, R2 (R3), R4 (R3) twice, R5, R6, R7, R8, R9.
2. **Main proof:** split into components (R10, R11), then one `simp` call with the definitions and the
   milestone evaluates each component (R12–R19), and `ring` (R20) closes what is left.

### Step 1 · The milestone: from `∂[μ]` to `fderiv`, linearity, and back

**R1 · `rw [Space.deriv_eq]`** changes the **goal**. The lemma is
`Space.deriv_eq : ∂[μ] f x = fderiv ℝ f x (basis μ)`: a partial derivative is the Fréchet derivative applied
to a basis vector. Rewrite with it so that Mathlib's `fderiv` lemmas apply. Placeholders:
`(μ : Fin 3) (f : Space → ℝ) (x : Space)`.

| Before | After |
|---|---|
| `⊢ P (Space.deriv μ f x)` | `⊢ P ((fderiv ℝ f x) (basis μ))` |

**R2 · `rw [fderiv_fun_sub hf hg]`** changes the **goal**. The lemma is
`fderiv_fun_sub : DifferentiableAt ℝ f x → DifferentiableAt ℝ g x → fderiv ℝ (fun y => f y - g y) x = fderiv ℝ f x - fderiv ℝ g x`.
Without the two arguments, `rw [fderiv_fun_sub]` changes the **goal list**: it adds the two side goals.
Write `rw [fderiv_fun_sub (by fun_prop) (by fun_prop)]` to close them on the spot. Placeholders:
`(f g : Space → ℝ) (x : Space)`, `P : (Space →L[ℝ] ℝ) → Prop`.

| Before | After `rw [fderiv_fun_sub]` |
|---|---|
| `⊢ P (fderiv ℝ (fun y => f y - g y) x)` | `⊢ P (fderiv ℝ f x - fderiv ℝ g x)`, `⊢ DifferentiableAt ℝ f x`, `⊢ DifferentiableAt ℝ g x` |

**R3 · `fun_prop`** **closes** a goal `DifferentiableAt ℝ f x` when `f` is built from coordinates
`y.val k`, constants, `+`, `-`, `*`. Example: `DifferentiableAt ℝ (fun y : Space => c * y.val k - y.val l) x`.
It is the argument `(by fun_prop)` of R2 and R4.

**R4 · `rw [fderiv_const_mul ha]`** changes the **goal**. The lemma is
`fderiv_const_mul : DifferentiableAt ℝ a x → ∀ b, fderiv ℝ (fun y => b * a y) x = b • fderiv ℝ a x`: a
constant factor **on the left** comes out of the derivative as a scalar multiple (`fderiv_mul_const` is the
mirror for `a y * b`). Write `rw [fderiv_const_mul (by fun_prop)]`; it rewrites the first match only, so the
milestone needs it twice. Placeholders: `(b : ℝ) (a : Space → ℝ) (x : Space)`.

| Before | After |
|---|---|
| `⊢ P (fderiv ℝ (fun y => b * a y) x)` | `⊢ P (b • fderiv ℝ a x)` |

**R5 · `_root_.sub_apply`** changes the **goal**: a difference of linear maps, applied to a vector, is the
difference of the values, `(L₁ - L₂) v = L₁ v - L₂ v`. Under `open Space Matrix`, plain `sub_apply` means
`Space.sub_apply` (for points of space), so write `_root_.sub_apply`. Placeholders:
`(L₁ L₂ : Space →L[ℝ] ℝ) (v : Space)`.

| Before | After |
|---|---|
| `⊢ P ((L₁ - L₂) v)` | `⊢ P (L₁ v - L₂ v)` |

**R6 · `_root_.smul_apply`** changes the **goal**: `(c • L) v = c • L v`. Plain `smul_apply` is ambiguous
(`Space.smul_apply`, `Matrix.smul_apply`); write `_root_.smul_apply`. Placeholders:
`(L : Space →L[ℝ] ℝ) (c : ℝ) (v : Space)`.

| Before | After |
|---|---|
| `⊢ P ((c • L) v)` | `⊢ P (c • L v)` |

**R7 · `smul_eq_mul`** changes the **goal**: scalar multiplication of a number by a number is
multiplication, `c • r = c * r`. Placeholders: `(c r : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (c • r)` | `⊢ P (c * r)` |

**R8 · `rw [← Space.deriv_eq]`** changes the **goal**: R1 right to left folds `fderiv ℝ f x (basis μ)` back
into a partial derivative, so that R9 applies. Inside `simp only [...]` write `← Space.deriv_eq`.

| Before | After |
|---|---|
| `⊢ P ((fderiv ℝ f x) (basis μ))` | `⊢ P (Space.deriv μ f x)` |

**R9 · `Space.deriv_component`** changes the **goal**. The lemma is
`Space.deriv_component : ∂[ν] (fun y => y.val μ) x = if ν = μ then 1 else 0`, i.e. `∂_ν y_μ = δ_νμ`.
Placeholders: `(μ ν : Fin 3) (x : Space)`.

| Before | After |
|---|---|
| `⊢ P (Space.deriv ν (fun y => y.val 3 μ) x)` | `⊢ P (if ν = μ then 1 else 0)` |

**W1: the chain on one scaled coordinate** `∂[j] (fun y => c * y.val k) x = c * (if j = k then 1 else 0)`
(no subtraction, so no R2 or R5). R1, R4 with `(by fun_prop)`, R6, R7, R8, R9:

```lean-goal
⊢ Space.deriv j (fun y => c * y.val 3 k) x = c * if j = k then 1 else 0
⊢ (fderiv ℝ (fun y => c * y.val 3 k) x) (basis j) = c * if j = k then 1 else 0
⊢ (c • fderiv ℝ (fun y => y.val 3 k) x) (basis j) = c * if j = k then 1 else 0
⊢ c • (fderiv ℝ (fun y => y.val 3 k) x) (basis j) = c * if j = k then 1 else 0
⊢ c * (fderiv ℝ (fun y => y.val 3 k) x) (basis j) = c * if j = k then 1 else 0
⊢ c * Space.deriv j (fun y => y.val 3 k) x = c * if j = k then 1 else 0
```

The last `rw [deriv_component]` makes both sides identical, and `rw` closes the goal by `rfl`. The milestone
is the same chain with R2 first and R5 after the two R4s. `rw` rewrites only the instances of its first match,
so R6, R7, R8 and R9 are each needed once per term (twice), or all of R5–R9 together in one `simp only [...]`.

### Step 2 · The main proof: components, then one `simp`

**R10 · `ext i`** changes the **goal and the context**: two vectors of `EuclideanSpace ℝ (Fin 3)` are equal
when every component is. Placeholders: `(u v : EuclideanSpace ℝ (Fin 3))`.

| Before | After |
|---|---|
| `⊢ u = v` | `i : Fin 3 ⊢ u.ofLp i = v.ofLp i` |

**R11 · `fin_cases i`** changes the **goal list and the context**: `i` leaves the context and there is one
goal per value `0, 1, 2`. Placeholders: `(P : Fin 3 → Prop) (i : Fin 3)`. Follow it with `<;> simp […]`
so `simp` runs on all three.

| Before | After |
|---|---|
| `i : Fin 3 ⊢ P i` | `⊢ P ((fun i => i) ⟨0, ⋯⟩)`, `⊢ P ((fun i => i) ⟨1, ⋯⟩)`, `⊢ P ((fun i => i) ⟨2, ⋯⟩)` |

`simp [curl, cross_apply, basis_repr_apply, <milestone>]` then applies R12–R19 by itself (R13, R14, R16,
R18, R19 are simp lemmas already; name R12, R15, R17 and the milestone).

**R12 · `simp only [curl]`** changes the **goal**: component `i` of the curl becomes the two partial
derivatives `∂ᵢ₊₁ Fᵢ₊₂ − ∂ᵢ₊₂ Fᵢ₊₁`. The definition is
`curl F x = WithLp.toLp 2 (fun i => ∂[i + 1] (fun x => (F x).ofLp (i + 2)) x - ∂[i + 2] (fun x => (F x).ofLp (i + 1)) x)`.
Placeholders: `(F : Space → EuclideanSpace ℝ (Fin 3)) (x : Space) (i : Fin 3)`.

| Before | After |
|---|---|
| `⊢ P ((curl F x).ofLp i)` | `⊢ P (Space.deriv (i + 1) (fun x => (F x).ofLp (i + 2)) x - Space.deriv (i + 2) (fun x => (F x).ofLp (i + 1)) x)` |

**R13 · `Fin.reduceAdd`** (a `simp` procedure) changes the **goal**: it computes `+` on literal `Fin 3`
indices, mod 3. After `fin_cases`, this is how `i + 1`, `i + 2` become concrete indices.

| Before | After |
|---|---|
| `⊢ P (2 + 2)` | `⊢ P 1` |

**R14 · `WithLp.equiv_apply`, `WithLp.equiv_symm_apply`** change the **goal**: they unwrap the notation
`u ⨯ₑ₃ v`, which is a `fun a b => …` that unwraps both vectors to `Fin 3 → ℝ`, takes `crossProduct`, and
wraps the result. The lemmas are `WithLp.equiv 2 V u = u.ofLp` and `(WithLp.equiv 2 V).symm = WithLp.toLp 2`.
Placeholders: `(u v : EuclideanSpace ℝ (Fin 3))`.

| Before | After `simp only [WithLp.equiv_apply, WithLp.equiv_symm_apply]` |
|---|---|
| `⊢ P (((fun a b => (WithLp.equiv 2 (Fin 3 → ℝ)).symm ((crossProduct ((WithLp.equiv 2 (Fin 3 → ℝ)) a)) ((WithLp.equiv 2 (Fin 3 → ℝ)) b))) u v).ofLp 0)` | `⊢ P ((crossProduct u.ofLp) v.ofLp 0)` |

**R15 · `rw [cross_apply]`** changes the **goal**. The lemma is
`cross_apply : a ⨯₃ b = ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]`.
Placeholders: `{R : Type} [CommRing R] (a b : Fin 3 → R)` (`R` has `+`, `-`, commutative `*`; `ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ P ((crossProduct a) b)` | `⊢ P ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]` |

**R16 · `Matrix.cons_val_…`** (applied by `simp`) changes the **goal**: an entry of a vector literal at a
literal index is that entry. Placeholders: `{α : Type} (a b c : α)`.

| Before | After |
|---|---|
| `⊢ P (![a, b, c] 2)` | `⊢ P c` |

**R17 · `Space.basis_repr_apply`** changes the **goal**. The lemma is
`(basis.repr p).ofLp i = p.val i`: the coordinate vector of a point has the point's coordinates. This puts
every component of the field in the form `a * y.val k - b * y.val l`, which the milestone matches.
Placeholders: `(p : Space) (i : Fin 3)`.

| Before | After |
|---|---|
| `⊢ P ((basis.repr p).ofLp i)` | `⊢ P (p.val 3 i)` |

**R18 · `Fin.reduceEq`, `↓reduceIte`** (applied by `simp`) change the **goal**: an `if` whose condition
compares literal indices is decided and replaced by its branch. After the milestone fires, this turns the
Kronecker deltas into `1` and `0`. Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `⊢ P (if 1 = 0 then a else b)` | `⊢ P b` |

**R19 · `PiLp.smul_apply`, then R7** change the **goal**: a component of `c • v` is `c` times the component.
The lemma is `(c • v).ofLp i = c • v.ofLp i`. This is what happens to the right side `(2 • ω).ofLp i`.
Placeholders: `(c : ℝ) (v : EuclideanSpace ℝ (Fin 3)) (i : Fin 3)`.

| Before | After `rw [PiLp.smul_apply]` | After `rw [smul_eq_mul]` |
|---|---|---|
| `⊢ P ((c • v).ofLp i)` | `⊢ P (c • v.ofLp i)` | `⊢ P (c * v.ofLp i)` |

**R20 · `ring`** **closes** an identity of commutative rings, here the leftover `a + a = 2 * a` in each
component (`simp` turns `ωᵢ − (−ωᵢ)` into `ωᵢ + ωᵢ` but does not collect it).

**W2: where `simp` stops without a derivative lemma.** For the stretched position field `y ↦ c • y`,
`ext i; fin_cases i` then `simp [curl, basis_repr_apply]` evaluates everything except the partial
derivatives:

```lean-goal
⊢ Space.deriv 1 (fun x => c * x.val 3 2) x - Space.deriv 2 (fun x => c * x.val 3 1) x = 0
```

`simp [deriv_coord_mul]` (W1) finishes. In the exercise the milestone plays the role of W1.

**W3: one cross-product component.** `(u ⨯ₑ₃ v).ofLp 1 = u.ofLp 2 * v.ofLp 0 - u.ofLp 0 * v.ofLp 2` by R14,
R15, then `simp` (R16):

```lean-goal
⊢ (crossProduct u.ofLp) v.ofLp 1 = u.ofLp 2 * v.ofLp 0 - u.ofLp 0 * v.ofLp 2
⊢ ![u.ofLp 1 * v.ofLp 2 - u.ofLp 2 * v.ofLp 1, u.ofLp 2 * v.ofLp 0 - u.ofLp 0 * v.ofLp 2, u.ofLp 0 * v.ofLp 1 - u.ofLp 1 * v.ofLp 0] 1 = u.ofLp 2 * v.ofLp 0 - u.ofLp 0 * v.ofLp 2
```

---

## Traps

- `simp` cannot differentiate `fun y => a * y.val k - b * y.val l`: R2 and R4 need differentiability
  arguments. Prove the milestone first and pass its name to `simp` (W2).
- State the milestone with `y.val k`, not `(basis.repr y).ofLp k`: `simp` rewrites to `y.val k` first (R17),
  and a lemma whose left side is not in that form never fires.
- Under `open Space Matrix`, `sub_apply` and `smul_apply` are ambiguous or wrong (`Space.sub_apply` is about
  points). Write `_root_.sub_apply`, `_root_.smul_apply`.
- `rw [fderiv_fun_sub]` without arguments leaves two `DifferentiableAt` goals (R2); pass `(by fun_prop)`.
- `rw [fderiv_const_mul …]` rewrites the first matching product only; the milestone needs two.
- `Fin 3` arithmetic wraps: `2 + 1 = 0`, `2 + 2 = 1` (R13). The curl's `i + 1`, `i + 2` are cyclic.
- Lean prints `y.val 3 k` for the coordinate you write as `y.val k`.
- `t1 ; t2` runs `t2` on the first goal only. After `fin_cases`, use `<;>` or `all_goals`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `∂[μ] f x` → `fderiv` / back | `rw [Space.deriv_eq]` / `← Space.deriv_eq` | R1, R8 |
| derivative of `f y - g y` | `rw [fderiv_fun_sub (by fun_prop) (by fun_prop)]` | R2, R3 |
| derivative of `b * a y` | `rw [fderiv_const_mul (by fun_prop)]` | R4, R3 |
| differentiability side goal | `fun_prop` | R3 |
| apply `L₁ - L₂`, `c • L` to `v` | `simp only [_root_.sub_apply, _root_.smul_apply]` | R5, R6 |
| `c • r → c * r` (numbers) | `smul_eq_mul` | R7 |
| `∂_ν y_μ = δ_νμ` | `deriv_component` | R9 |
| vector equation → 3 components | `ext i; fin_cases i` | R10, R11 |
| unfold `∇ ⨯ F` | `simp [curl]` | R12 |
| `Fin 3` index arithmetic | `simp` (`Fin.reduceAdd`) | R13 |
| unfold `u ⨯ₑ₃ v` | `simp [cross_apply]` (`WithLp.equiv_apply`, …) | R14, R15 |
| entry of `![a, b, c]` | `simp` | R16 |
| `(basis.repr y).ofLp i → y.val i` | `basis_repr_apply` | R17 |
| decide `if 1 = 0 …` | `simp` | R18 |
| component of `c • v` | `simp` (`PiLp.smul_apply`, `smul_eq_mul`) | R19 |
| `a + a = 2 * a` | `ring` | R20 |
| see the state | infoview | |
