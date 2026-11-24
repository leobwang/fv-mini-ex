# H111 · Oscillator energy conservation from scratch: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `apply`, `rw`, `rw … at h`, `simp`,
`simp only`, `have`, `funext`, `ring`, anonymous functions `fun x => …`. **New here:** Mathlib's Fréchet
derivative `fderiv`, `Differentiable`, `DifferentiableAt`, `ContDiff`, continuous linear maps
`E →L[ℝ] F`, the `fun_prop` tactic, real inner products `⟪·,·⟫_ℝ`, `EuclideanSpace`; and physlib's
`Time`, the time derivative `∂ₜ`, and the classical `HarmonicOscillator` with its energies, force and
equation of motion.

**The physics, in symbols.** `S : HarmonicOscillator` carries a mass `m = S.m > 0` and a spring constant
`k = S.k > 0`. A trajectory is `x : Time → ℝ¹` (`EuclideanSpace ℝ (Fin 1)`), smooth (`ContDiff ℝ ∞ x`).
Write $\dot x = \partial_t x$, $\ddot x = \partial_t \partial_t x$ and $\langle u, w\rangle$ for the real
inner product. The energy is $E = T + U$ with $T = \tfrac12 m \langle \dot x, \dot x\rangle$ and
$U = \tfrac12 k \langle x, x\rangle$.
- Product rule: $\dot T = \tfrac12 m (\langle \dot x, \ddot x\rangle + \langle \ddot x, \dot x\rangle) = \langle \dot x, m \ddot x\rangle$,
  and likewise $\dot U = \langle \dot x, k x\rangle$ (Parts 1, 2).
- Sum: $\dot E = \langle \dot x, m\ddot x + k x\rangle$. physlib's `EquationOfMotion` (Euler–Lagrange) is
  equivalent to Newton's law $m \ddot x = F(x)$ with $F(x) = -k x$, so $\dot E = \langle \dot x, 0\rangle = 0$ (Part 3).
- Zero derivative everywhere ⇒ constant (Part 4). In Lean the derivative of $E$ at $\tau$ is a linear map
  `Time →L[ℝ] ℝ`; it is the zero map because its value at the unit time `1` is $\dot E(\tau) = 0$ and every
  `p : Time` is `p.val • 1`.

The three milestones are the three bullets; the spec theorem `energy_const` is the last step.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal.
- Placeholders are written as Lean binders. `{F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]` means
  "`F` is a real normed vector space" (a type with `+`, `-`, `0`, a norm `‖·‖` and real scalars `•`);
  `ℝ`, `Time` and `EuclideanSpace ℝ (Fin 1)` all qualify. `[InnerProductSpace ℝ E]` adds a real inner
  product `⟪·,·⟫_ℝ`; `EuclideanSpace ℝ (Fin 1)` qualifies.
- Fact-building entries (`hf.differentiableAt`, `hf.differentiable …`) are shown as `have h := …`, so the
  context gains `h` and you see its type. `hf.differentiable` is dot notation for `ContDiff.differentiable hf`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `S : HarmonicOscillator` | a structure with fields `S.m`, `S.k : ℝ` (mass, spring constant) and proofs `S.m_pos`, `S.k_pos` |
| `t : Time` | a time; a structure wrapping one real number `t.val : ℝ`. `0 : Time` is the time origin (as in `S.energy x 0`), `1 : Time` is one unit of time |
| `S.energy x t` | the energy function `S.energy x : Time → ℝ` evaluated at time `t` |
| `∀ (x_1 : Time), …` | after R26: `x_1` is just a fresh name for the bound time, because `x` is already the trajectory; `intro τ` renames it |
| `EuclideanSpace ℝ (Fin 1)` | `ℝ¹` with its inner product and norm: the position space |
| `∂ₜ f t` | physlib's time derivative `Time.deriv f t`, defined as `(fderiv ℝ f t) 1` (R5) |
| `∂ₜ (∂ₜ x) t` | the acceleration $\ddot x(t)$ |
| `fderiv ℝ f t` | the derivative of `f` at `t`, a continuous linear map `Time →L[ℝ] F` |
| `(fderiv ℝ f t) 1` | that map applied to the unit time step: the rate of change of `f` |
| `E →L[ℝ] F` | continuous `ℝ`-linear maps from `E` to `F`; `L v` applies `L` to `v` |
| `⟪u, w⟫_ℝ` | the real inner (dot) product of `u` and `w` |
| `c • v` | scalar `c : ℝ` times `v`; between two reals it is just `c * v` (R15) |
| `-S.k • y` | `(-S.k) • y`: the minus belongs to the scalar |
| `ContDiff ℝ ∞ f` | `f` is smooth (`C^∞`). `∞` comes from `open ContDiff` |
| `Differentiable ℝ f` / `DifferentiableAt ℝ f t` | differentiable everywhere / at the point `t` |
| `S.kineticEnergy x` | the function `t ↦ 1 / 2 * S.m * ⟪∂ₜ x t, ∂ₜ x t⟫_ℝ` (R4) |
| `S.potentialEnergy y` | `(1 / 2) • S.k • ⟪y, y⟫_ℝ` for a position `y` (R14) |
| `S.energy x` | `fun t => S.kineticEnergy x t + S.potentialEnergy (x t)` (R19) |
| `S.force y` | `-∇U(y)`, equal to `-S.k • y` (R23) |
| `S.EquationOfMotion x` | physlib's Euler–Lagrange equation; equivalent to Newton's law (R17) |
| `0 t` | the zero function `Time → ℝ` applied to `t` (R24) |
| `0 p` | the zero linear map applied to `p` (R30) |
| `p.val • 1` | the time `p` written as a multiple of the unit time (R28) |

---

## Part 1 · `kinetic_deriv` (milestone)

Statement: `∂ₜ (S.kineticEnergy x) = fun t => ⟪∂ₜ x t, S.m • ∂ₜ (∂ₜ x) t⟫_ℝ`, i.e.
$\dot T = \langle \dot x, m \ddot x\rangle$.

### Pointwise, and the facts you need first

**R1 · `funext t`** changes the **goal and the context**: an equation of functions becomes an equation of
values at a new `t : Time`. Placeholders: `{β : Type} (F G : Time → β)`.

| Before | After |
|---|---|
| `⊢ F = fun t => G t` | `t : Time ⊢ F t = G t` |

**R2 · `Time.deriv_differentiable_of_contDiff f hf`** changes the **context**. Lemma:
`ContDiff ℝ ∞ f → Differentiable ℝ (∂ₜ f)`: the velocity of a smooth path is differentiable. Placeholders:
`{F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Time → F) (hf : ContDiff ℝ ∞ f)`.

| Before | After `have h := Time.deriv_differentiable_of_contDiff f hf` |
|---|---|
| `hf : ContDiff ℝ ∞ f ⊢ Differentiable ℝ (∂ₜ f)` | `h : Differentiable ℝ (∂ₜ f) ⊢ Differentiable ℝ (∂ₜ f)` |

**R3 · `hf.differentiableAt`** changes the **context**. Lemma `Differentiable.differentiableAt`:
`Differentiable ℝ f → DifferentiableAt ℝ f t`. The point `t` is implicit, so write the type:
`have h : DifferentiableAt ℝ f t := hf.differentiableAt`. Placeholders: `(f : Time → F) (t : Time)`.

| Before | After |
|---|---|
| `hf : Differentiable ℝ f ⊢ DifferentiableAt ℝ f t` | `h : DifferentiableAt ℝ f t ⊢ DifferentiableAt ℝ f t` |

### Unfolding and differentiating

**R4 · `rw [kineticEnergy_eq]`** changes the **goal**: the name becomes its formula. Placeholders:
`(S : HarmonicOscillator) (y : Time → EuclideanSpace ℝ (Fin 1))`.

| Before | After |
|---|---|
| `⊢ P (S.kineticEnergy y)` | `⊢ P fun t => 1 / 2 * S.m * ⟪∂ₜ y t, ∂ₜ y t⟫_ℝ` |

**R5 · `rw [Time.deriv_eq]`** changes the **goal**: `∂ₜ f t` becomes the derivative map applied to `1`.
Lemma: `∂ₜ f t = (fderiv ℝ f t) 1`. `rw [← Time.deriv_eq]` folds it back. Placeholders:
`{F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Time → F) (t : Time)`.

| Before | After |
|---|---|
| `⊢ P (∂ₜ f t)` | `⊢ P ((fderiv ℝ f t) 1)` |

**R6 · `fun_prop`** **closes** a `Differentiable`/`DifferentiableAt` goal for a function built from `+`, `*`,
`•`, `⟪·,·⟫_ℝ`, constants and hypotheses in the context. It also uses every lemma tagged `@[fun_prop]`;
physlib tags R2, R18 and `energy_differentiable`, so `hx : ContDiff ℝ ∞ x` in the context is enough for
`Differentiable ℝ (S.energy x)`. Placeholders: `{E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
(f : Time → E) (hf : Differentiable ℝ f) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ DifferentiableAt ℝ (fun τ => c * ⟪f τ, f τ⟫_ℝ) t` | ∅ |

**R7 · `rw [fderiv_const_mul ha]`** changes the **goal**: a constant factor comes out of `fderiv`. Lemma:
`DifferentiableAt ℝ a x → fderiv ℝ (fun y => b * a y) x = b • fderiv ℝ a x`. Pass `ha` as `(by fun_prop)`.
`*` groups to the left, so in `1 / 2 * S.m * ⟪…⟫` the constant is `b = 1 / 2 * S.m`. Placeholders:
`{E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : E → ℝ) (b : ℝ) (x : E)`.

| Before | After |
|---|---|
| `⊢ P (fderiv ℝ (fun y => b * a y) x)` | `⊢ P (b • fderiv ℝ a x)` |

**R8 · `rw [_root_.smul_apply]`** changes the **goal**: a scaled linear map applied to `v`. Lemma:
`(c • L) v = c • L v`. The `_root_.` is needed because `open Time` makes `smul_apply` mean another lemma.
Placeholders: `(L : E →L[ℝ] F) (c : ℝ) (v : E)`.

| Before | After |
|---|---|
| `⊢ P ((c • L) v)` | `⊢ P (c • L v)` |

**R9 · `rw [fderiv_inner_apply ℝ hf hg]`** changes the **goal**: the product rule for the inner product,
`fderiv ℝ (fun y => ⟪f y, g y⟫_ℝ) x v = ⟪f x, fderiv ℝ g x v⟫_ℝ + ⟪fderiv ℝ f x v, g x⟫_ℝ`. The field `ℝ`
is explicit; `hf hg : DifferentiableAt ℝ _ x`. For `T` both functions are `∂ₜ x` (use R2, R3); for `U`
both are `x` (use R13, R3). Placeholders: `{E G : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
[NormedAddCommGroup G] [NormedSpace ℝ G] (f g : G → E) (x v : G)`.

| Before | After |
|---|---|
| `⊢ P ((fderiv ℝ (fun y => ⟪f y, g y⟫_ℝ) x) v)` | `⊢ P (⟪f x, (fderiv ℝ g x) v⟫_ℝ + ⟪(fderiv ℝ f x) v, g x⟫_ℝ)` |

After R9, `rw [← Time.deriv_eq]` (R5 backwards) turns `(fderiv ℝ (∂ₜ x) t) 1` into `∂ₜ (∂ₜ x) t`; `rw`
rewrites every copy of that term at once.

### Collecting the two inner products

**R10 · `rw [inner_smul_right]`** changes the **goal**. Lemma: `⟪u, r • w⟫_ℝ = r * ⟪u, w⟫_ℝ`. Use it on the
right side, `⟪∂ₜ x t, S.m • ∂ₜ (∂ₜ x) t⟫_ℝ`. Placeholders: `(u w : E) (r : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ⟪u, r • w⟫_ℝ` | `⊢ P (r * ⟪u, w⟫_ℝ)` |

**R11 · `rw [real_inner_comm u]`** changes the **goal**. Lemma: `real_inner_comm u w : ⟪w, u⟫_ℝ = ⟪u, w⟫_ℝ`.
Giving `u` makes it swap only inner products whose **second** slot is `u`, so the product-rule pair
`⟪v, a⟫ + ⟪a, v⟫` becomes two copies of `⟪v, a⟫`. Placeholders: `(u w : E)`.

| Before | After |
|---|---|
| `⊢ P ⟪w, u⟫_ℝ` | `⊢ P ⟪u, w⟫_ℝ` |

**R12 · `ring`** **closes** an identity of real numbers. It treats each inner product as an unknown and reads
`•` between two reals as `*`.

| Before | After |
|---|---|
| `⊢ (1 / 2 * m) • (⟪u, w⟫_ℝ + ⟪u, w⟫_ℝ) = m * ⟪u, w⟫_ℝ` | ∅ |

---

## Part 2 · `potential_deriv` (milestone)

Statement: `∂ₜ (fun t => S.potentialEnergy (x t)) = fun t => ⟪∂ₜ x t, S.k • x t⟫_ℝ`, i.e.
$\dot U = \langle \dot x, k x\rangle$. Same route as Part 1 (R1, R5, R7, R8, R9, R5 backwards, R10, R11,
R12) after two preparations: a differentiability fact for `x` itself, and rewriting `potentialEnergy`,
which physlib writes with `•`, into the `b * a y` shape that R7 needs.

**R13 · `hf.differentiable (by simp)`** changes the **context**. Lemma `ContDiff.differentiable`:
`ContDiff ℝ n f → n ≠ 0 → Differentiable ℝ f`; `by simp` proves `∞ ≠ 0`. Follow it with R3 to get
`DifferentiableAt ℝ x t`. Placeholders: `(f : Time → F) (hf : ContDiff ℝ ∞ f)`.

| Before | After `have h := hf.differentiable (by simp)` |
|---|---|
| `hf : ContDiff ℝ ∞ f ⊢ Differentiable ℝ f` | `h : Differentiable ℝ f ⊢ Differentiable ℝ f` |

**R14 · `simp only [potentialEnergy_eq]`** changes the **goal**: `S.potentialEnergy y` becomes its formula.
In the exercise the argument is `x t` with `t` bound by `fun t => …`; `rw` cannot rewrite there, `simp only`
can. Placeholders: `(S : HarmonicOscillator) (y : EuclideanSpace ℝ (Fin 1))`.

| Before | After |
|---|---|
| `⊢ P (S.potentialEnergy y)` | `⊢ P ((1 / 2) • S.k • ⟪y, y⟫_ℝ)` |

**R15 · `smul_eq_mul`** changes the **goal**: `a • b = a * b` for two reals. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a • b)` | `⊢ P (a * b)` |

**R16 · `← mul_assoc`** changes the **goal**. Lemma: `mul_assoc : a * b * c = a * (b * c)`; right to left it
regroups `1 / 2 * (S.k * ⟪…⟫)` into `1 / 2 * S.k * ⟪…⟫`, so R7 takes `b = 1 / 2 * S.k` in one step.
Placeholders: `(a b c : ℝ)`. In the exercise all three go in one call:
`simp only [potentialEnergy_eq, smul_eq_mul, ← mul_assoc]`.

| Before | After |
|---|---|
| `⊢ P (a * (b * c))` | `⊢ P (a * b * c)` |

### Worked combination (W2, not the exercise's function)

**W2.** `∂ₜ (fun τ => 3 * ⟪f τ, f τ⟫_ℝ) t = 6 * ⟪f t, ∂ₜ f t⟫_ℝ`. R5, R7 with `(by fun_prop)`, R8, R9,
R5 backwards, R11 with `f t`, then R12:

```lean-goal
⊢ (fderiv ℝ (fun τ => 3 * ⟪f τ, f τ⟫_ℝ) t) 1 = 6 * ⟪f t, ∂ₜ f t⟫_ℝ
⊢ (3 • fderiv ℝ (fun τ => ⟪f τ, f τ⟫_ℝ) t) 1 = 6 * ⟪f t, ∂ₜ f t⟫_ℝ
⊢ 3 • (fderiv ℝ (fun τ => ⟪f τ, f τ⟫_ℝ) t) 1 = 6 * ⟪f t, ∂ₜ f t⟫_ℝ
⊢ 3 • (⟪f t, (fderiv ℝ f t) 1⟫_ℝ + ⟪(fderiv ℝ f t) 1, f t⟫_ℝ) = 6 * ⟪f t, ∂ₜ f t⟫_ℝ
⊢ 3 • (⟪f t, ∂ₜ f t⟫_ℝ + ⟪∂ₜ f t, f t⟫_ℝ) = 6 * ⟪f t, ∂ₜ f t⟫_ℝ
⊢ 3 • (⟪f t, ∂ₜ f t⟫_ℝ + ⟪f t, ∂ₜ f t⟫_ℝ) = 6 * ⟪f t, ∂ₜ f t⟫_ℝ
```

**W1** in `guide.lean` is the bare product rule in `∂ₜ` form (R5, R9, R5 backwards twice).

---

## Part 3 · `energy_deriv_zero` (milestone)

Statement: from `h : S.EquationOfMotion x`, `∂ₜ (S.energy x) = 0`. Turn `h` into Newton's law, split
`∂ₜ E = ∂ₜ T + ∂ₜ U`, substitute Parts 1 and 2, merge the inner products, and use `m ẍ = -k x`.

**R17 · `rw [equationOfMotion_iff_newtons_2nd_law S y hy] at h`** changes the **context**: `h` becomes
Newton's second law. Lemma: `ContDiff ℝ ∞ y → (S.EquationOfMotion y ↔ ∀ t, S.m • ∂ₜ (∂ₜ y) t = S.force (y t))`.
`rw` with an `↔` replaces one proposition by the other. Placeholders:
`(S : HarmonicOscillator) (y : Time → EuclideanSpace ℝ (Fin 1)) (hy : ContDiff ℝ ∞ y)`.

| Before | After |
|---|---|
| `h : S.EquationOfMotion y ⊢ ∀ (t : Time), S.m • ∂ₜ (∂ₜ y) t = S.force (y t)` | `h : ∀ (t : Time), S.m • ∂ₜ (∂ₜ y) t = S.force (y t)` and `⊢ ∀ (t : Time), S.m • ∂ₜ (∂ₜ y) t = S.force (y t)` |

**R18 · `S.potentialEnergy_differentiable y hy t`** changes the **context**. Lemma:
`ContDiff ℝ ∞ y → Differentiable ℝ (fun t => S.potentialEnergy (y t))`; applied to `t` it is the
`DifferentiableAt` fact R20 needs for `U`. (For `T`, `(by fun_prop)` works.)

| Before | After `have h := S.potentialEnergy_differentiable y hy t` |
|---|---|
| `hy : ContDiff ℝ ∞ y ⊢ DifferentiableAt ℝ (fun t => S.potentialEnergy (y t)) t` | `h : DifferentiableAt ℝ (fun t => S.potentialEnergy (y t)) t ⊢ DifferentiableAt ℝ (fun t => S.potentialEnergy (y t)) t` |

**R19 · `rw [energy_eq]`** changes the **goal**: `S.energy y` becomes `T + U` pointwise.

| Before | After |
|---|---|
| `⊢ P (S.energy y)` | `⊢ P fun t => S.kineticEnergy y t + S.potentialEnergy (y t)` |

**R20 · `rw [fderiv_fun_add hf hg]`** changes the **goal**: the derivative of a sum. Lemma:
`DifferentiableAt ℝ f x → DifferentiableAt ℝ g x → fderiv ℝ (fun y => f y + g y) x = fderiv ℝ f x + fderiv ℝ g x`.
Placeholders: `{E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
(f g : E → F) (x : E)`. Note that `fun t => S.kineticEnergy y t` prints back as `S.kineticEnergy y`.

| Before | After |
|---|---|
| `⊢ P (fderiv ℝ (fun y => f y + g y) x)` | `⊢ P (fderiv ℝ f x + fderiv ℝ g x)` |

**R21 · `rw [_root_.add_apply]`** changes the **goal**: a sum of linear maps applied to `v`. Lemma:
`(L + M) v = L v + M v`. `_root_.` for the same reason as R8. Placeholders: `(L M : E →L[ℝ] F) (v : E)`.

| Before | After |
|---|---|
| `⊢ P ((L + M) v)` | `⊢ P (L v + M v)` |

Then `rw [← Time.deriv_eq, ← Time.deriv_eq]` (one per summand; each rewrites one pattern), and
`rw [kinetic_deriv S x hx, potential_deriv S x hx]`. This leaves `(fun t => …) t` terms; the next `rw` still
finds its pattern inside them.

**R22 · `rw [← inner_add_right]`** changes the **goal**. Lemma: `⟪u, w + z⟫_ℝ = ⟪u, w⟫_ℝ + ⟪u, z⟫_ℝ`; right to
left it merges two inner products with the same left slot. Placeholders: `(u w z : E)`.

| Before | After |
|---|---|
| `⊢ P (⟪u, w⟫_ℝ + ⟪u, z⟫_ℝ)` | `⊢ P ⟪u, w + z⟫_ℝ` |

Then `rw [h t]` replaces `S.m • ∂ₜ (∂ₜ x) t` by `S.force (x t)` (Newton, from R17).

**R23 · `rw [force_eq_linear]`** changes the **goal**: Hooke's law. Lemma: `S.force y = -S.k • y`.
Placeholders: `(y : EuclideanSpace ℝ (Fin 1))`.

| Before | After |
|---|---|
| `⊢ P (S.force y)` | `⊢ P (-S.k • y)` |

**R24 · `Pi.zero_apply`** changes the **goal**: `(0 : Time → β) t = 0`. After `funext t`, the right side of
`∂ₜ E = 0` is `0 t`, the zero function applied. `simp` uses this by itself. Placeholders:
`{β : Type} [Zero β] (t : Time)`.

| Before | After |
|---|---|
| `⊢ P (0 t)` | `⊢ P 0` |

**R25 · `simp`** **closes** `⟪u, -c • w + c • w⟫_ℝ = 0`. It uses `neg_smul` (`-c • w = -(c • w)`),
`neg_add_cancel` (`-a + a = 0`) and `inner_zero_right` (`⟪u, 0⟫_ℝ = 0`); with R24 it closes the
`= 0 t` form too. Placeholders: `(u w : E) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ ⟪u, -c • w + c • w⟫_ℝ = 0` | ∅ |

---

## Part 4 · `energy_const`

Statement: `S.energy x t = S.energy x 0` for a smooth solution `x` of the equation of motion: the energy at
any time equals the energy at time `0`.

**R26 · `apply is_const_of_fderiv_eq_zero (𝕜 := ℝ) hf`** changes the **goal**. Lemma:
`Differentiable 𝕜 f → (∀ z, fderiv 𝕜 f z = 0) → ∀ x y, f x = f y`. `𝕜` is the scalar field; it does not
appear in the goal, so name it with `(𝕜 := ℝ)`. Pass `hf` as `(by fun_prop)` (R6). Placeholders:
`{E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (hf : Differentiable ℝ f) (x y : E)`.

| Before | After |
|---|---|
| `⊢ f x = f y` | `⊢ ∀ (x : E), fderiv ℝ f x = 0` |

After `intro τ` the goal is an equation of linear maps `fderiv ℝ (S.energy x) τ = 0`.

**R27 · `ext p`** changes the **goal and the context** (lemma `ContinuousLinearMap.ext`): two linear maps
are equal when they agree at every `p`. Placeholders: `(L : Time →L[ℝ] F)`.

| Before | After |
|---|---|
| `⊢ L = 0` | `p : Time ⊢ L p = 0 p` |

**R28 · `rw [p.eq_one_smul]`** changes the **goal**. Lemma `Time.eq_one_smul : p = p.val • 1`. It replaces
**every** `p` in the goal, both sides. Placeholders: `(L : Time →L[ℝ] F) (p : Time)`.

| Before | After |
|---|---|
| `⊢ P (L p)` | `⊢ P (L (p.val • 1))` |

**R29 · `rw [map_smul]`** changes the **goal**: linearity, `L (c • v) = c • L v`. `rw` fixes `L` at the first match
(the left side), so the `0 (p.val • 1)` on the right stays for `simp`. Placeholders: `(L : Time →L[ℝ] F)
(c : ℝ) (v : Time)`.

| Before | After |
|---|---|
| `⊢ P (L (c • v))` | `⊢ P (c • L v)` |

Then `rw [← Time.deriv_eq]` (R5 backwards) turns `(fderiv ℝ (S.energy x) τ) 1` into `∂ₜ (S.energy x) τ`,
and `rw [energy_deriv_zero S x hx h]` (Part 3) makes it `0 τ`.

**R30 · `zero_apply`** changes the **goal**: the zero linear map applied to `v` is `0`. Placeholders:
`(v : Time)`, the map `(0 : Time →L[ℝ] F)`.

| Before | After |
|---|---|
| `⊢ P (0 v)` | `⊢ P 0` |

**R31 · `smul_zero`** changes the **goal**: `c • 0 = 0`. Placeholders: `(c : ℝ)`, `0 : F`.

| Before | After |
|---|---|
| `⊢ P (c • 0)` | `⊢ P 0` |

`simp` applies R24, R30, R31 by itself and closes the last goal.

### Worked combination (W3, not the exercise's map)

**W3: a linear map `L : Time →L[ℝ] ℝ` with `L 1 = 0` is zero.** R27, R28, R29, then `rw [h1]` and `simp`:

```lean-goal
⊢ L = 0
⊢ L p = 0 p
⊢ L (p.val • 1) = 0 (p.val • 1)
⊢ p.val • L 1 = 0 (p.val • 1)
⊢ p.val • 0 = 0 (p.val • 1)
```

---

## Traps

- `rw` cannot rewrite under `fun t => …` when the match mentions `t`: `rw [potentialEnergy_eq]` fails inside
  `∂ₜ (fun t => S.potentialEnergy (x t))`. Use `simp only` (R14).
- `potentialEnergy` is written with `•`, `kineticEnergy` with `*`. R7 matches only `fun y => b * a y`, so
  turn `•` into `*` and regroup first (R15, R16).
- `open Time` hides the general `smul_apply` and `add_apply`: write `_root_.smul_apply`, `_root_.add_apply`
  (R8, R21).
- `R9` needs a `DifferentiableAt` proof for each slot at the point `t`: `∂ₜ x` for the kinetic energy (R2, R3),
  `x` for the potential energy (R13, R3). Write the type in the `have`, or `hf.differentiableAt` cannot
  guess the point.
- `real_inner_comm u w : ⟪w, u⟫_ℝ = ⟪u, w⟫_ℝ`: the argument you give is the one that ends up **first**.
- After `funext t` the goal of Part 3 ends in `= 0 t`, not `= 0` (R24).
- `apply is_const_of_fderiv_eq_zero` without `(𝕜 := ℝ)` leaves the field unknown and fails.
- physlib's own energy-derivative and conservation lemmas are `BANNED`; the point is to derive them. You do
  not need `S.m_pos` or `S.k_pos`.
- A `have` belongs to one proof: each milestone proves its own `hd`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| function equation → pointwise | `funext t` | R1 |
| `DifferentiableAt` of `∂ₜ x` / of `x` at `t` | `(Time.deriv_differentiable_of_contDiff x hx).differentiableAt` / `(hx.differentiable (by simp)).differentiableAt` | R2, R13, R3 |
| differentiability side goal | `by fun_prop` | R6 |
| unfold the energies | `rw [kineticEnergy_eq]`, `simp only [potentialEnergy_eq, smul_eq_mul, ← mul_assoc]`, `rw [energy_eq]` | R4, R14–R16, R19 |
| `∂ₜ f t` ↔ `fderiv ℝ f t 1` | `rw [Time.deriv_eq]` / `rw [← Time.deriv_eq]` | R5 |
| constant out of `fderiv` | `rw [fderiv_const_mul (by fun_prop), _root_.smul_apply]` | R7, R8 |
| product rule for `⟪f, g⟫_ℝ` | `rw [fderiv_inner_apply ℝ hd hd]` | R9 |
| collect inner products | `rw [inner_smul_right, real_inner_comm u]`, then `ring` | R10–R12 |
| `EquationOfMotion` → Newton | `rw [equationOfMotion_iff_newtons_2nd_law S x hx] at h` | R17 |
| derivative of `T + U` | `rw [fderiv_fun_add (by fun_prop) hd, _root_.add_apply]` | R18, R20, R21 |
| merge, Newton, Hooke | `rw [← inner_add_right, h t, force_eq_linear]`, then `simp` | R22–R25 |
| zero derivative ⇒ constant | `apply is_const_of_fderiv_eq_zero (𝕜 := ℝ) (by fun_prop)` | R26 |
| linear map on `Time` → its value at `1` | `ext p; rw [p.eq_one_smul, map_smul, ← Time.deriv_eq]` | R27–R29 |
| finish `c • 0 τ = 0 (c • 1)` | `simp` | R24, R30, R31 |
| see the state | infoview | |
