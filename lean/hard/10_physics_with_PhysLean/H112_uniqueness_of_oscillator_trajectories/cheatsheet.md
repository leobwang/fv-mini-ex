# H112 · Uniqueness of oscillator trajectories: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's harmonic oscillator
(`HarmonicOscillator`, `InitialConditions`, `Time`, `∂ₜ`, the equation of motion, the energy),
Mathlib's Fréchet derivative `fderiv`, smoothness `ContDiff`, real inner products `⟪·, ·⟫_ℝ`,
and the tactics `fun_prop`, `set`, `simpa`.

**The mathematics.** Let `T = IC.trajectory S` be physlib's explicit solution and `y = x − T`.
(1) The equation of motion `m·ÿ = −k·y` is linear, so `y` solves it too (milestone 2).
(2) `y(0) = 0` and `ẏ(0) = 0`, so the energy `E(y)(t) = ½ m ⟨ẏ, ẏ⟩ + ½ k ⟨y, y⟩` is `0` at `t = 0`;
physlib's energy conservation makes it `0` at every `t`.
(3) Both terms are `≥ 0` and `k > 0`, so `⟨y t, y t⟩ = 0`, so `y t = 0` (milestone 3), so `x = T`.
Here `m` is the mass `S.m > 0`, `k` the spring constant `S.k > 0`, `ẏ = ∂ₜ y` the velocity.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- `G` with a hypothesis `k : … → G` is "whatever you were proving": the entry changes a hypothesis.
- Placeholders are Lean binders. `{E : Type}` is any type. A bracket such as `[NormedSpace ℝ E]` is a
  requirement on `E` (a *type class*). `[NormedAddCommGroup E] [NormedSpace ℝ E]`: `E` is a real
  normed vector space; `[InnerProductSpace ℝ E]` adds a real inner product. `ℝ` and
  `EuclideanSpace ℝ (Fin 1)` (the positions here) meet all of them.
- "closed" means the step finishes the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `S : HarmonicOscillator` | an oscillator: fields `S.m`, `S.k : ℝ` with `S.m_pos : 0 < S.m`, `S.k_pos : 0 < S.k` |
| `IC : InitialConditions` | initial position `IC.x₀` and velocity `IC.v₀`, both in `EuclideanSpace ℝ (Fin 1)` |
| `EuclideanSpace ℝ (Fin 1)` | `ℝ¹` as a vector space with the dot product (positions and velocities live here) |
| `Time` | a structure wrapping a real number `t.val`; `0 : Time` is time zero |
| `InitialConditions.trajectory S IC` | how `IC.trajectory S` is printed: physlib's explicit solution, `t ↦ cos(ωt)·x₀ + (sin(ωt)/ω)·v₀` |
| `∂ₜ f t` | the time derivative of `f : Time → M` at `t`; `∂ₜ (∂ₜ f) t` is the acceleration |
| `fderiv ℝ f t` | the Fréchet derivative of `f` at `t`: a continuous linear map; `∂ₜ f t = (fderiv ℝ f t) 1` (R2) |
| `E →L[ℝ] F` | continuous ℝ-linear maps from `E` to `F`; `(L - M) v` is a difference of maps applied to `v` |
| `ContDiff ℝ ∞ f` | `f` is smooth (`C^∞`); `∞` is notation from `open ContDiff` |
| `Differentiable ℝ f` | `f` is differentiable at every point, i.e. `∀ x, DifferentiableAt ℝ f x` |
| `r • v` | scalar `r : ℝ` times vector `v`; between two reals `•` is `*` (`smul_eq_mul`, R21) |
| `⟪u, v⟫_ℝ` | the real inner product of `u` and `v`; `⟪v, v⟫_ℝ = ‖v‖²` |
| `S.EquationOfMotion x` | `x` solves the Euler–Lagrange equation; for smooth `x` it is Newton's law (R10–R12) |
| `S.force x` | the force at position `x`, equal to `-S.k • x` (R14) |
| `S.energy x t` | kinetic plus potential energy of the path `x` at time `t` (R15) |
| `S.kineticEnergy z t` | the kinetic energy `1 / 2 * S.m * ⟪∂ₜ z t, ∂ₜ z t⟫_ℝ`, a real number (R15) |
| `S.potentialEnergy v` | the potential energy `(1 / 2) • S.k • ⟪v, v⟫_ℝ` at position `v`, a real number (R15) |
| `-S.k • x` | `(-S.k) • x`: the real scalar `-S.k` times the vector `x` |
| `h : 1 / 2 = 0 ∨ …` | `1 / 2` here is the real number `0.5` (physlib writes `1 / (2 : ℝ)`), so this disjunct is false |
| `0 t` | the zero function applied to `t`; `simp` turns it into `0` |
| `y : T := e` | a local definition made by `set` (R27): `y` is a name for `e` |
| `fun x_1 => x x_1 - …` | Lean renamed the bound variable to `x_1` because `x` is already taken |

---

## Part 1 · `deriv_sub` (milestone 1)

Statement: for differentiable paths `f g : Time → EuclideanSpace ℝ (Fin 1)`,
`∂ₜ (fun t => f t - g t) = fun t => ∂ₜ f t - ∂ₜ g t`: the derivative of a difference is the difference
of derivatives. Used twice in Part 2 (velocity, then acceleration) and once in Part 4.

**R1 · `funext t`** changes the **goal and the context**: an equation of functions becomes one at a
fresh point `t`. Placeholders: `{α β : Type} (f g : α → β)`.

| Before | After |
|---|---|
| `⊢ f = g` | `t : α ⊢ f t = g t` |

**R2 · `simp only [Time.deriv_eq]`** changes the **goal**. The lemma is `∂ₜ f t = (fderiv ℝ f t) 1`:
physlib's time derivative is the Fréchet derivative applied to the unit time step `1`. `simp only`
rewrites every `∂ₜ` in the goal. Placeholders:
`{M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] (f : Time → M) (t : Time)`.

| Before | After |
|---|---|
| `⊢ P (∂ₜ f t)` | `⊢ P ((fderiv ℝ f t) 1)` |

**R3 · `rw [fderiv_fun_sub hf hg]`** changes the **goal**. The lemma is
`DifferentiableAt ℝ f x → DifferentiableAt ℝ g x → fderiv ℝ (fun y => f y - g y) x = fderiv ℝ f x - fderiv ℝ g x`.
From `hf : Differentiable ℝ f` you get `hf x : DifferentiableAt ℝ f x`. Placeholders:
`{E F : Type}` normed real spaces, `(f g : E → F) (x : E)`.

| Before | After |
|---|---|
| `⊢ P (fderiv ℝ (fun y => f y - g y) x)` | `⊢ P (fderiv ℝ f x - fderiv ℝ g x)` |

**R4 · `simp only [sub_apply]`** changes the **goal**. The lemma is `(L - M) v = L v - M v`.
Placeholders: `(L M : E →L[ℝ] F) (v : E)`. In the milestone the goal then reads `a - b = a - b` and
`simp only` closes it. R2, R3, R4 fit in one `simp only [Time.deriv_eq, fderiv_fun_sub (hf t) (hg t), sub_apply]`.

| Before | After |
|---|---|
| `⊢ P ((L - M) v)` | `⊢ P (L v - M v)` |

**W1** does the same for a sum (`fderiv_fun_add`, `add_apply`):

```lean-goal
⊢ ∂ₜ (fun t => f t + g t) t = ∂ₜ f t + ∂ₜ g t
⊢ (fderiv ℝ (fun t => f t + g t) t) 1 = (fderiv ℝ f t) 1 + (fderiv ℝ g t) 1
⊢ (fderiv ℝ f t + fderiv ℝ g t) 1 = (fderiv ℝ f t) 1 + (fderiv ℝ g t) 1
```

---

## Part 2 · `eom_sub` (milestone 2)

Statement: if `x` is smooth and solves the equation of motion, so does `fun t => x t - IC.trajectory S t`.
Route: turn every `EquationOfMotion` into Newton's law `S.m • ∂ₜ (∂ₜ z) t = S.force (z t)`, split the
acceleration of the difference with milestone 1 (twice), and use Hooke's law `S.force x = -S.k • x`.

### Smoothness

**R5 · `fun_prop`** **closes** a goal `ContDiff ℝ n f`, `Differentiable ℝ f` or `Continuous f` when `f` is
built from pieces it knows. physlib registers `InitialConditions.trajectory_contDiff`, so
`fun_prop` proves `ContDiff ℝ ∞ (IC.trajectory S)` directly. Placeholders: `(f : ℝ → E) (hf : ContDiff ℝ ∞ f) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ ContDiff ℝ ∞ fun t => c • f t` | closed |

**R6 · `have h := hf.sub hg`** (lemma `ContDiff.sub`) changes the **context**: the difference of two
smooth paths is smooth. This is the argument `hz` that R12 and R28 need for `x − T`. Placeholders:
`(f g : Time → E) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)`.

| Before | After |
|---|---|
| `⊢ ContDiff ℝ ∞ fun t => f t - g t` | `h : ContDiff ℝ ∞ fun x => f x - g x ⊢ ContDiff ℝ ∞ fun t => f t - g t` |

**R7 · `have h := hf.differentiable (by simp)`** (lemma `ContDiff.differentiable : ContDiff 𝕜 n f → n ≠ 0 → Differentiable 𝕜 f`)
changes the **context**. The `(by simp)` proves the side condition `∞ ≠ 0`. Placeholders:
`(f : Time → E) (hf : ContDiff ℝ ∞ f)`.

| Before | After |
|---|---|
| `⊢ Differentiable ℝ f` | `h : Differentiable ℝ f ⊢ Differentiable ℝ f` |

**R8 · `have h := Time.deriv_differentiable_of_contDiff f hf`** changes the **context**: the velocity
`∂ₜ f` of a smooth path is differentiable. You need it for the second use of milestone 1, on
`∂ₜ (fun t => ∂ₜ x t - ∂ₜ T t)`.

| Before | After |
|---|---|
| `⊢ Differentiable ℝ (∂ₜ f)` | `h : Differentiable ℝ (∂ₜ f) ⊢ Differentiable ℝ (∂ₜ f)` |

### The equation of motion as Newton's law

**R9 · `have h := IC.trajectory_equationOfMotion S`** changes the **context**: the explicit trajectory
solves the equation of motion. Placeholders: `(S : HarmonicOscillator) (IC : InitialConditions)`.

| Before | After |
|---|---|
| `⊢ S.EquationOfMotion (InitialConditions.trajectory S IC)` | `h : S.EquationOfMotion (InitialConditions.trajectory S IC) ⊢ S.EquationOfMotion (InitialConditions.trajectory S IC)` |

**R10 · `(S.equationOfMotion_iff_newtons_2nd_law z hz).1 hE`** is a proof of Newton's law for `z`: with
`have hz2 := …` the **context** gains it, with `exact …` it **closes** the goal (shown). The lemma
is `ContDiff ℝ ∞ z → (S.EquationOfMotion z ↔ ∀ t, S.m • ∂ₜ (∂ₜ z) t = S.force (z t))`; `.1` is the
`→` half. Use it to get Newton's law for the trajectory (from R9, with `hz` from R5). Placeholders:
`(z : Time → EuclideanSpace ℝ (Fin 1)) (hz : ContDiff ℝ ∞ z) (hE : S.EquationOfMotion z)`.

| Before | After |
|---|---|
| `hE : S.EquationOfMotion z ⊢ ∀ (t : Time), S.m • ∂ₜ (∂ₜ z) t = S.force (z t)` | closed |

**R11 · `rw [S.equationOfMotion_iff_newtons_2nd_law _ hz] at hE`** changes the **context**: `hE` itself
becomes Newton's law. The `_` is `z`, read off `hz`.

| Before | After |
|---|---|
| `hE : S.EquationOfMotion z ⊢ G` | `⊢ G`, now with `hE : ∀ (t : Time), S.m • ∂ₜ (∂ₜ z) t = S.force (z t)` |

**R12 · `rw [S.equationOfMotion_iff_newtons_2nd_law _ hz]`** changes the **goal**. For the difference
`x − T`, `hz` is `hx.sub hT` (R6). Follow it with `intro t`.

| Before | After |
|---|---|
| `⊢ S.EquationOfMotion z` | `⊢ ∀ (t : Time), S.m • ∂ₜ (∂ₜ z) t = S.force (z t)` |

### Splitting the acceleration, then Hooke's law

After `intro t` the goal is `S.m • ∂ₜ (∂ₜ fun x_1 => x x_1 - T x_1) t = S.force (x t - T t)`.
`rw [deriv_sub _ _ h₁ h₂]` with `h₁, h₂` from R7 turns the inner `∂ₜ` into
`fun t => ∂ₜ x t - ∂ₜ T t`; a second `rw [deriv_sub _ _ h₃ h₄]` with `h₃, h₄` from R8 splits the outer one.
The goal is then `S.m • (∂ₜ (∂ₜ x) t - ∂ₜ (∂ₜ T) t) = …` (with a `fun t => …` applied to `t`, which `rw` sees through).

**R13 · `rw [smul_sub]`** changes the **goal**. The lemma is `r • (x - y) = r • x - r • y`. After it, the
two terms are exactly the left sides of the Newton laws, so `rw [h, hT2]` replaces them by forces.
Placeholders: `{E : Type} [AddCommGroup E] [Module ℝ E] (r : ℝ) (x y : E)`.

| Before | After |
|---|---|
| `⊢ P (r • (x - y))` | `⊢ P (r • x - r • y)` |

**R14 · `simp only [force_eq_linear]`** changes the **goal**. The lemma is
`HarmonicOscillator.force_eq_linear : S.force x = -S.k • x` (Hooke's law). After `rw [h, hT2]` the
goal is `S.force (x t) - S.force (T t) = S.force (x t - T t)`; `simp only [force_eq_linear, smul_sub]`
(R14, R13) closes it. Placeholders: `(x : EuclideanSpace ℝ (Fin 1))`.

| Before | After |
|---|---|
| `⊢ P (S.force x)` | `⊢ P (-S.k • x)` |

---

## Part 3 · `eq_zero_of_energy_zero` (milestone 3)

Statement: if `S.energy y t = 0` for every `t`, then `y = 0`. Start with `funext t` (R1); the goal
is `y t = 0 t`. Show both energy terms are `≥ 0`, so the potential term is `0`, so `⟪y t, y t⟫_ℝ = 0`.

**R15 · `simp only [energy, kineticEnergy, potentialEnergy]`** changes the **goal** (or `at h`):
it unfolds the energy into its definition. Placeholders:
`(S : HarmonicOscillator) (z : Time → EuclideanSpace ℝ (Fin 1)) (t : Time)`. The first `1 / 2` is a
real number multiplied with `*`; the second acts with `•` and is also real.

| Before | After |
|---|---|
| `⊢ P (S.energy z t)` | `⊢ P (1 / 2 * S.m * ⟪∂ₜ z t, ∂ₜ z t⟫_ℝ + (1 / 2) • S.k • ⟪z t, z t⟫_ℝ)` |

### Both terms are nonnegative

**R16 · `mul_nonneg ha hb`** **closes** `0 ≤ a * b` from `ha : 0 ≤ a` and `hb : 0 ≤ b`.
`S.kineticEnergy y t` unfolds by definition to `1 / 2 * S.m * ⟪…⟫`, which is `(1 / 2 * S.m) * ⟪…⟫`, so
`mul_nonneg (mul_nonneg h½ hm) hi` proves `0 ≤ S.kineticEnergy y t` as a term, with `h½ := by norm_num`.
Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ a * b` | closed |

**R17 · `S.m_pos.le`** changes the **context**: `S.m_pos : 0 < S.m`, and `.le` (lemma `LT.lt.le`) weakens
`<` to `≤`. Likewise `S.k_pos.le : 0 ≤ S.k`.

| Before | After |
|---|---|
| `⊢ 0 ≤ S.m` | `h : 0 ≤ S.m ⊢ 0 ≤ S.m` |

**R18 · `real_inner_self_nonneg`** **closes** `0 ≤ ⟪x, x⟫_ℝ` (as a term: the last argument of R16 and R19).
The vector `x` is implicit; Lean reads it off the expected type. Placeholders: `{E : Type}` a real inner
product space, `(x : E)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ ⟪x, x⟫_ℝ` | closed |

**R19 · `smul_nonneg ha hb`** **closes** `0 ≤ a • b`, as R16 but for `•`. `S.potentialEnergy (y t)`
unfolds to `(1 / 2) • S.k • ⟪y t, y t⟫_ℝ`, so `smul_nonneg h½ (smul_nonneg hk hi)` proves it.

| Before | After |
|---|---|
| `⊢ 0 ≤ a • b` | closed |

**R20 · `((add_eq_zero_iff_of_nonneg ha hb).mp hab).2`** changes the **context**. The lemma is
`0 ≤ a → 0 ≤ b → (a + b = 0 ↔ a = 0 ∧ b = 0)`; `.mp` uses the `→` half and `.2` takes the second
conjunct. With `hab := hE t` (`S.energy y t` is by definition `kinetic + potential`) you get
`S.potentialEnergy (y t) = 0`.

| Before | After |
|---|---|
| `hab : a + b = 0 ⊢ b = 0` | `h : b = 0 ⊢ b = 0` |

### From `potential = 0` to `y t = 0`

Unfold `potentialEnergy` in `h` (R15), then R21–R23; they fit in one
`simp only [potentialEnergy, smul_eq_mul, mul_eq_zero, S.k_ne_zero] at h`.

**R21 · `simp only [smul_eq_mul] at h`** changes the **context**: `a • b` with both real becomes `a * b`.

| Before | After |
|---|---|
| `h : a • b • c = 0 ⊢ G` | `h : a * (b * c) = 0 ⊢ G` |

**R22 · `simp only [mul_eq_zero] at h`** changes the **context**. The lemma is `a * b = 0 ↔ a = 0 ∨ b = 0`
(ℝ has no zero divisors); on a nested product it gives a nested `∨`.

| Before | After |
|---|---|
| `h : a * (b * c) = 0 ⊢ G` | `h : a = 0 ∨ b = 0 ∨ c = 0 ⊢ G` |

**R23 · `simp only [S.k_ne_zero] at h`** changes the **context**. `S.k_ne_zero : S.k ≠ 0`; a hypothesis
`a ≠ 0` given to `simp` rewrites `a = 0` to `False`.

| Before | After |
|---|---|
| `h : S.k = 0 ∨ c = 0 ⊢ G` | `h : False ∨ c = 0 ⊢ G` |

**R24 · `rw [inner_self_eq_zero]`** changes the **goal** (with `at h`, the hypothesis): the lemma is
`⟪x, x⟫_ℝ = 0 ↔ x = 0` (a positive-definite inner product). It is a `simp` lemma, so R25 and R26 use it
without being told.

| Before | After |
|---|---|
| `⊢ ⟪x, x⟫_ℝ = 0` | `⊢ x = 0` |

**R25 · `norm_num`** changes the **goal**; `norm_num at h` does the same to `h`, which is how the milestone
uses it (`h : 1 / 2 = 0 ∨ False ∨ ⟪y t, y t⟫_ℝ = 0` becomes `h : y t = 0`). It decides `1 / 2 = 0`
(false), drops the `False` disjuncts and applies `simp` lemmas such as R24.

| Before | After |
|---|---|
| `⊢ 1 / 2 = 0 ∨ False ∨ ⟪x, x⟫_ℝ = 0` | `⊢ x = 0` |

**R26 · `simpa using h`** **closes** the goal: it simplifies the goal and `h` the same way and matches
them. Here `simp` turns `0 t` into `0`.

| Before | After |
|---|---|
| `h : f t = 0 ⊢ f t = 0 t` | closed |

**W2** chains R21, R22, an `S.k_ne_zero`-style hypothesis and R25 on `(1 / 3) • c • ⟪v, v⟫_ℝ = 0`:

```lean-goal
⊢ v = 0
```

after `simp only [smul_eq_mul, mul_eq_zero, hc] at h` the hypothesis is `1 / 3 = 0 ∨ False ∨ ⟪v, v⟫_ℝ = 0`,
and `norm_num at h` leaves `h : v = 0`.

---

## Part 4 · `trajectory_unique`

Statement: a smooth solution `x` with `x 0 = IC.x₀` and `∂ₜ x 0 = IC.v₀` equals `IC.trajectory S`.

**R27 · `set y := e with hy`** changes the **context and the goal**: `y` becomes a name for `e`
(shown as `y : T := e`), `hy : y = e` is added, and every `e` in the goal is replaced by `y`. Because
`y` is defined as `e`, a term about `e` (such as `eom_sub S IC x hx h`) is accepted where one about
`y` is expected. Placeholders: `(f g : ℝ → ℝ)`.

| Before | After |
|---|---|
| `⊢ P fun t => f t - g t` | `y : ℝ → ℝ := fun t => f t - g t, hy : y = fun t => f t - g t ⊢ P y` |

**R28 · `rw [S.energy_conservation_of_equationOfMotion' z hz hE]`** changes the **goal**. The lemma is
`ContDiff ℝ ∞ z → S.EquationOfMotion z → ∀ t, S.energy z t = S.energy z 0`: the energy of a solution
is constant. For `z = y`: `hz` is `hx.sub hT` (R6), `hE` is milestone 2.

| Before | After |
|---|---|
| `⊢ P (S.energy z t)` | `⊢ P (S.energy z 0)` |

### The energy at time 0

Prove two facts first, each with `rw [hy]` and then `simp`:
`hv0 : ∂ₜ y 0 = 0` (after `rw [hy, deriv_sub _ _ h₁ h₂]` with R7, the goal is
`(fun t => ∂ₜ x t - ∂ₜ T t) 0 = 0`; `simp [hv]` closes it with R30 and `sub_self : a - a = 0`) and
`hy0 : y 0 = 0` (after `rw [hy]` the goal is `(fun t => x t - T t) 0 = 0`; `simp [h0]` closes it with R29 and `sub_self`).

**R29 · `InitialConditions.trajectory_position_at_zero`** changes the **goal**: `IC.trajectory S 0 = IC.x₀`.
A `simp` lemma: plain `simp` uses it.

| Before | After |
|---|---|
| `⊢ P (InitialConditions.trajectory S IC 0)` | `⊢ P IC.x₀` |

**R30 · `InitialConditions.trajectory_velocity_at_zero`** changes the **goal**: `∂ₜ (IC.trajectory S) 0 = IC.v₀`.
Also a `simp` lemma.

| Before | After |
|---|---|
| `⊢ P (∂ₜ (InitialConditions.trajectory S IC) 0)` | `⊢ P IC.v₀` |

Then unfold the energy (R15), `rw [hv0, hy0]`, and close with R31. (`simp [energy, kineticEnergy, potentialEnergy, hv0, hy0]`
does all three.)

**R31 · `simp`** **closes** an expression built from `⟪0, 0⟫_ℝ`: `inner_zero_left` (`⟪0, v⟫_ℝ = 0`),
`mul_zero`, `smul_zero`, `add_zero`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ a * ⟪0, 0⟫_ℝ + b • ⟪0, 0⟫_ℝ = 0` | closed |

### From `y = 0` to `x = T`

After `funext t` (R1) the goal is `x t = T t`. Milestone 3 gives `y = 0`.

**R32 · `congrFun h t`** changes the **context**: from `h : f = g` (functions) it gives `f t = g t`.
On milestone 3 it gives `y t = 0 t`. Placeholders: `{α β : Type} (f g : α → β) (t : α)`.

| Before | After |
|---|---|
| `hfg : f = g ⊢ f t = g t` | `h : f t = g t ⊢ f t = g t` |

**R33 · `sub_eq_zero.mp`** **closes** `a = b` from `a - b = 0`. The lemma is `a - b = 0 ↔ a = b`.
`y t = 0 t` is by definition `x t - T t = 0`, so `exact sub_eq_zero.mp (…)` accepts it without unfolding.

| Before | After |
|---|---|
| `hab : a - b = 0 ⊢ a = b` | closed |

**W3** is the same ending for real functions, with the `0 t` cleaned up by `Pi.zero_apply` first:

```lean-goal
⊢ f = g
⊢ f t = g t
```

---

## Traps

- `(1 / 2) • v` that you type yourself defaults to the natural number `1 / 2`, which is `0`. Write
  `(1 / 2 : ℝ)`. The `(1 / 2)` that physlib's `potentialEnergy` prints is already real.
- `hx.differentiable` needs the argument `(by simp)` for `∞ ≠ 0` (R7); without it you get an implication,
  not `Differentiable ℝ x`.
- `fderiv_fun_sub` needs `DifferentiableAt` at the point: pass `hf t`, not `hf` (R3).
- The second split of `∂ₜ (∂ₜ (x − T))` needs differentiability of the VELOCITIES `∂ₜ x`, `∂ₜ T`, which
  comes from smoothness (R8), not from R7.
- `rw [h, hT2]` only fires after `smul_sub` (R13) has made `S.m • ∂ₜ (∂ₜ x) t` appear literally.
- `eom_sub` is stated for `fun t => x t - IC.trajectory S t`. Keep `y` in exactly that form (R27), or the
  milestones will not match.
- `S.energy y t` is `kinetic + potential` only by definition: `add_eq_zero_iff_of_nonneg` (R20) accepts
  `hE t` directly, but `rw` would not see the `+` without unfolding (R15).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| equation of functions → at a point | `funext t` | R1 |
| `∂ₜ` of a difference | `simp only [Time.deriv_eq, fderiv_fun_sub (hf t) (hg t), sub_apply]` | R2–R4 |
| smoothness of the trajectory | `fun_prop` | R5 |
| smoothness of `x − T` | `hx.sub hT` | R6 |
| `Differentiable ℝ x` from smooth | `hx.differentiable (by simp)` | R7 |
| `Differentiable ℝ (∂ₜ x)` from smooth | `deriv_differentiable_of_contDiff _ hx` | R8 |
| the trajectory solves the EOM | `IC.trajectory_equationOfMotion S` | R9 |
| EOM ↔ Newton's law | `(S.equationOfMotion_iff_newtons_2nd_law _ hz).1 hE`, `rw [… _ hz] at h`, `rw [… _ hz]` | R10–R12 |
| `r • (a - b)` | `smul_sub` | R13 |
| Hooke's law | `force_eq_linear` | R14 |
| unfold the energy | `simp only [energy, kineticEnergy, potentialEnergy]` | R15 |
| `0 ≤ a * b`, `0 ≤ a • b` | `mul_nonneg`, `smul_nonneg` | R16, R19 |
| `0 ≤ S.m`, `0 ≤ S.k` | `S.m_pos.le`, `S.k_pos.le` | R17 |
| `0 ≤ ⟪v, v⟫_ℝ` | `real_inner_self_nonneg` | R18 |
| one of two nonneg summands is 0 | `((add_eq_zero_iff_of_nonneg ha hb).mp hab).2` | R20 |
| `a • b • c = 0` → which factor | `simp only [smul_eq_mul, mul_eq_zero, S.k_ne_zero] at h` | R21–R23 |
| `⟪v, v⟫_ℝ = 0` → `v = 0`, numerals | `norm_num at h` (uses `inner_self_eq_zero`) | R24, R25 |
| close `y t = 0 t` from `h : y t = 0` | `simpa using h` | R26 |
| name `x − T` | `set y := fun t => x t - IC.trajectory S t with hy` | R27 |
| energy at `t` = energy at `0` | `rw [S.energy_conservation_of_equationOfMotion' y hz hE]` | R28 |
| trajectory at `0` | `simp` (`trajectory_position_at_zero`, `trajectory_velocity_at_zero`) | R29, R30 |
| energy of the zero state | `simp` | R31 |
| `f = g` → `f t = g t` | `congrFun h t` | R32 |
| `a - b = 0` → `a = b` | `sub_eq_zero.mp` | R33 |
| see the state | infoview | |
