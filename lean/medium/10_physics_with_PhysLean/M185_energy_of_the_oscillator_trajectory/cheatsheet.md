# M185 · Energy of the oscillator trajectory: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`have`, `rw [h]`, `simp only`, `ring`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's harmonic oscillator
(`HarmonicOscillator`, `InitialConditions`, `trajectory`, `energy`, `Time`, `∂ₜ`), Mathlib's real inner
product spaces (`⟪x, y⟫_ℝ`, `‖x‖`, `•`), `Real.sin`/`Real.cos`, and the tactics `field_simp` and
`linear_combination`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp only`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{E : Type}` is any type. A bracket such as
  `[InnerProductSpace ℝ E]` is a requirement on `E` (a *type class*). Each entry says which familiar types
  meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `S : HarmonicOscillator` | a physlib oscillator: a structure with fields `S.m` (mass), `S.k` (spring constant) and proofs `S.m_pos : 0 < S.m`, `S.k_pos : 0 < S.k` |
| `S.ω` | the angular frequency, *defined* as `√(S.k / S.m)` (`Real.sqrt`); facts: R1, `S.ω_ne_zero : S.ω ≠ 0` |
| `EuclideanSpace ℝ (Fin 1)` | ℝ¹ as a Mathlib inner product space: vectors with one real coordinate. Positions and velocities live here |
| `IC : InitialConditions` | a structure with `IC.x₀` (position at `t = 0`) and `IC.v₀` (velocity at `t = 0`), both in `EuclideanSpace ℝ (Fin 1)` |
| `InitialConditions.trajectory S IC` | how Lean prints `IC.trajectory S : Time → EuclideanSpace ℝ (Fin 1)`, the solution `t ↦ cos(ωt)·x₀ + (sin(ωt)/ω)·v₀` |
| `t : Time`, `t.val` | physlib's time type wraps one real number; `t.val : ℝ` is that number (`S.ω * t` means `S.ω * t.val`) |
| `∂ₜ x` | the time derivative of `x : Time → EuclideanSpace ℝ (Fin 1)`, again a function of time; `∂ₜ x t` is the velocity at `t` |
| `S.energy x t` | `kineticEnergy + potentialEnergy` at time `t` (R3) |
| `⟪x, y⟫_ℝ` | the real inner product of `x` and `y` (in ℝ¹: the product of the coordinates) |
| `‖x‖` | the norm, `‖x‖ ^ 2 = ⟪x, x⟫_ℝ` (R12) |
| `r • x` | scalar `r : ℝ` times vector `x`. `•` binds to the right: `a • b • x` is `a • (b • x)` |
| `-S.ω • sin (…) • IC.x₀` | `(-S.ω) • (sin (…) • IC.x₀)` |
| `(1 / 2) • S.k • ⟪x, x⟫_ℝ` | the same `•`, with `ℝ` acting on `ℝ`: plain multiplication (R10) |
| `sin`, `cos` | `Real.sin`, `Real.cos` (the file opens `Real`) |
| `inst✝ : InnerProductSpace ℝ E` | an unnamed type-class assumption from a `[…]` binder |

---

## Part 1 · `energy_along_trajectory`

Statement: for every oscillator `S`, initial conditions `IC` and time `t`, the energy of the trajectory
at time `t` equals `½ (m ‖v₀‖² + k ‖x₀‖²)`, the energy at `t = 0`. Proof plan: get rid of `S.k` in favour of
`S.m * S.ω ^ 2` (milestone `hk`), unfold the energy, substitute velocity and position, expand every inner
product into the three atoms `‖x₀‖ ^ 2`, `‖v₀‖ ^ 2`, `⟪x₀, v₀⟫_ℝ`, clear `/ S.ω`, and finish modulo
`sin² + cos² = 1`.

### The oscillator's constants

**R1 · `rw [ω_sq]`** changes the **goal**. The lemma is `HarmonicOscillator.ω_sq : S.ω ^ 2 = S.k / S.m`
(written `ω_sq` because the file opens `HarmonicOscillator`). Placeholders: `(S : HarmonicOscillator)`.

| Before | After |
|---|---|
| `⊢ P (S.ω ^ 2)` | `⊢ P (S.k / S.m)` |

**R2 · `field_simp [S.m_ne_zero]`** changes the **goal**: it multiplies out every division whose denominator
it can prove nonzero from the listed facts, then normalises; if a ring identity is left, it closes the goal.
`S.m_ne_zero : S.m ≠ 0` is the physlib fact it needs here. Placeholders: `(S : HarmonicOscillator) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ a = S.m * (a / S.m)` | closed |

### Unfolding the energy and the trajectory

**R3 · `simp only [energy, kineticEnergy, potentialEnergy]`** changes the **goal**: it unfolds the three
physlib definitions `energy = kineticEnergy + potentialEnergy`, `kineticEnergy x t = 1/2 * m * ⟪∂ₜ x t, ∂ₜ x t⟫_ℝ`,
`potentialEnergy x = (1/2) • k • ⟪x, x⟫_ℝ`. Placeholders: `(S : HarmonicOscillator)
(x : Time → EuclideanSpace ℝ (Fin 1)) (τ : Time)`.

| Before | After |
|---|---|
| `⊢ P (S.energy x τ)` | `⊢ P (1 / 2 * S.m * ⟪∂ₜ x τ, ∂ₜ x τ⟫_ℝ + (1 / 2) • S.k • ⟪x τ, x τ⟫_ℝ)` |

**R4 · `rw [InitialConditions.trajectory_velocity]`** changes the **goal**. The lemma is
`∂ₜ (IC.trajectory S) = fun t => -S.ω • sin (S.ω * t.val) • IC.x₀ + cos (S.ω * t.val) • IC.v₀`, an equation
between *functions*; `rw` leaves the application `(fun t => …) τ` unreduced (the next `simp only` reduces it).
Placeholders: `(S : HarmonicOscillator) (IC : InitialConditions) (τ : Time)`.

| Before | After |
|---|---|
| `⊢ P (∂ₜ (InitialConditions.trajectory S IC) τ)` | `⊢ P ((fun t => -S.ω • sin (S.ω * t.val) • IC.x₀ + cos (S.ω * t.val) • IC.v₀) τ)` |

**R5 · `simp only [InitialConditions.trajectory_eq]`** changes the **goal**. The lemma is
`IC.trajectory S = fun t => cos (S.ω * t) • IC.x₀ + (sin (S.ω * t) / S.ω) • IC.v₀`; `simp only` also
substitutes `τ` for `t`. Placeholders: as in R4.

| Before | After |
|---|---|
| `⊢ P (InitialConditions.trajectory S IC τ)` | `⊢ P (cos (S.ω * τ.val) • IC.x₀ + (sin (S.ω * τ.val) / S.ω) • IC.v₀)` |

### Expanding inner products

R6–R12 hold in any real inner product space. Placeholders:
`{E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]` (E has a norm and a real inner product;
`EuclideanSpace ℝ (Fin 1)` and every `EuclideanSpace ℝ (Fin n)` qualify), `(x y z : E) (r : ℝ)`. In the
exercise put R5–R11 into **one** `simp only […]`: it applies them repeatedly until none matches.

**R6 · `inner_add_left`** changes the **goal**: `⟪x + y, z⟫_ℝ = ⟪x, z⟫_ℝ + ⟪y, z⟫_ℝ`.

| Before | After |
|---|---|
| `⊢ P ⟪x + y, z⟫_ℝ` | `⊢ P (⟪x, z⟫_ℝ + ⟪y, z⟫_ℝ)` |

**R7 · `inner_add_right`** changes the **goal**: `⟪x, y + z⟫_ℝ = ⟪x, y⟫_ℝ + ⟪x, z⟫_ℝ`.

| Before | After |
|---|---|
| `⊢ P ⟪x, y + z⟫_ℝ` | `⊢ P (⟪x, y⟫_ℝ + ⟪x, z⟫_ℝ)` |

**R8 · `real_inner_smul_left`** changes the **goal**: `⟪r • x, y⟫_ℝ = r * ⟪x, y⟫_ℝ`.

| Before | After |
|---|---|
| `⊢ P ⟪r • x, y⟫_ℝ` | `⊢ P (r * ⟪x, y⟫_ℝ)` |

**R9 · `real_inner_smul_right`** changes the **goal**: `⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ`.

| Before | After |
|---|---|
| `⊢ P ⟪x, r • y⟫_ℝ` | `⊢ P (r * ⟪x, y⟫_ℝ)` |

**R10 · `smul_eq_mul`** changes the **goal**: `a • b = a * b` for `{α : Type} [Mul α] (a b : α)`; here
`a b : ℝ`. It turns the potential energy's `(1 / 2) • S.k • …` into products.

| Before | After |
|---|---|
| `⊢ P (a • b)` | `⊢ P (a * b)` |

**R11 · `real_inner_comm x y`** changes the **goal**: `⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ`. Give both arguments
(`real_inner_comm IC.x₀ IC.v₀`), so only `⟪v₀, x₀⟫_ℝ` is rewritten and both cross terms become the same
atom `⟪x₀, v₀⟫_ℝ`. (`ring` treats `⟪x₀, v₀⟫_ℝ` and `⟪v₀, x₀⟫_ℝ` as unrelated unknowns. In this exercise each
of them happens to cancel on its own, but one atom gives a shorter goal and a clear coefficient for R15.)

| Before | After |
|---|---|
| `⊢ P ⟪y, x⟫_ℝ` | `⊢ P ⟪x, y⟫_ℝ` |

**R12 · `rw [real_inner_self_eq_norm_sq]`** changes the **goal**: `⟪x, x⟫_ℝ = ‖x‖ ^ 2`. `rw` rewrites the
first instance it finds (all copies of it); repeat it for the second vector.

| Before | After |
|---|---|
| `⊢ P ⟪x, x⟫_ℝ` | `⊢ P (‖x‖ ^ 2)` |

### Finishing the real-number identity

**R13 · `field_simp [S.ω_ne_zero]`** changes the **goal**: like R2, with `S.ω_ne_zero : S.ω ≠ 0`. Both sides
are multiplied by the denominators, and common nonzero factors (such as `S.m`) may be cancelled, so the
result is often much shorter. Placeholders: `(S : HarmonicOscillator) (a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ a / S.ω * b + c = c` | `⊢ a * b + S.ω * c = S.ω * c` |

**R14 · `Real.sin_sq_add_cos_sq`** changes the **goal**: `sin θ ^ 2 + cos θ ^ 2 = 1`. Placeholders:
`(θ : ℝ)`. With `rw` it only fires on that literal sum; in the exercise the squares are spread over the
goal, so hand it to R15 instead.

| Before | After |
|---|---|
| `⊢ P (sin θ ^ 2 + cos θ ^ 2)` | `⊢ P 1` |

**R15 · `linear_combination e * h`** **closes** a goal `a = b` when `a - b - e * (lhs - rhs)` is `0` by
`ring`, where `h : lhs = rhs`. With `h := Real.sin_sq_add_cos_sq θ` the coefficient `e` is whatever
multiplies `sin θ ^ 2` (and `cos θ ^ 2`) in `a - b`. Placeholders: `(a θ : ℝ)`.

| Before | After |
|---|---|
| `⊢ a * sin θ ^ 2 + a * cos θ ^ 2 = a` | closed by `linear_combination a * Real.sin_sq_add_cos_sq θ` |

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: potential energy of `c • x + d • y`** with `c d : ℝ`, `x y : EuclideanSpace ℝ (Fin 1)`. R3 (just
`potentialEnergy`), then one `simp only` with R6–R11, then R12 twice, then `ring`:

```lean-goal
⊢ S.potentialEnergy (c • x + d • y) = 1 / 2 * S.k * (c ^ 2 * ‖x‖ ^ 2 + 2 * c * d * ⟪x, y⟫_ℝ + d ^ 2 * ‖y‖ ^ 2)
⊢ (1 / 2) • S.k • ⟪c • x + d • y, c • x + d • y⟫_ℝ = 1 / 2 * S.k * (c ^ 2 * ‖x‖ ^ 2 + 2 * c * d * ⟪x, y⟫_ℝ + d ^ 2 * ‖y‖ ^ 2)
⊢ 1 / 2 * (S.k * (c * (c * ⟪x, x⟫_ℝ) + c * (d * ⟪x, y⟫_ℝ) + (d * (c * ⟪x, y⟫_ℝ) + d * (d * ⟪y, y⟫_ℝ)))) = 1 / 2 * S.k * (c ^ 2 * ‖x‖ ^ 2 + 2 * c * d * ⟪x, y⟫_ℝ + d ^ 2 * ‖y‖ ^ 2)
⊢ 1 / 2 * (S.k * (c * (c * ‖x‖ ^ 2) + c * (d * ⟪x, y⟫_ℝ) + (d * (c * ⟪x, y⟫_ℝ) + d * (d * ‖y‖ ^ 2)))) = 1 / 2 * S.k * (c ^ 2 * ‖x‖ ^ 2 + 2 * c * d * ⟪x, y⟫_ℝ + d ^ 2 * ‖y‖ ^ 2)
```

Note the single atom `⟪x, y⟫_ℝ` in both cross terms: that is R11's job.

**W2: clear `/ S.ω`, then use `sin² + cos² = 1`.** R13 factors the goal, then R15 with R14 and coefficient
`a`:

```lean-goal
⊢ S.ω ^ 2 * a * (sin θ / S.ω) ^ 2 + a * cos θ ^ 2 = a
⊢ a * (sin θ ^ 2 + cos θ ^ 2) = a
```

---

## Traps

- **Order of R4 and R5.** Rewrite `∂ₜ (IC.trajectory S)` with R4 *before* unfolding the trajectory with R5.
  R4 is stated for `∂ₜ (IC.trajectory S)` literally; once R5 has replaced `IC.trajectory S` by its formula,
  the goal contains `∂ₜ (fun t => …)`, which R4 no longer matches, and you would have to differentiate by hand.
- **Order of the expansion and R12.** Turn `⟪x₀, x₀⟫_ℝ` into `‖x₀‖ ^ 2` only after the `simp only`
  expansion. If `real_inner_self_eq_norm_sq` runs first it turns `⟪traj, traj⟫_ℝ` into `‖traj‖ ^ 2`, and the
  inner-product lemmas R6–R9 have nothing left to expand.
- **`S.k` vs `S.m * S.ω ^ 2`.** The goal mixes `S.k` and `S.ω` (through `/ S.ω` and `S.ω * …`), and nothing
  relates them until you rewrite with the milestone `hk : S.k = S.m * S.ω ^ 2`. Do that before R13, so that
  `field_simp` can cancel the `S.ω ^ 2` against the two `/ S.ω`.
- **`rw [real_inner_comm]` without arguments** rewrites the first inner product it meets, whichever it is
  (`⟪x₀, x₀⟫_ℝ` included). Give the arguments: `real_inner_comm IC.x₀ IC.v₀` (R11).
- **The coefficient in R15.** Read it off the goal after R13: collect what multiplies `sin (S.ω * t.val) ^ 2`
  once the cross terms cancel. A wrong coefficient makes `linear_combination` fail with `ring failed`.
- `S.ω * t` in a lemma statement is `S.ω * t.val` in the infoview: `t : Time` is cast to `ℝ`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `S.ω ^ 2 → S.k / S.m` | `rw [ω_sq]` | R1 |
| clear `/ S.m` or `/ S.ω` | `field_simp [S.m_ne_zero]`, `field_simp [S.ω_ne_zero]` | R2, R13 |
| prove a fact first | `have hk : … := by …` | TACTIC_STATES |
| unfold the energy | `simp only [energy, kineticEnergy, potentialEnergy]` | R3 |
| velocity of the trajectory | `rw [InitialConditions.trajectory_velocity]` | R4 |
| position of the trajectory | `simp only [InitialConditions.trajectory_eq, …]` | R5 |
| `⟪x + y, z⟫`, `⟪x, y + z⟫` | `inner_add_left`, `inner_add_right` | R6, R7 |
| `⟪r • x, y⟫`, `⟪x, r • y⟫` | `real_inner_smul_left`, `real_inner_smul_right` | R8, R9 |
| `a • b → a * b` in `ℝ` | `smul_eq_mul` | R10 |
| `⟪v, x⟫ → ⟪x, v⟫` | `real_inner_comm x v` | R11 |
| `⟪x, x⟫ → ‖x‖ ^ 2` | `rw [real_inner_self_eq_norm_sq]` | R12 |
| substitute the milestone | `rw [hk]` | TACTIC_STATES |
| `sin θ ^ 2 + cos θ ^ 2 = 1` | `Real.sin_sq_add_cos_sq θ` | R14 |
| close modulo that fact | `linear_combination e * Real.sin_sq_add_cos_sq θ` | R15 |
| see the state | infoview | |
