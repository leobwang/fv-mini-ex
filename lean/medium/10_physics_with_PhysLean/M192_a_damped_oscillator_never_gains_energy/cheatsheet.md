# M192 · A damped oscillator never gains energy: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`have`, `intro`, `rw [h]`, `exact`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). M185 (energy of the oscillator trajectory) uses the same
`HarmonicOscillator` energy but is not required. **New here:** physlib's `Time`, its time derivative `∂ₜ`
and the bridge `Time.toRealCLE` to `ℝ`; the damped oscillator `DampedHarmonicOscillator` and its
`energy_dissipation_rate`; Mathlib's Fréchet derivative `fderiv`, the one-variable `deriv`, continuous
linear maps and equivalences, the chain rule `fderiv_comp`, `antitone_of_deriv_nonpos`, real inner products
`⟪u, v⟫_ℝ`, and `nlinarith`.

**Physics in one paragraph.** A mass `m > 0` on a spring of stiffness `k > 0` with friction coefficient
`γ ≥ 0` moves along a line; its position `x t` obeys `m ẍ + γ ẋ + k x = 0`. physlib stores the position as a
1-dimensional vector `x t : EuclideanSpace ℝ (Fin 1)`, so squares are inner products: the energy is
`E t = ½ m ⟪ẋ, ẋ⟫_ℝ + ½ k ⟪x, x⟫_ℝ` (kinetic + potential). Differentiating and using the equation of
motion gives `Ė = ẋ · (m ẍ + k x) = -γ ⟪ẋ, ẋ⟫_ℝ ≤ 0` (physlib proves this equality). The exercise is the
calculus step "derivative ≤ 0 everywhere ⇒ `E` decreases", which Mathlib states only for functions
`ℝ → ℝ`, while `E` is a function `Time → ℝ`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. For an entry that changes the **context**, the goal is just `P : Prop` and a
  hypothesis `k : (new fact) → P` finishes the example.
- Placeholders are written as Lean binders. `{E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]` says `E`
  is a real normed vector space (a vector space with a norm `‖·‖`); `ℝ`, `Time` and
  `EuclideanSpace ℝ (Fin 1)` all qualify. `[InnerProductSpace ℝ F]` adds a real inner product `⟪·, ·⟫_ℝ`;
  `ℝ` and `EuclideanSpace ℝ (Fin 1)` qualify.
- Mathlib states its calculus lemmas over any scalar field `𝕜` (`ℝ` or `ℂ`); in this exercise `𝕜` is always `ℝ`,
  so read `fderiv 𝕜` as `fderiv ℝ`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Time` | physlib's time: a structure with one field `val : ℝ`. `t.val` (also printed `val t`) is its real value |
| `S : DampedHarmonicOscillator` | the data `S.m`, `S.k : ℝ` (positive, from `HarmonicOscillator`) and `S.γ : ℝ` with `S.γ_nonneg : 0 ≤ S.γ` |
| `EuclideanSpace ℝ (Fin 1)` | `ℝ¹` as an inner product space; positions and velocities live here |
| `⟪u, v⟫_ℝ` | the real inner product of `u` and `v` (on `ℝ¹`: the product `u₀ v₀`); `⟪v, v⟫_ℝ = ‖v‖²` |
| `ContDiff ℝ ∞ x` | `x` is smooth (infinitely differentiable); `∞` is notation from `open ContDiff` |
| `S.EquationOfMotion x` | `∀ t, S.m • ∂ₜ (∂ₜ x) t + S.γ • ∂ₜ x t + S.k • x t = 0`, where `c • v` is scalar times vector |
| `S.energy x t` | `½ m ⟪ẋ, ẋ⟫_ℝ + ½ k ⟪x, x⟫_ℝ` at time `t` (inherited from `HarmonicOscillator`) |
| `∂ₜ f t` | physlib's time derivative `Time.deriv f t`, defined as `fderiv ℝ f t 1` (R9) |
| `fderiv ℝ f t` | the Fréchet derivative of `f` at `t`: the continuous linear map `L` with `f (t + h) ≈ f t + L h` |
| `(fderiv ℝ f t) 1` | that linear map applied to the direction `1`: the ordinary derivative |
| `_root_.deriv g r` | Mathlib's one-variable derivative of `g : ℝ → F` at `r`. Printed with `_root_.` because `open Time` makes plain `deriv` mean `Time.deriv` |
| `E →L[ℝ] F` | continuous `ℝ`-linear maps from `E` to `F` |
| `E ≃L[ℝ] F` | continuous linear equivalences: linear bijections, continuous both ways |
| `toRealCLE` | `Time.toRealCLE : Time ≃L[ℝ] ℝ`, the map `t ↦ t.val`. `toRealCLE.symm : ℝ ≃L[ℝ] Time` sends `r ↦ ⟨r⟩` |
| `⇑e`, `↑e` | the equivalence `e` used as a function, resp. as a continuous linear map `E →L[ℝ] F` |
| `A ∘SL B` | composition of continuous linear maps, `A.comp B` (`SL`: semilinear; here plain linear) |
| `Differentiable ℝ f` | `f` is differentiable at every point: by definition `∀ t, DifferentiableAt ℝ f t` |
| `Antitone g` | `g` is non-increasing: `∀ ⦃a b⦄, a ≤ b → g b ≤ g a`. `⦃a b⦄` are *strict-implicit*: Lean fills them in once you pass `a ≤ b` |
| `g : ℝ → ℝ := f ∘ ⇑toRealCLE.symm` | a `let` in the context: `g` together with its definition. After `congr 1` it may print as `g : ℝ → ℝ := ⋯` (body elided, still there) |
| `case e_6` | the label of the goal `congr 1` produced (compare the arguments) |

---

## Part 1 · `energy_antitone`

Statement: for a damped oscillator `S`, a smooth path `x` solving the equation of motion, and times
`t₁ ≤ t₂`, `S.energy x t₂ ≤ S.energy x t₁`. Plan: move `S.energy x` to a function `g : ℝ → ℝ`, show
`deriv g r ≤ 0` through the chain rule and `energy_dissipation_rate`, then use `antitone_of_deriv_nonpos`.

### The energy is differentiable

**R1 · `S.energy_differentiable y hy`** changes the **context**. The lemma
`HarmonicOscillator.energy_differentiable` says `ContDiff ℝ ∞ y → Differentiable ℝ (S.energy y)`. A
`DampedHarmonicOscillator` extends `HarmonicOscillator`, so `S.energy …` works on it directly.
Placeholders: `(S : DampedHarmonicOscillator) (y : Time → EuclideanSpace ℝ (Fin 1)) (hy : ContDiff ℝ ∞ y)`.

| Before | After `have hE := S.energy_differentiable y hy` |
|---|---|
| `⊢ P` | `hE : Differentiable ℝ (S.energy y) ⊢ P` |

### From `Time` to `ℝ`

**R2 · `let g : ℝ → ℝ := f ∘ Time.toRealCLE.symm`** changes the **context**: it adds `g` and remembers its
body (a `have` would forget it). `f ∘ toRealCLE.symm` is `r ↦ f ⟨r⟩`, the same function read on `ℝ`.
Placeholders: `(f : Time → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (f ∘ ⇑toRealCLE.symm)` | `g : ℝ → ℝ := f ∘ ⇑toRealCLE.symm ⊢ P (f ∘ ⇑toRealCLE.symm)` |

**R3 · `hv.comp hu`** (lemma `Differentiable.comp`) changes the **context**: `Differentiable ℝ v →
Differentiable ℝ u → Differentiable ℝ (v ∘ u)`. The **outer** function's proof comes first. Placeholders:
`{E F G : Type}` real normed spaces, `(u : E → F) (v : F → G)`.

| Before | After `have h := hv.comp hu` |
|---|---|
| `hu : Differentiable ℝ u, hv : Differentiable ℝ v ⊢ P` | `h : Differentiable ℝ (v ∘ u) ⊢ P` |

**R4 · `e.differentiable`, `e.differentiableAt`** (lemmas `ContinuousLinearEquiv.differentiable`,
`ContinuousLinearEquiv.differentiableAt`) change the **context**: a continuous linear equivalence is
differentiable everywhere, and at each point. The exercise uses `e := Time.toRealCLE.symm`. Placeholders:
`{E F : Type}` real normed spaces, `(e : E ≃L[ℝ] F) (x : E)`.

| Before | After |
|---|---|
| `⊢ P` | `h : Differentiable ℝ ⇑e ⊢ P` (from `have h := e.differentiable`) |
| `⊢ P` | `h : DifferentiableAt ℝ (⇑e) x ⊢ P` (from `have h := e.differentiableAt (x := x)`) |

**R5 · `hf t`** changes the **context**: `Differentiable ℝ f` is a `∀`, so applying it to a point gives
`DifferentiableAt` there. Write `hf _` to let Lean find the point. Placeholders: `(f : Time → ℝ) (t : Time)`.

| Before | After `have h := hf t` |
|---|---|
| `hf : Differentiable ℝ f ⊢ P` | `h : DifferentiableAt ℝ f t ⊢ P` |

### The chain rule, step by step (the milestone `deriv g r = ∂ₜ (S.energy x) (toRealCLE.symm r)`)

**R6 · `rw [← fderiv_apply_one_eq_deriv]`** changes the **goal**. The lemma is
`(fderiv 𝕜 u r) 1 = deriv u r` (for `u : 𝕜 → F`); right to left it turns the one-variable derivative into
a Fréchet derivative, the form the chain rule speaks. Placeholders: `{F : Type}` a real normed space,
`(u : ℝ → F) (r : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (_root_.deriv u r)` | `⊢ P ((fderiv ℝ u r) 1)` |

**R7 · `rw [fderiv_comp x hv hu]`** changes the **goal**. The lemma is the chain rule
`fderiv 𝕜 (v ∘ u) x = fderiv 𝕜 v (u x) ∘SL fderiv 𝕜 u x`, with arguments: the point `x` (or `_`),
`hv : DifferentiableAt 𝕜 v (u x)` (from R5: `hE _`), `hu : DifferentiableAt 𝕜 u x` (from R4).
Placeholders: `{E F G : Type}` real normed spaces, `(u : E → F) (v : F → G) (x : E)`.

| Before | After |
|---|---|
| `⊢ P (fderiv ℝ (v ∘ u) x)` | `⊢ P (fderiv ℝ v (u x) ∘SL fderiv ℝ u x)` |

**R8 · `rw [ContinuousLinearEquiv.fderiv]`** changes the **goal**. The lemma is `fderiv 𝕜 (⇑e) x = ↑e`: a
linear map is its own derivative. Placeholders: `{E F : Type}` real normed spaces, `(e : E ≃L[ℝ] F) (x : E)`.

| Before | After |
|---|---|
| `⊢ P (fderiv ℝ (⇑e) x)` | `⊢ P ↑e` |

**R9 · `rw [Time.deriv_eq]`** changes the **goal**. The lemma is `∂ₜ f t = fderiv ℝ f t 1` (true by `rfl`);
it unfolds physlib's time derivative so both sides of the milestone speak `fderiv`. Placeholders:
`{M : Type}` a real normed space, `(f : Time → M) (t : Time)`.

| Before | After |
|---|---|
| `⊢ P (∂ₜ f t)` | `⊢ P ((fderiv ℝ f t) 1)` |

**R10 · `rw [ContinuousLinearMap.comp_apply]`** changes the **goal**. The lemma is `(A ∘SL B) w = A (B w)`.
Placeholders: `{E F G : Type}` real normed spaces, `(A : F →L[ℝ] G) (B : E →L[ℝ] F) (w : E)`.

| Before | After |
|---|---|
| `⊢ P ((A ∘SL B) w)` | `⊢ P (A (B w))` |

After R6–R10 both sides of the milestone are the same linear map `fderiv ℝ (S.energy x) (toRealCLE.symm r)`,
applied to `↑toRealCLE.symm 1` on the left and to `1 : Time` on the right. R11–R14 match the two.

**R11 · `congr 1`** changes the **goal**: an equation `A a = A b` with the same function on both sides becomes
`a = b`. It closes the new goal itself when it is `rfl` or a hypothesis. Placeholders:
`{F : Type}` a real normed space, `(A : ℝ →L[ℝ] F) (a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ A a = A b` | `⊢ a = b` |

**R12 · `ext`** (lemma `Time.ext`) changes the **goal**: two times are equal when their values are.
Placeholders: `(s t : Time)`.

| Before | After |
|---|---|
| `⊢ s = t` | `⊢ s.val = t.val` |

**R13 · `simp [Time.toRealCLE]`** changes the **goal**: unfolding `toRealCLE` lets `simp` compute
`toRealCLE.symm r = ⟨r⟩`, whose value is `r`. Placeholders: `(r : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (↑toRealCLE.symm r).val` | `⊢ P r` |

**R14 · `Time.one_val`** changes the **goal**. The lemma is `val 1 = 1`: the time `1` has real value `1`.
Together, `simp [Time.toRealCLE, Time.one_val]` closes `(↑toRealCLE.symm 1).val = val 1`.

| Before | After `rw [Time.one_val]` |
|---|---|
| `⊢ P (val 1)` | `⊢ P 1` |

### The sign of the derivative

**R15 · `rw [S.energy_dissipation_rate y t hm hy]`** changes the **goal**. The lemma
`DampedHarmonicOscillator.energy_dissipation_rate` says
`S.EquationOfMotion y → ContDiff ℝ ∞ y → ∂ₜ (S.energy y) t = -S.γ * ⟪∂ₜ y t, ∂ₜ y t⟫_ℝ`. The point `t`
may be `_` once the goal fixes it. Placeholders: `(S : DampedHarmonicOscillator)
(y : Time → EuclideanSpace ℝ (Fin 1)) (t : Time) (hm : S.EquationOfMotion y) (hy : ContDiff ℝ ∞ y)`.

| Before | After |
|---|---|
| `⊢ P (∂ₜ (S.energy y) t)` | `⊢ P (-S.γ * ⟪∂ₜ y t, ∂ₜ y t⟫_ℝ)` |

**R16 · `S.γ_nonneg`** changes the **context**: it is a field of the structure, `0 ≤ S.γ`.
Placeholders: `(S : DampedHarmonicOscillator)`.

| Before | After `have h := S.γ_nonneg` |
|---|---|
| `⊢ P` | `h : 0 ≤ S.γ ⊢ P` |

**R17 · `real_inner_self_nonneg (x := v)`** changes the **context**: `0 ≤ ⟪v, v⟫_ℝ`. The vector is an
**implicit** argument named `x`, so pass it by name. Placeholders: `{F : Type} [NormedAddCommGroup F]
[InnerProductSpace ℝ F] (v : F)`.

| Before | After `have h := real_inner_self_nonneg (x := v)` |
|---|---|
| `⊢ P` | `⊢ P`, with `h : 0 ≤ ⟪v, v⟫_ℝ` added |

**R18 · `nlinarith`** **closes** a real (in)equality that follows from the hypotheses after multiplying
pairs of them (here `0 ≤ c` times `0 ≤ q`). `linarith` does only linear combinations and fails on `c * q`.
Facts not yet in the context can be passed: `nlinarith [fact₁, fact₂]`. Placeholders: `(c q : ℝ)`.

| Before | After |
|---|---|
| `hc : 0 ≤ c, hq : 0 ≤ q ⊢ -c * q ≤ 0` | no goals |

### Derivative ≤ 0 ⇒ the function decreases

**R19 · `antitone_of_deriv_nonpos hg hg'`** changes the **context**. The lemma says
`Differentiable ℝ g → (∀ r, deriv g r ≤ 0) → Antitone g`, for `g : ℝ → ℝ` only. Placeholders: `(g : ℝ → ℝ)`.

| Before | After `have hA := antitone_of_deriv_nonpos hg hg'` |
|---|---|
| `hg : Differentiable ℝ g ⊢ P` | `hA : Antitone g ⊢ P` |

**R20 · `(Time.le_def s t).mp hst`** changes the **context**. The lemma is `s ≤ t ↔ s.val ≤ t.val` (true by
`Iff.rfl`); `.mp` uses it left to right. `(Time.le_def _ _).mp` lets Lean find `s`, `t`. Placeholders:
`(s t : Time)`.

| Before | After `have h := (Time.le_def s t).mp hst` |
|---|---|
| `hst : s ≤ t ⊢ P` | `h : s.val ≤ t.val ⊢ P` |

**R21 · `hA hab`** **closes** the goal: `Antitone g` is a function taking `a ≤ b` (with `a`, `b` implicit) to
`g b ≤ g a`, so it can be applied directly, also chained: `antitone_of_deriv_nonpos hg hg' hab`.
Placeholders: `(g : ℝ → ℝ) (a b : ℝ)`.

| Before | After `exact hA hab` |
|---|---|
| `hA : Antitone g, hab : a ≤ b ⊢ g b ≤ g a` | no goals |

**R22 · `exact` up to unfolding** **closes** the goal: `(f ∘ ⇑toRealCLE.symm) t.val` unfolds to `f ⟨t.val⟩`,
which is `f t` (a one-field structure is rebuilt from its field), so a fact about `g (t.val)` proves the
same fact about `f t` with no rewriting. This needs `g` to be a `let` (R2). Placeholders:
`(f : Time → ℝ) (t : Time)`.

| Before | After `exact h` |
|---|---|
| `h : P ((f ∘ ⇑toRealCLE.symm) t.val) ⊢ P (f t)` | no goals |

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: the chain rule the other way**, for `u ∘ toRealCLE : Time → ℝ` with `u : ℝ → ℝ` differentiable.
R9, R7 (with R5, R4), R8, R10, R6 right to left, then R11; `congr 1` closes `toRealCLE t = t.val` by `rfl`
itself and leaves the direction, which `simp [Time.toRealCLE]` closes:

```lean-goal
⊢ ∂ₜ (u ∘ ⇑toRealCLE) t = _root_.deriv u t.val
⊢ (fderiv ℝ (u ∘ ⇑toRealCLE) t) 1 = _root_.deriv u t.val
⊢ (fderiv ℝ u (toRealCLE t) ∘SL fderiv ℝ (⇑toRealCLE) t) 1 = _root_.deriv u t.val
⊢ (fderiv ℝ u (toRealCLE t) ∘SL ↑toRealCLE) 1 = _root_.deriv u t.val
⊢ (fderiv ℝ u (toRealCLE t)) (↑toRealCLE 1) = _root_.deriv u t.val
⊢ (fderiv ℝ u (toRealCLE t)) (↑toRealCLE 1) = (fderiv ℝ u t.val) 1
⊢ ↑toRealCLE 1 = 1
```

**W2: signs from two inner products.** With `hc : 0 ≤ c`, add `0 ≤ ⟪v, v⟫_ℝ` and `0 ≤ ⟪w, w⟫_ℝ` (R17
twice); `nlinarith` (R18) then closes

```lean-goal
⊢ -c * ⟪v, v⟫_ℝ - ⟪w, w⟫_ℝ ≤ 0
```

---

## Traps

- `antitone_of_deriv_nonpos` wants `f : ℝ → ℝ`, but `S.energy x` lives on `Time`: precompose with
  `Time.toRealCLE.symm` (R2) and prove everything about `g`.
- Use `let g := …`, not `have g := …`: `have` forgets the body, so neither the chain rule nor the final
  `exact` (R22) can see that `g` is `S.energy x ∘ ⇑toRealCLE.symm`.
- Under `open Time`, `deriv` is overloaded: Lean picks `Time.deriv` (`∂ₜ`) or Mathlib's `deriv` by the
  argument's type, and prints Mathlib's as `_root_.deriv`. `deriv g r` with `g : ℝ → ℝ` is Mathlib's.
- After the chain rule the direction on the left is `↑toRealCLE.symm 1`, not `1 : Time`. They are equal but
  not syntactically, so `rw`/`rfl` stop there: `congr 1`, `ext`, `simp [Time.toRealCLE, Time.one_val]`
  (R11–R14).
- `fderiv_comp` takes the point first, then the **outer** function's `DifferentiableAt` (at `u x`), then the
  inner one's. `Differentiable.comp` also takes the outer one first: `hE.comp Time.toRealCLE.symm.differentiable`.
- `real_inner_self_nonneg` has its vector implicit: `real_inner_self_nonneg (x := v)`, or let `nlinarith`
  receive it in brackets.
- `nlinarith` only uses facts in the context or in its `[…]` list: add `0 ≤ S.γ` (R16) and
  `0 ≤ ⟪ẋ, ẋ⟫_ℝ` (R17) first.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| energy is differentiable | `S.energy_differentiable x hx` | R1 |
| a function on `ℝ` from one on `Time` | `let g : ℝ → ℝ := f ∘ Time.toRealCLE.symm` | R2 |
| differentiable composition | `hf.comp Time.toRealCLE.symm.differentiable` | R3, R4 |
| `Differentiable` → `DifferentiableAt t` | `hf t` / `hf _` | R5 |
| `deriv g r` → `fderiv ℝ g r 1` | `rw [← fderiv_apply_one_eq_deriv]` | R6 |
| chain rule | `rw [fderiv_comp _ (hf _) e.differentiableAt]` | R7 |
| derivative of a linear equivalence | `rw [ContinuousLinearEquiv.fderiv]` | R8 |
| `∂ₜ f t` → `fderiv ℝ f t 1` | `rw [Time.deriv_eq]` | R9 |
| `(A ∘SL B) w` → `A (B w)` | `rw [ContinuousLinearMap.comp_apply]` | R10 |
| `A a = A b` → `a = b` | `congr 1` | R11 |
| equality in `Time` | `ext` | R12 |
| `↑toRealCLE.symm 1 = 1` after `ext` | `simp [Time.toRealCLE, Time.one_val]` | R13, R14 |
| `∂ₜ (S.energy x) t` → `-S.γ * ⟪ẋ, ẋ⟫_ℝ` | `rw [S.energy_dissipation_rate x _ h hx]` | R15 |
| `0 ≤ S.γ`, `0 ≤ ⟪v, v⟫_ℝ` | `S.γ_nonneg`, `real_inner_self_nonneg (x := v)` | R16, R17 |
| sign of a product | `nlinarith` | R18 |
| derivative ≤ 0 ⇒ antitone | `antitone_of_deriv_nonpos hg hg'` | R19 |
| `t₁ ≤ t₂` → `t₁.val ≤ t₂.val` | `(Time.le_def _ _).mp ht` | R20 |
| use `Antitone g` | `hA hab` | R21 |
| `g t.val` is `f t` | `exact` (no rewrite needed) | R22 |
| see the state | infoview | |
