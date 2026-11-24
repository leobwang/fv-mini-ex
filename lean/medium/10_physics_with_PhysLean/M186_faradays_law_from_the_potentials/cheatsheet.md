# M186 · Faraday's law from the potentials: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). M182 (curl of a gradient) helps but is not needed: here
that fact is a library lemma. **New here:** physlib's electromagnetic potential `ElectromagneticPotential`,
its scalar and vector potentials, the fields `electricField`, `magneticField`, the time derivative `∂ₜ`,
`curl`, `grad` (`∇`); `rw` with lemmas that have hypotheses (side goals); Mathlib's smoothness predicates
`Differentiable`, `ContDiff` and the tactic `fun_prop` that proves them.

**The physics.** A potential $V$ gives a scalar potential $\varphi(t, x) \in \mathbb{R}$ and a vector
potential $A(t, x) \in \mathbb{R}^3$, with $t$ time and $x$ a point of space. The fields are
$E = -\nabla\varphi - \partial_t A$ and $B = \nabla \times A$. Then
$\nabla \times E = -\nabla \times \nabla\varphi - \nabla \times \partial_t A = 0 - \partial_t(\nabla \times A) = -\partial_t B$,
using linearity of the curl, $\nabla \times \nabla \varphi = 0$, and that $\partial_t$ commutes with
$\nabla \times$ (Schwarz, so $A$ must be $C^2$). Each of these steps is one library lemma; each lemma asks
for a smoothness fact, and those are the side goals.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`apply`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal.
- Placeholders are written as Lean binders. `f : Space → EuclideanSpace ℝ (Fin 3)` is a vector field,
  `φ : Space → ℝ` a scalar field, `fₜ : Time → Space → EuclideanSpace ℝ (Fin 3)` a time-dependent vector
  field, `U : ElectromagneticPotential` a potential (the exercise calls it `V`).
- Several cells in one row are several goals, in the order Lean lists them.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Space` | `Space 3`, physlib's 3D space (a point has coordinates `Fin 3 → ℝ`) |
| `Time` | physlib's time axis, a wrapper around one real number |
| `EuclideanSpace ℝ (Fin 3)` | $\mathbb{R}^3$ as a vector type: the values of `E`, `B`, `A`, `curl F` |
| `ElectromagneticPotential` | the 4-potential: a function from spacetime to 4-vectors (dimension `d = 3` by default) |
| `c : SpeedOfLight` | a positive real constant; it only fixes how `φ`, `A` are read off the 4-potential |
| `scalarPotential c V t` | `V.scalarPotential c t : Space → ℝ`, the scalar potential $\varphi$ at time `t` |
| `vectorPotential c V t` | `V.vectorPotential c t : Space → ℝ³`, the vector potential $A$ at time `t` |
| `electricField c V t`, `magneticField c V t` | `V.electricField c t`, `V.magneticField c t : Space → ℝ³`: $E$, $B$ at time `t` (with `open ElectromagneticPotential` the infoview drops the dot) |
| `∇ φ` | `Space.grad φ : Space → ℝ³`, the gradient |
| `∇ ⨯ F` (prints `curl F`) | `Space.curl F : Space → ℝ³`, the curl of `F : Space → ℝ³`; `curl F x` is its value at `x` |
| `∂ₜ g t` | `Time.deriv g t`, the derivative of `g : Time → M` at time `t` |
| `∂ₜ (fun t => A t x) t` | $\partial_t A(t, x)$: differentiate in time at the fixed point `x` |
| `↿fₜ` | `fₜ : Time → Space → M` uncurried, `fun (t, x) => fₜ t x : Time × Space → M` |
| `Differentiable ℝ f` | `f` is (Fréchet) differentiable everywhere |
| `ContDiff ℝ 2 f`, `ContDiff ℝ ∞ f` | `f` is $C^2$, resp. $C^\infty$ (`∞` is notation from `open ContDiff`) |
| `hV : ContDiff ℝ ∞ (V.val 3)` | how the hypothesis `hV : ContDiff ℝ ∞ V` prints: `V.val` is the function underlying `V`; the `3` is the dimension argument `d`, not an application |
| `(fun t x => …) t x` | a beta-redex: `rw` with a lemma of the form `F = fun t x => …` leaves it; it means `…` with `t`, `x` substituted |
| `0 i` | the zero function applied to `i`, i.e. the zero vector |
| `case hf`, `case hf1`, `case hf2` | side goals: the hypotheses `hf`, `hf1`, `hf2` of a lemma used by `rw` |

---

## Part 1 · `faraday`

Statement: for every time `t` and point `x`, `(∇ ⨯ V.electricField c t) x = -∂ₜ (fun t => V.magneticField c t x) t`,
i.e. $(\nabla \times E)(t, x) = -\partial_t B(t, x)$, assuming `hV : ContDiff ℝ ∞ V` (the potential is smooth).

### Fields → potentials

**R1 · `rw [ThreeDimension.electricField_eq_3D]`** changes the **goal**. The lemma is
`V.electricField c = fun t x => -∇ (V.scalarPotential c t) x - ∂ₜ (fun t => V.vectorPotential c t x) t`,
i.e. $E = -\nabla\varphi - \partial_t A$. Placeholders: `(U : ElectromagneticPotential) (c : SpeedOfLight)`,
`P : (Time → Space → EuclideanSpace ℝ (Fin 3)) → Prop`. No side goal.

| Before | After |
|---|---|
| `⊢ P (electricField c U)` | `⊢ P fun t x => -∇ (scalarPotential c U t) x - ∂ₜ (fun t => vectorPotential c U t x) t` |

**R2 · `rw [ThreeDimension.magneticField_eq_3D]`** changes the **goal**. The lemma is
`V.magneticField c = fun t x => curl (V.vectorPotential c t) x`, i.e. $B = \nabla \times A$. Placeholders as in R1.

| Before | After |
|---|---|
| `⊢ P (magneticField c U)` | `⊢ P fun t x => curl (vectorPotential c U t) x` |

In the exercise both rewrites leave beta-redexes such as `curl ((fun t x => …) t) x`. Read them with `t`, `x`
substituted; the next rewrites match through them.

### Rewriting the curl

These lemmas have hypotheses. `rw [lemma]` rewrites with the conclusion and adds each hypothesis as a new
goal. The new goals go **right after the main goal**, so after several such rewrites the main goal is still
first and the newest side goals come next.

**R3 · `rw [Space.fun_curl_sub]`** changes the **goal** and the **goal list**. The lemma is
`Differentiable ℝ f1 → Differentiable ℝ f2 → (curl fun x => f1 x - f2 x) = fun x => curl f1 x - curl f2 x`:
the curl is additive, $\nabla \times (f - g) = \nabla \times f - \nabla \times g$.
Placeholders: `(f g : Space → EuclideanSpace ℝ (Fin 3))`, `P : (Space → EuclideanSpace ℝ (Fin 3)) → Prop`.

| Before | After |
|---|---|
| `⊢ P (curl fun x => f x - g x)` | `⊢ P fun i => curl f i - curl g i`, `⊢ Differentiable ℝ f`, `⊢ Differentiable ℝ g` |

**R4 · `rw [Space.fun_curl_neg]`** changes the **goal** and the **goal list**. The lemma is
`Differentiable ℝ f → (curl fun x => -f x) = fun x => -curl f x`. Placeholders as in R3.

| Before | After |
|---|---|
| `⊢ P (curl fun x => -f x)` | `⊢ P fun i => -curl f i`, `⊢ Differentiable ℝ f` |

**R5 · `rw [Space.curl_of_grad_eq_zero]`** changes the **goal** and the **goal list**. The lemma is
`ContDiff ℝ 2 f → curl (∇ f) = 0`, $\nabla \times \nabla \varphi = 0$ (M182). It needs `curl (∇ φ)` literally,
so it applies only after R4 has pulled the minus sign out. Placeholders: `(φ : Space → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (curl (∇ φ))` | `⊢ P 0`, `⊢ ContDiff ℝ 2 φ` |

**R6 · `rw [Space.time_deriv_curl_commute]`** changes the **goal** and the **goal list**. The lemma is
`ContDiff ℝ 2 ↿fₜ → ∂ₜ (fun t => curl (fₜ t) x) t = curl (fun x => ∂ₜ (fun t => fₜ t x) t) x`:
$\partial_t (\nabla \times f) = \nabla \times (\partial_t f)$ for a $C^2$ field of `(t, x)`. In the exercise it
acts on the right-hand side. Placeholders: `(fₜ : Time → Space → EuclideanSpace ℝ (Fin 3)) (t : Time) (x : Space)`,
`P : EuclideanSpace ℝ (Fin 3) → Prop`.

| Before | After |
|---|---|
| `hf : ContDiff ℝ 2 ↿fₜ ⊢ P (∂ₜ (fun t => curl (fₜ t) x) t)` | `⊢ P (curl (fun x => ∂ₜ (fun t => fₜ t x) t) x)`, `⊢ ContDiff ℝ 2 ↿fₜ` |

### Closing the main goal

**R7 · `simp`** **closes** the main goal. After R1–R6 it reads "$-0 - X = -X$" with `X` the curl of $\partial_t A$
at `x`, wrapped in beta-redexes. `simp` reduces the redexes and uses `Pi.zero_apply` (`(0 : α → β) a = 0`),
`neg_zero` (`-0 = 0`) and `zero_sub` (`0 - a = -a`). Placeholders: `(f : Space → EuclideanSpace ℝ (Fin 3)) (x : Space)`.

| Before | After |
|---|---|
| `⊢ (fun i => (fun i => -0 i) i - f i) x = -f x` | no goals |

### Closing the side goals

**R8 · `fun_prop`** **closes** a goal `Differentiable ℝ F` or `ContDiff ℝ n F` by splitting `F` into pieces
(`+`, `-`, negation, composition, `fun x => …`) and using a lemma registered with `@[fun_prop]` for each piece, plus
hypotheses in the context. It fails (with an error) on a goal that is not of this kind. Placeholders:
`(f : Space → EuclideanSpace ℝ (Fin 3))`.

| Before | After |
|---|---|
| `hf : Differentiable ℝ f ⊢ Differentiable ℝ fun x => -f x` | no goals |

R9–R12 are the registered lemmas `fun_prop` finds for the exercise's side goals. You never have to name
them; they explain why `fun_prop` succeeds with only `hV` in the context.

**R9 · `scalarPotential_contDiff_space_of_smooth`** changes the **goal** (shown with `apply`). The lemma is
`ContDiff ℝ ∞ U → ContDiff ℝ n (U.scalarPotential c t)` for every `n : ℕ`: a smooth potential has a $C^n$
scalar potential at each time. Placeholders: `(U : ElectromagneticPotential) (c : SpeedOfLight) (t : Time)`.

| Before | After |
|---|---|
| `hU : ContDiff ℝ ∞ (U.val 3) ⊢ ContDiff ℝ 2 (scalarPotential c U t)` | `⊢ ContDiff ℝ ∞ (U.val 3)` |

**R10 · `vectorPotential_contDiff_of_smooth`** changes the **goal**. The lemma is
`ContDiff ℝ ∞ U → ContDiff ℝ n ↿(U.vectorPotential c)`: $A$ is $C^n$ jointly in `(t, x)`, which is what R6 needs.
Placeholders as in R9.

| Before | After |
|---|---|
| `hU : ContDiff ℝ ∞ (U.val 3) ⊢ ContDiff ℝ 2 ↿(vectorPotential c U)` | `⊢ ContDiff ℝ ∞ (U.val 3)` |

**R11 · `Space.contDiff_grad`** changes the **goal** (shown with `apply`). The lemma is
`ContDiff ℝ (n + 1) f → ContDiff ℝ n (fun x => ∇ f x)`: the gradient of a $C^{n+1}$ function is $C^n$.
`fun_prop` uses it with `n = 1`, followed by `ContDiff.differentiable_one : ContDiff 𝕜 1 f → Differentiable 𝕜 f`,
to prove the side goal `Differentiable ℝ (∇ (scalarPotential c V t))` of R4. `1 + 1` is `2` by definition, so
`exact hφ` closes the new goal. Placeholders: `(φ : Space → ℝ) (hφ : ContDiff ℝ 2 φ)`.

| Before | After |
|---|---|
| `hφ : ContDiff ℝ 2 φ ⊢ ContDiff ℝ 1 (∇ φ)` | `⊢ ContDiff ℝ (1 + 1) φ` |

**R12 · `Space.time_deriv_differentiable_space`** changes the **goal**. The lemma is
`ContDiff ℝ 2 ↿f → ∀ t, Differentiable ℝ fun x => ∂ₜ (fun t => f t x) t`: the field $\partial_t A$ at a fixed
time is differentiable in `x`. It discharges the second side goal of R3. Placeholders:
`(fₜ : Time → Space → EuclideanSpace ℝ (Fin 3)) (t : Time)`.

| Before | After |
|---|---|
| `hf : ContDiff ℝ 2 ↿fₜ ⊢ Differentiable ℝ fun x => ∂ₜ (fun t => fₜ t x) t` | `⊢ ContDiff ℝ 2 ↿fₜ` |

### Worked combination (W1, not the exercise's objects)

**W1: gauge invariance of B,** $\nabla \times (A - \nabla\chi) = \nabla \times A$. One `rw [fun_curl_sub, curl_of_grad_eq_zero]`
(R3, R5) turns the goal (first line) into the main goal followed by three side goals (R5's first, then R3's two):

```lean-goal
⊢ (curl fun x => f x - ∇ χ x) = curl f
⊢ (fun i => curl f i - 0 i) = curl f
⊢ ContDiff ℝ 2 χ
⊢ Differentiable ℝ f
⊢ Differentiable ℝ (∇ χ)
```

`· simp` closes the first (R7); `all_goals fun_prop` closes the rest (R8, R11). The exercise has the same shape
with six rewrites and five side goals.

---

## Traps

- Rewrite order matters. `fun_curl_neg` matches only after `fun_curl_sub` has split the difference, and
  `curl_of_grad_eq_zero` only after `fun_curl_neg` has turned `curl (-∇φ)` into `-curl (∇φ)`.
- `all_goals fun_prop` while the main goal (an equation) is still open fails: `fun_prop` errors on it, so
  `all_goals` fails. Close the main goal first with `· simp`.
- `fun_prop` does not lower smoothness for an arbitrary function: from `hφ : ContDiff ℝ ∞ φ` it cannot prove
  `ContDiff ℝ 2 φ`. In the exercise it works only because R9 and R10 start from `ContDiff ℝ ∞ V` themselves.
  Leave `hV` as it is; do not try to derive `ContDiff ℝ ∞` facts about `φ` or `A` by hand.
- `rw` leaves beta-redexes `(fun t x => …) t x` in the goal. They are harmless (later rewrites and `simp` see
  through them); `beta_reduce` removes them if you want to read the goal.
- `faradayLaw` is physlib's own proof of this statement and is banned.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `E` in terms of `φ`, `A` | `rw [ThreeDimension.electricField_eq_3D]` | R1 |
| `B` in terms of `A` | `rw [ThreeDimension.magneticField_eq_3D]` | R2 |
| `curl (f - g) → curl f - curl g` | `rw [fun_curl_sub]` (+2 side goals) | R3 |
| `curl (-f) → -curl f` | `rw [fun_curl_neg]` (+1 side goal) | R4 |
| `curl (∇ φ) → 0` | `rw [curl_of_grad_eq_zero]` (+1 side goal) | R5 |
| `∂ₜ (curl f) → curl (∂ₜ f)` | `rw [time_deriv_curl_commute]` (+1 side goal) | R6 |
| several rewrites at once | `rw [l₁, l₂, …]` (side goals of all of them pile up after the main goal) | R1–R6 |
| `-0 - X = -X` on functions | `· simp` | R7 |
| every `Differentiable`/`ContDiff` side goal | `all_goals fun_prop` | R8 (finds R9–R12) |
| see the state | infoview | |
