# E075 · fun_prop: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's predicates `Continuous`,
`Differentiable` and `ContinuousAt` on real functions, the real functions `Real.exp`, `Real.sin`,
`Real.cos`, `Real.log`, and the tactic `fun_prop`, which proves such predicates for a function built
from pieces. Each hole is one `fun_prop` call; the other entries are the lemmas it applies, so you can
do one step by hand and understand what `fun_prop` is doing when it fails.

## How to read an entry

Each entry is one tactic or one lemma used with `apply`/`exact`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `u v : ℝ → ℝ` are arbitrary real functions; `c : ℝ` a real constant; `n : ℕ` a natural exponent; `a : ℝ`
  a point.
- The library lemmas are stated for any topological space (for `Continuous`) or any normed space over a
  field `𝕜` (for `Differentiable`). In this exercise every function is `ℝ → ℝ`, so the entries state them
  on `ℝ` only.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers `Real` (typed `\R`) |
| `fun x => c * x ^ n + x` | the function $x \mapsto c x^n + x$; `x ^ n` with `n : ℕ` is the power $x^n$ |
| `Continuous f` | $f$ is continuous everywhere: $\forall a\, \forall \varepsilon > 0\, \exists \delta > 0\, \forall x,\ \lvert x - a\rvert < \delta \to \lvert f x - f a\rvert < \varepsilon$ |
| `ContinuousAt f a` | $f$ is continuous at the single point $a$: $f x \to f a$ as $x \to a$ |
| `Differentiable ℝ f` | $f$ has a derivative at every point. The first argument is the field (`ℝ`) the derivative is linear over; it comes **before** the function |
| `Real.exp`, `Real.sin`, `Real.cos` | $e^x$, $\sin x$, $\cos x$ on `ℝ`; continuous and differentiable everywhere |
| `Real.log` | the natural logarithm, made total: Lean defines `Real.log x` $= \ln\lvert x\rvert$ for $x \neq 0$ and `Real.log 0 = 0`, so it is continuous at every `a ≠ 0` but not at `0` |
| `Continuous Real.exp` | Lean prints `fun x => Real.exp x` in this shorter form (η-reduced) |
| `Continuous fun x => …` | `Continuous (fun x => …)`: Lean drops the parentheses around a final `fun` argument |
| `Continuous (HMul.hMul 3)` | `Continuous (fun x => 3 * x)`, printed in the same shorter form (`HMul.hMul 3` is "multiply by 3"); `apply Continuous.mul` (R3) still splits it |
| `fun b => 3`, `fun b => b` | the constant function 3 and the identity; the bound variable's name (`b`, `x`) does not matter |
| `f * g`, `g ∘ f` (in lemma statements) | the pointwise product `fun x => f x * g x` and the composition `fun x => g (f x)` |
| `case hf`, `case hg`, `case ha`, `case hb` | the names `apply` gives the goals it leaves: they are the lemma's hypothesis names |
| `case refine_1` | the name `refine` gives the goal for its first `?_` |

---

## Part 1 · `cont_poly`

Statement: $x \mapsto x^2 + 3x + 1$ is continuous on `ℝ`. A polynomial is built from `x` and constants by
`+`, `*` and `^`; each of those has a continuity lemma, and `fun_prop` chains them.

**R1 · `fun_prop`** **closes** a goal `Continuous (fun x => …)` whose body is built from `+`, `*`, `^`,
constants and `x`. It splits the body at its outermost operation (R2, R3), repeats on each piece, and ends
each branch with a basic lemma (R4–R7). Placeholders: `(c : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ Continuous fun x => c * x ^ n + x` | no goals |

**R2 · `apply Continuous.add`** changes the **goal list**. The lemma is
`Continuous.add : Continuous f → Continuous g → Continuous (f + g)`, where `f + g` is `fun x => f x + g x`.
Placeholders: `(u v : ℝ → ℝ)`.

| Before | After |
|---|---|
| `⊢ Continuous fun x => u x + v x` | `⊢ Continuous u`, `⊢ Continuous v` |

**R3 · `apply Continuous.mul`** changes the **goal list**: the same for a product,
`Continuous.mul : Continuous f → Continuous g → Continuous (f * g)`. Placeholders: `(u v : ℝ → ℝ)`.

| Before | After |
|---|---|
| `⊢ Continuous fun x => u x * v x` | `⊢ Continuous u`, `⊢ Continuous v` |

**R4 · `exact continuous_const`** **closes** the goal for a constant function. The lemma is
`continuous_const : Continuous (fun x => c)`. Placeholders: `(c : ℝ)`.

| Before | After |
|---|---|
| `c : ℝ ⊢ Continuous fun x => c` | no goals |

**R5 · `exact continuous_id`** **closes** the goal for `fun x => x`. The lemma is stated as
`Continuous id`, and `id` unfolds to `fun x => x`, so `exact` accepts it.

| Before | After |
|---|---|
| `⊢ Continuous fun x => x` | no goals |

**R6 · `exact continuous_pow n`** **closes** the goal for a power. The lemma is
`continuous_pow (n : ℕ) : Continuous (fun x => x ^ n)`. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ Continuous fun x => x ^ n` | no goals |

**W1: a polynomial by hand.** On `fun x => 5 * x ^ 3 + x`, R2 leaves two goals; R3 splits the first, R4 and
R6 close its pieces, R5 closes the second:

```lean-goal
⊢ Continuous fun x => 5 * x ^ 3 + x
⊢ Continuous fun x => 5 * x ^ 3
⊢ Continuous fun x => x
```

---

## Part 2 · `cont_exp_sin`

Statement: $x \mapsto e^x \sin x$ is continuous. A product (R3) of two named functions, each with a
lemma that `fun_prop` knows.

**R7 · `Real.continuous_exp`, `Real.continuous_sin`, `Real.continuous_cos`** **close** the goals
`Continuous Real.exp`, `Continuous Real.sin`, `Continuous Real.cos`. Mathlib tags these lemmas so that
`fun_prop` finds them by itself; with an outer function applied to an inner one (`Real.exp (2 * x)`) it
combines them with the composition lemma (R13).

| Before | After |
|---|---|
| `⊢ Continuous Real.exp ∧ Continuous Real.sin ∧ Continuous Real.cos` | no goals |

---

## Part 3 · `diff_cos_exp`

Statement: $x \mapsto \cos(x^2)\, e^{2x}$ is differentiable on `ℝ`. Same shape as Part 2, with a chain rule
for each factor: $\cos$ after $x^2$, and $\exp$ after $2x$.

**R8 · `fun_prop` on `Differentiable ℝ f`** **closes** the goal with the differentiability lemmas
(R9–R11) instead of the continuity ones. Write the field first: `Differentiable ℝ f`.

| Before | After |
|---|---|
| `⊢ Differentiable ℝ fun x => Real.sin x * x ^ 3` | no goals |

**R9 · `apply Differentiable.mul`** changes the **goal list**: the product rule as a fact about existence,
`Differentiable 𝕜 a → Differentiable 𝕜 b → Differentiable 𝕜 (a * b)`. The goals are named after the
lemma's arguments `a`, `b`. Placeholders: `(u v : ℝ → ℝ)`.

| Before | After |
|---|---|
| `⊢ Differentiable ℝ fun x => u x * v x` | `⊢ Differentiable ℝ u`, `⊢ Differentiable ℝ v` |

**R10 · `apply Differentiable.comp`** changes the **goal list**: the chain rule,
`Differentiable.comp : Differentiable 𝕜 g → Differentiable 𝕜 f → Differentiable 𝕜 (g ∘ f)`, where
`g ∘ f` is `fun x => g (f x)`. The **outer** function's goal comes first. Placeholders: `(u v : ℝ → ℝ)`.

| Before | After |
|---|---|
| `⊢ Differentiable ℝ fun x => v (u x)` | `⊢ Differentiable ℝ v`, `⊢ Differentiable ℝ u` |

**R11 · `Real.differentiable_exp`, `Real.differentiable_cos`, `differentiable_pow n`** **close** the basic
goals; also `Real.differentiable_sin`, `differentiable_const c` (for `fun x => c`) and `differentiable_id`
(for `fun x => x`). Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ Differentiable ℝ Real.exp ∧ Differentiable ℝ Real.cos ∧ Differentiable ℝ fun x => x ^ n` | no goals |

**W2: the chain rule by hand.** On `fun x => Real.sin (x ^ 3)`, name the outer function in R10
(`refine Differentiable.comp (g := Real.sin) ?_ ?_`), then close both goals with R11:

```lean-goal
⊢ Differentiable ℝ fun x => Real.sin (x ^ 3)
⊢ Differentiable ℝ Real.sin
⊢ Differentiable ℝ fun x => x ^ 3
```

---

## Part 4 · `cont_comb`

Statement: for continuous `f g : ℝ → ℝ` (hypotheses `hf`, `hg`), $x \mapsto f(x)\,g(x) + f(g(x))$ is
continuous. `f` and `g` are unknown, so no tagged lemma covers them; `fun_prop` uses the hypotheses in
the context instead, together with R2, R3 and composition (R13).

**R12 · `fun_prop` with a hypothesis** **closes** the goal: a hypothesis `hu : Continuous u` in the context
makes `u` a known piece, usable alone (`u x`) or inside a composition (`Real.exp (u x)`).
Placeholders: `(u : ℝ → ℝ) (hu : Continuous u)`.

| Before | After |
|---|---|
| `hu : Continuous u ⊢ Continuous fun x => Real.exp (u x) + u x` | no goals |

**R13 · `apply Continuous.comp`** changes the **goal list**. The lemma is
`Continuous.comp : Continuous g → Continuous f → Continuous (g ∘ f)`, where `g ∘ f` is `fun x => g (f x)`;
the outer function's goal comes first. Placeholders: `(u v : ℝ → ℝ)`.

| Before | After |
|---|---|
| `⊢ Continuous fun x => v (u x)` | `hv : Continuous v ⊢ Continuous v`, `hu : Continuous u ⊢ Continuous u` |

---

## Part 5 · `contAt_log_sin`

Statement: $y \mapsto \log y \cdot \sin y$ is continuous at the point $2$. `Real.log` is continuous only at
nonzero points, so one piece comes with a side goal, `(2 : ℝ) ≠ 0`, which `fun_prop` cannot prove alone.

**R14 · `apply ContinuousAt.mul`** changes the **goal list**: the product lemma at one point,
`ContinuousAt f x → ContinuousAt g x → ContinuousAt (f * g) x`. Placeholders: `(u v : ℝ → ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ ContinuousAt (fun x => u x * v x) a` | `⊢ ContinuousAt u a`, `⊢ ContinuousAt v a` |

**R15 · `apply Continuous.continuousAt`** changes the **goal**: a function continuous everywhere is
continuous at `a`, `Continuous.continuousAt : Continuous f → ContinuousAt f x`. Use it for `sin`, `cos`,
`exp`, then R7. Placeholders: `(u : ℝ → ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ ContinuousAt u a` | `⊢ Continuous u` |

**R16 · `apply Real.continuousAt_log`** changes the **goal**: the lemma is
`Real.continuousAt_log : x ≠ 0 → ContinuousAt Real.log x`, so what is left is the side condition.
Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ ContinuousAt Real.log a` | `⊢ a ≠ 0` |

**R17 · `fun_prop (disch := norm_num)`** **closes** the goal. `disch` ("discharger") is the tactic
`fun_prop` runs on every side condition it meets, such as the `x ≠ 0` of `Real.log`. Without it, `fun_prop`
fails with the message `Failed to prove necessary assumption 5 ≠ 0 when applying theorem
ContinuousAt.log`, which names the side goal to discharge. `norm_num` proves numeral facts such as
`5 ≠ 0` (TACTIC_STATES, "Closing").

| Before | After |
|---|---|
| `⊢ ContinuousAt (fun x => Real.log x + x) 5` | no goals |

**W3: continuity at a point by hand.** On `fun x => Real.log x * Real.cos x` at `3`: R14 splits the
product; R16 turns the `log` goal into `3 ≠ 0`, which `norm_num` closes; R15 then R7 close the `cos` goal.

```lean-goal
⊢ ContinuousAt (fun x => Real.log x * Real.cos x) 3
⊢ ContinuousAt Real.log 3
⊢ ContinuousAt Real.cos 3
```

---

## Traps

- The `continuity` tactic is banned here: use `fun_prop`.
- `Differentiable ℝ f`, not `Differentiable f ℝ`: the field comes first.
- `fun_prop` on `Continuous (fun x => Real.log x)` fails: it needs `∀ x, x ≠ 0`, which is false. `Real.log`
  is continuous only at points `a ≠ 0` (`ContinuousAt`), and plain `fun_prop` cannot prove even `2 ≠ 0`:
  pass a discharger (R17). Read its error message: it names the side goal.
- `apply Differentiable.comp` on `fun x => Real.sin (x ^ 3)` unfolds `Real.sin` into its definition through
  `Complex.sin` and leaves goals about `Complex.re`. Name the outer function: `(g := Real.sin)` (W2).
  `fun_prop` never does this.
- By hand, `apply Continuous.add` on `x ^ 2 + 3 * x + 1` leaves `Continuous (HMul.hMul 3)` for the `3 * x`
  piece: that is `fun x => 3 * x` printed short, and `apply Continuous.mul` (R3) splits it into
  `fun b => 3` (R4) and `fun b => b` (R5).
- `apply` lists the lemma's goals in its own order: for composition (R10, R13) the outer function comes
  first.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `Continuous (fun x => …)` from `+ * ^`, constants, `exp sin cos` | `fun_prop` | R1, R7 |
| the same with `hf : Continuous f` in context | `fun_prop` | R12 |
| `Differentiable ℝ (fun x => …)` | `fun_prop` | R8 |
| `ContinuousAt f a` with a side condition like `a ≠ 0` | `fun_prop (disch := norm_num)` | R17 |
| split `+` / `*` by hand | `apply Continuous.add` / `apply Continuous.mul` | R2, R3 |
| constant / `x` / `x ^ n` | `continuous_const` / `continuous_id` / `continuous_pow n` | R4–R6 |
| product, chain rule for `Differentiable` | `apply Differentiable.mul` / `refine Differentiable.comp (g := …) ?_ ?_` | R9, R10 |
| basic differentiable functions | `Real.differentiable_exp`, `differentiable_pow n`, … | R11 |
| composition `fun x => v (u x)` | `apply Continuous.comp` | R13 |
| at one point | `apply ContinuousAt.mul`, `apply Continuous.continuousAt` | R14, R15 |
| `log` at `a` | `apply Real.continuousAt_log` → `⊢ a ≠ 0` | R16 |
| see the state | infoview | |
