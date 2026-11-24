# H114 · The QHO ground state solves the Schrödinger equation: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`have`, `rw [h]`, `ring`, `rfl`) are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's one-variable derivative `deriv` for
functions `ℝ → ℂ` (product rule, chain rule, constants), `Complex.exp`, the cast `ℝ → ℂ` and how to move it
(`push_cast`), `field_simp`, and physlib's 1D harmonic oscillator (`HarmonicOscillator`, `ξ`, `ℏ`, the
eigenfunctions, the Schrödinger operator, the eigenvalues).

The plan, in physics notation: with $\xi = \sqrt{\hbar/(m\omega)}$ (the oscillator length) and
$\psi_0(x) = C\, e^{-x^2/(2\xi^2)}$, $C = 1/\sqrt{\sqrt\pi\,\xi}$,

$$\psi_0' = -\tfrac{x}{\xi^2}\psi_0,\qquad
\psi_0'' = -\tfrac{1}{\xi^2}\Bigl(1-\tfrac{x^2}{\xi^2}\Bigr)\psi_0,\qquad
H\psi_0 = \tfrac{\hbar^2}{2m}\Bigl(-\psi_0'' + \tfrac{x^2}{\xi^4}\psi_0\Bigr) = \tfrac{\hbar^2}{2m\xi^2}\psi_0
= \tfrac12\hbar\omega\,\psi_0 .$$

The three milestones are the three derivative facts; the main theorem is the last equation, and it closes
only after $\xi^2 = \hbar/(m\omega)$ is substituted.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp only`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℂ → Prop`, or `P : (ℝ → ℂ) → Prop` when the changing part is a whole
  function). The step changes only the part inside `P (…)`.
- `G : Prop` is an arbitrary goal; in the guide a hypothesis `k : … → G` consumes a new fact.
- Placeholders are written as Lean binders. `(f : ℝ → ℂ)` is any function from reals to complex numbers,
  `(Q : HarmonicOscillator)` any oscillator. Mathlib states the derivative lemmas over a field `𝕜` with a
  bracket `[NontriviallyNormedField 𝕜]` (a field with an absolute value that is not trivial): `ℝ` and `ℂ`
  meet it, and here `𝕜 = ℝ` (the variable) and values lie in `ℂ`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ`, `ℂ` | Mathlib's real and complex numbers |
| `↑x` (with `x : ℝ` in a complex expression) | the cast `Complex.ofReal x : ℂ`. Lean inserts it; `(x : ℂ)` is how you write it |
| `fun y => ↑y`, `Complex.ofReal` | the cast as a function `ℝ → ℂ`; the two are the same function, and after R2 with R3 the goal prints the second |
| `deriv fun x => t` | `deriv (fun x => t)`: Lean drops the parentheses around a `fun` that is the last argument |
| `-↑x ^ 2` | `-(↑x ^ 2)`, i.e. $-x^2$: `^` binds tighter than unary `-` |
| `1 / ↑√(√Real.pi * Q.ξ)` | the normalisation constant $C = 1/\sqrt{\sqrt\pi\,\xi}$, computed in `ℝ` and cast to `ℂ` |
| `Complex.exp z` | the complex exponential $e^z$ |
| `√x`, `Real.pi` | `Real.sqrt x` (a real number, `0` for `x < 0`) and $\pi$ |
| `deriv f x` | the derivative $f'(x)$ of `f : ℝ → ℂ` at `x` (a complex number). It is `0` if `f` is not differentiable at `x`, so every rule needs differentiability side goals |
| `deriv f` | the derivative as a function `ℝ → ℂ`; `deriv (deriv f) x` is $f''(x)$ |
| `DifferentiableAt ℝ f x` | `f` is differentiable at `x`, with `ℝ` as the scalar field (the variable is real) |
| `DifferentiableAt ℂ g z` | `g : ℂ → ℂ` is complex-differentiable at `z` (needed for `exp` in the chain rule) |
| `g ∘ u` | the composition `fun x => g (u x)` |
| `(fun x => t) x` | a function applied to an argument, not yet simplified (β-redex); R17 removes it |
| `HarmonicOscillator` | physlib's 1D oscillator: a structure with mass `Q.m`, frequency `Q.ω` and proofs `0 < Q.m`, `0 < Q.ω` |
| `Q.ξ` | the characteristic length $\xi = \sqrt{\hbar/(m\omega)}$ (a real number, `ξ_sq` gives its square) |
| `ℏ` | `Constants.ℏ`, the reduced Planck constant, of type `{x : ℝ // 0 < x}` (a positive real bundled with its proof: a *subtype*) |
| `↑ℏ`, `↑↑ℏ` | `ℏ` as a real number (`Subtype.val`), and that real cast on to `ℂ` |
| `Q.eigenfunction 0` | the ground state $\psi_0$ as a function `ℝ → ℂ` |
| `Q.schrodingerOperator ψ` | the function $x \mapsto -\frac{\hbar^2}{2m}\psi''(x) + \frac12 m\omega^2x^2\psi(x)$ (`ℝ → ℂ`) |
| `Q.eigenValue n` | the real number $(n + \frac12)\hbar\omega$; in the main goal it appears cast, `↑(Q.eigenValue 0)` |
| `↑0` inside `(↑0 + 1 / 2)` | the natural number `0` cast to `ℝ` (from `n : ℕ`); `push_cast` turns it into `0` |

---

## Part 1 · `deriv_gauss` (milestone 1)

Statement: $\frac{d}{dx} e^{-x^2/(2\xi^2)} = -\frac{x}{\xi^2} e^{-x^2/(2\xi^2)}$, as an equation in `ℂ` at
the point `x`. Plan: first the auxiliary fact $\frac{d}{dx}x^2 = 2x$ (R1–R4) and `hξ : ↑Q.ξ ≠ 0` (R5, R6);
then chain rule (R7–R9), evaluate (R10–R12), clear denominators (R13).

### The auxiliary fact `deriv (fun x => ↑x ^ 2) x = 2 * ↑x`

**R1 · `simp only [pow_two]`** changes the **goal**. The lemma is `pow_two : a ^ 2 = a * a`. `simp only`
rewrites inside `fun x => …`, where `rw` fails (the term mentions the bound variable). Placeholders:
`(P : (ℝ → ℂ) → Prop)`; the lemma holds in any monoid `{M : Type} [Monoid M]` (ℕ, ℝ, ℂ, matrices).

| Before | After |
|---|---|
| `⊢ P fun x => ↑x ^ 2` | `⊢ P fun x => ↑x * ↑x` |

**R2 · `rw [deriv_fun_mul hc hd]`** changes the **goal**: the product rule
`deriv (fun y => c y * d y) x = deriv c x * d x + c x * deriv d x`, valid when
`hc : DifferentiableAt ℝ c x` and `hd : DifferentiableAt ℝ d x`. Placeholders: `(c d : ℝ → ℂ) (x : ℝ)`. If you
do not have `hc hd` at hand, write `deriv_fun_mul (by fun_prop) (by fun_prop)` (R9).

| Before | After |
|---|---|
| `⊢ P (deriv (fun y => c y * d y) x)` | `⊢ P (deriv c x * d x + c x * deriv d x)` |

**R3 · `Complex.differentiableAt_ofReal`** **closes** `DifferentiableAt ℝ (fun y => ↑y) x` (statement:
`∀ {x : ℝ}, DifferentiableAt ℝ Complex.ofReal x`). Use it as both arguments of R2 when the factors are the cast.
Because its statement names `Complex.ofReal`, the goal after R2 shows the factors' derivatives as
`deriv Complex.ofReal x`, not `deriv (fun y => ↑y) x` (the same function).

**R4 · `simp only [Complex.deriv_ofReal]`** changes the **goal**. The lemma is `deriv Complex.ofReal x = 1`:
the cast has derivative 1. It also rewrites `deriv (fun y => ↑y) x`, the same function written as a `fun`
(milestone 3). Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (deriv Complex.ofReal x)` | `⊢ P 1` |

The auxiliary fact, step by step: after R1 the goal is `deriv (fun x => ↑x * ↑x) x = 2 * ↑x`; after R2 with
R3, R3 it is `deriv Complex.ofReal x * ↑x + ↑x * deriv Complex.ofReal x = 2 * ↑x`; after R4 it is
`1 * ↑x + ↑x * 1 = 2 * ↑x`, which `ring` closes.

### Nonzero facts for `field_simp`

**R5 · `have hc := Complex.ofReal_ne_zero.mpr hr`** changes the **context**. The lemma is
`Complex.ofReal_ne_zero : (↑z : ℂ) ≠ 0 ↔ z ≠ 0`; `.mpr` is its right-to-left direction. `field_simp` (R13) works
in `ℂ` and needs the fact in this cast form. Placeholders: `(r : ℝ) (hr : r ≠ 0)`.

| Before | After |
|---|---|
| `⊢ G` | `hc : ↑r ≠ 0 ⊢ G` |

**R6 · physlib's nonzero facts** change the **context**: `Q.ξ_ne_zero : Q.ξ ≠ 0`, `Q.m_ne_zero : Q.m ≠ 0`,
`Q.ω_ne_zero : Q.ω ≠ 0` and `ℏ_ne_zero : ↑ℏ ≠ 0`, all in `ℝ`. Feed them to R5:
`Complex.ofReal_ne_zero.mpr Q.ξ_ne_zero : ↑Q.ξ ≠ 0` in `ℂ`. Placeholders: `(Q : HarmonicOscillator)`.

| Before | After the four `have`s |
|---|---|
| `⊢ G` | `h1 : Q.ξ ≠ 0, h2 : Q.m ≠ 0, h3 : Q.ω ≠ 0, h4 : ↑ℏ ≠ 0 ⊢ G` |

### Chain rule

**R7 · `rw [show (fun x => g (u x)) = g ∘ u from rfl]`** changes the **goal**: a nested function is written as
a composition, the shape R8 needs. `show A = B from rfl` is a proof of `A = B` by unfolding (`∘` is defined
that way). In the exercise, write the inner function out in full. Placeholders: `(g : ℂ → ℂ) (u : ℝ → ℂ)`.

| Before | After |
|---|---|
| `⊢ P fun x => g (u x)` | `⊢ P (g ∘ u)` |

**R8 · `rw [deriv_comp x hg hu]`** changes the **goal**: the chain rule
`deriv (g ∘ u) x = deriv g (u x) * deriv u x`. The hypotheses are `hg : DifferentiableAt ℂ g (u x)` (the outer
function is differentiable over `ℂ`) and `hu : DifferentiableAt ℝ u x`; `deriv_comp _ (by fun_prop) (by fun_prop)`
lets Lean find `x` and proves both. Placeholders: `(g : ℂ → ℂ) (u : ℝ → ℂ) (x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (deriv (g ∘ u) x)` | `⊢ P (deriv g (u x) * deriv u x)` |

**R9 · `fun_prop`** **closes** a goal `DifferentiableAt 𝕜 f x` when `f` is built from differentiable pieces:
casts, `Complex.exp`, `+`, `-`, `*`, `^`, division by a constant. Examples it closes:

| Goal | |
|---|---|
| `⊢ DifferentiableAt ℝ (fun y => -↑y ^ 2 / c) x` | `c : ℂ`, any value (dividing by `0` is still differentiable) |
| `⊢ DifferentiableAt ℂ Complex.exp z` | the outer function of R8 |

### Evaluating the derivatives

**R10 · `simp only [Complex.deriv_exp]`** changes the **goal**. The lemma is `deriv Complex.exp = Complex.exp`.
Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (deriv Complex.exp z)` | `⊢ P (Complex.exp z)` |

**R11 · `simp only [deriv_div_const]`** changes the **goal**. The lemma is
`deriv (fun x => c x / d) x = deriv c x / d`. Placeholders: `(f : ℝ → ℂ) (c : ℂ) (x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (deriv (fun y => f y / c) x)` | `⊢ P (deriv f x / c)` |

**R12 · `simp only [deriv.fun_neg']`** changes the **goal**. The lemma is
`(deriv fun i => -f i) = fun x => -deriv f x`; `simp only` also β-reduces the result. Placeholders:
`(f : ℝ → ℂ) (x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (deriv (fun y => -f y) x)` | `⊢ P (-deriv f x)` |

R10, R11, R12 and your own `hsq` go into one `simp only [...]`: it evaluates
`deriv (fun x => -↑x ^ 2 / (2 * ↑Q.ξ ^ 2)) x` to `-(2 * ↑x) / (2 * ↑Q.ξ ^ 2)`.

**R13 · `field_simp`** changes the **goal**: it multiplies out every denominator whose `≠ 0` fact is in the
context (R5) and cancels common factors, often closing the goal or leaving a polynomial identity for `ring`.
The orientation of what remains is Lean's choice (`c * b`, not `b * c`). Placeholders: `(a b c : ℂ) (hc : c ≠ 0)`.

| Before | After |
|---|---|
| `⊢ a / c = b` | `⊢ a = c * b` |

---

## Part 2 · `deriv_ground` (milestone 2)

Statement: `deriv ψ₀ = fun x => (-↑x / ↑Q.ξ ^ 2) * ψ₀ x`, an equation of **functions**. Unfold `ψ₀` (R14),
go pointwise (R15), take out the constant (R16), β-reduce (R17), then milestone 1 and `ring`.

**R14 · `rw [eigenfunction_zero]`** changes the **goal**. The lemma is
`Q.eigenfunction 0 = fun x => 1 / ↑√(√Real.pi * Q.ξ) * Complex.exp (-↑x ^ 2 / (2 * ↑Q.ξ ^ 2))`. `rw` replaces
every `Q.eigenfunction 0`, including the one on the right side of the milestone (which then reads
`(fun x => …) x`, see R17). Placeholders: `(Q : HarmonicOscillator) (P : (ℝ → ℂ) → Prop)`.

| Before | After |
|---|---|
| `⊢ P (Q.eigenfunction 0)` | `⊢ P fun x => 1 / ↑√(√Real.pi * Q.ξ) * Complex.exp (-↑x ^ 2 / (2 * ↑Q.ξ ^ 2))` |

**R15 · `funext x`** changes the **goal and the context**: two functions are equal when they agree at every
point. Placeholders: `(f g : ℝ → ℂ)`.

| Before | After |
|---|---|
| `⊢ f = g` | `x : ℝ ⊢ f x = g x` |

**R16 · `rw [deriv_const_mul_field']`** changes the **goal**. The lemma is
`(deriv fun x => u * v x) = fun x => u * deriv v x`: a constant factor comes out of the derivative (no
differentiability needed). It is an equation of functions, so at a point it leaves a β-redex. Placeholders:
`(u : ℂ) (v : ℝ → ℂ) (x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (deriv (fun y => u * v y) x)` | `⊢ P ((fun x => u * deriv v x) x)` |

**R17 · `dsimp only`** changes the **goal**: β-reduction, `(fun y => t y) x` becomes `t x`. `simp only` with
no lemmas does the same. Placeholders: `(f : ℝ → ℂ) (x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((fun y => f y + 1) x)` | `⊢ P (f x + 1)` |

After R17, the goal contains `deriv (fun x => Complex.exp (-↑x ^ 2 / (2 * ↑Q.ξ ^ 2))) x`: `rw [deriv_gauss]`
(milestone 1) and `ring` finish.

---

## Part 3 · `deriv_deriv_ground` (milestone 3)

Statement: `deriv (deriv ψ₀) x = (-1 / ↑Q.ξ ^ 2) * (1 - ↑x ^ 2 / ↑Q.ξ ^ 2) * ψ₀ x`. No new entries: milestone 2
is an equation of functions, so `rw [deriv_ground]` replaces `deriv ψ₀` inside `deriv (deriv ψ₀)`. The
product rule R2 (side goals R9) then produces a new `deriv ψ₀ x`; a second `rw [deriv_ground]` replaces that
one too. Then R11, R12, R4 in one `simp only` evaluate `deriv (fun x => -↑x / ↑Q.ξ ^ 2) x = -1 / ↑Q.ξ ^ 2`, and
R13 + `ring` finish (with `hξ` from R5, R6 in the context).

---

## Part 4 · `ground_state_tise`

Statement: `Q.schrodingerOperator ψ₀ x = ↑(Q.eigenValue 0) * ψ₀ x` in `ℂ`. Expand both sides (R18, R17, R19),
insert milestone 3, then do the algebra. The algebra needs $\xi^2 = \hbar/(m\omega)$ in `ℂ` (R20–R22).

**R18 · `rw [schrodingerOperator_eq_ξ]`** changes the **goal**. The lemma is
`Q.schrodingerOperator ψ = fun x => ↑↑ℏ ^ 2 / (2 * ↑Q.m) * (-deriv (deriv ψ) x + (1 / ↑Q.ξ ^ 2) ^ 2 * ↑x ^ 2 * ψ x)`,
the operator rewritten with `ξ`. At a point it leaves a β-redex (R17). Placeholders:
`(ψ : ℝ → ℂ) (Q : HarmonicOscillator) (P : (ℝ → ℂ) → Prop)`.

| Before | After |
|---|---|
| `⊢ P (Q.schrodingerOperator ψ)` | `⊢ P fun x => ↑↑ℏ ^ 2 / (2 * ↑Q.m) * (-deriv (deriv ψ) x + (1 / ↑Q.ξ ^ 2) ^ 2 * ↑x ^ 2 * ψ x)` |

**R19 · `rw [eigenValue]`** changes the **goal**: it unfolds the definition
`Q.eigenValue n = (↑n + 1 / 2) * ↑ℏ * Q.ω` (in `ℝ`). Placeholders: `(n : ℕ) (Q : HarmonicOscillator) (P : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (Q.eigenValue n)` | `⊢ P ((↑n + 1 / 2) * ↑ℏ * Q.ω)` |

In the main goal this sits inside a cast: `↑((↑0 + 1 / 2) * ↑ℏ * Q.ω)`. `push_cast` (R22) turns it into
`(0 + 1 / 2) * ↑↑ℏ * ↑Q.ω`.

### The fact `hsq : (Q.ξ : ℂ) ^ 2 = ℏ / (Q.m * Q.ω)`

`ξ_sq` is an equation in `ℝ`, the goal is in `ℂ`. Move the cast outward (R20), rewrite in `ℝ` (R21), move the
casts back inward (R22), then `rfl` (Traps).

**R20 · `rw [← Complex.ofReal_pow]`** changes the **goal**. The lemma is `Complex.ofReal_pow : ↑(r ^ n) = ↑r ^ n`;
right to left it moves `^` inside the cast. Placeholders: `(r : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (↑r ^ n)` | `⊢ P ↑(r ^ n)` |

**R21 · `rw [ξ_sq]`** changes the **goal**. The lemma is `Q.ξ ^ 2 = ↑ℏ / (Q.m * Q.ω)` in `ℝ`, so it matches
`Q.ξ ^ 2` only under a cast `↑(Q.ξ ^ 2)`, never `↑Q.ξ ^ 2` (do R20 first). Placeholders:
`(Q : HarmonicOscillator) (P : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (Q.ξ ^ 2)` | `⊢ P (↑ℏ / (Q.m * Q.ω))` |

**R22 · `push_cast`** changes the **goal**: it pushes every cast `↑` inward onto the atoms (variables,
numerals): `↑(a / (b * c))` becomes `↑a / (↑b * ↑c)`, `↑(0 : ℕ)` becomes `0`. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ↑(a / (b * c))` | `⊢ P (↑a / (↑b * ↑c))` |

### Worked combinations (W1–W4, on objects that are not the exercise's)

**W1: chain rule on $e^{3x}$.** R7, R8 (side goals R9), then one `simp only` with R10, R16, R4, then `ring`:

```lean-goal
⊢ deriv (fun y => Complex.exp (3 * ↑y)) x = 3 * Complex.exp (3 * ↑x)
⊢ deriv (Complex.exp ∘ fun y => 3 * ↑y) x = 3 * Complex.exp (3 * ↑x)
⊢ deriv Complex.exp (3 * ↑x) * deriv (fun y => 3 * ↑y) x = 3 * Complex.exp (3 * ↑x)
⊢ Complex.exp (3 * ↑x) * (3 * 1) = 3 * Complex.exp (3 * ↑x)
```

**W2: peeling `/ c` and `-` off a derivative.** `simp only [deriv_div_const, deriv.fun_neg', Complex.deriv_ofReal]`
closes `deriv (fun y => -↑y / c) x = -1 / c` (R11, R12, R4). This is step 3 of milestone 3 with `c` for `↑Q.ξ ^ 2`.

**W3: a real equation moved into `ℂ`.** From `h : r ^ 2 = a / b` in `ℝ`: R20, `rw [h]`, R22, then `rfl`:

```lean-goal
⊢ ↑r ^ 2 = ↑a / ↑b
⊢ ↑(r ^ 2) = ↑a / ↑b
⊢ ↑(a / b) = ↑a / ↑b
⊢ ↑a / ↑b = ↑a / ↑b
```

**W4: product rule, then clear denominators.** With `hc : c ≠ 0`: R2 (side goals R9), one `simp only` with
R11, R12, R4, then R13 and `ring`:

```lean-goal
⊢ deriv (fun y => -↑y / c * f y) x * c = -f x - ↑x * deriv f x
⊢ (deriv (fun y => -↑y / c) x * f x + -↑x / c * deriv f x) * c = -f x - ↑x * deriv f x
⊢ (-1 / c * f x + -↑x / c * deriv f x) * c = -f x - ↑x * deriv f x
⊢ -f x + -(↑x * deriv f x) = -f x - ↑x * deriv f x
```

---

## Traps

- **`push_cast` can leave a goal whose two sides print identically** (W3, and `hsq`): the casts were built
  by different routes and `push_cast` does not notice they agree. Close it with `rfl`.
- **Rewrite with `hsq` before `field_simp`.** `field_simp` combines `↑Q.ξ ^ 2 * ↑Q.ξ ^ 2` into `↑Q.ξ ^ 4`,
  which `hsq` (about `↑Q.ξ ^ 2`) no longer matches.
- **`push_cast` the main goal before `field_simp`.** Otherwise the right side keeps the eigenvalue as one
  opaque cast `↑((↑0 + 1 / 2) * ↑ℏ * Q.ω)`, which `field_simp` and `ring` cannot relate to the `↑↑ℏ`, `↑Q.m`,
  `↑Q.ω` on the left. Whether `push_cast` comes before or after `rw [hsq]` does not matter.
- **`ξ_sq` lives in `ℝ`.** The goal has `↑Q.ξ ^ 2` in `ℂ`; `rw [ξ_sq]` fails on it. Use R20 first, or prove
  `hsq` once.
- **`field_simp` needs `≠ 0` facts in `ℂ`:** `Complex.ofReal_ne_zero.mpr Q.ξ_ne_zero : ↑Q.ξ ≠ 0` (R5, R6), not
  `Q.ξ_ne_zero : Q.ξ ≠ 0`. In the main proof it needs `↑Q.m`, `↑Q.ω` and `↑↑ℏ` nonzero.
- **`deriv_comp` matches only `g ∘ u`.** A goal `deriv (fun x => Complex.exp (…)) x` must first be restated with
  R7; write the inner function out exactly as it appears in the goal, including the type ascription `x : ℝ`.
- **`rw` cannot rewrite under `fun x => …`** when the pattern mentions the bound `x`: it reports that it did
  not find the pattern. `simp only [lemma]` can (R1).
- **Function equations leave `(fun x => …) x`** after `rw` at a point (R14, R16, R18); `dsimp only` or `simp only`
  removes it (R17). Do that before `rw [deriv_gauss]`: inside the unreduced `(fun x => …) x` the pattern
  mentions the bound `x`, so `rw` does not find it.
- **`deriv f x` is `0` where `f` is not differentiable**, so every rule here (R2, R8) has differentiability side
  goals. `fun_prop` (R9) proves them; give it to `rw` as `(by fun_prop)`.
- **Banned:** physlib already proves these derivatives (`deriv_eigenfunction_zero`, …) and the whole statement
  (`schrodingerOperator_eigenfunction`); the `BANNED:` line forbids them, and search tactics (`exact?`, …).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `a ^ 2 → a * a` under a `fun` | `simp only [pow_two]` | R1 |
| product rule | `rw [deriv_fun_mul (by fun_prop) (by fun_prop)]` | R2, R9 |
| the cast is differentiable | `Complex.differentiableAt_ofReal` | R3 |
| `deriv (fun y => ↑y) x → 1` | `simp only [Complex.deriv_ofReal]` | R4 |
| `↑r ≠ 0` in `ℂ` | `have h := Complex.ofReal_ne_zero.mpr Q.ξ_ne_zero` | R5, R6 |
| nested function → composition | `rw [show (fun x : ℝ => g (u x)) = g ∘ (fun x : ℝ => u x) from rfl]` | R7 |
| chain rule | `rw [deriv_comp _ (by fun_prop) (by fun_prop)]` | R8, R9 |
| `deriv exp`, `/ c`, `-` | `simp only [Complex.deriv_exp, deriv_div_const, deriv.fun_neg']` | R10–R12 |
| clear denominators | `field_simp` (then `ring`) | R13 |
| unfold `ψ₀` | `rw [eigenfunction_zero]` | R14 |
| function equation → pointwise | `funext x` | R15 |
| constant out of `deriv` | `rw [deriv_const_mul_field']` | R16 |
| remove `(fun x => …) x` | `dsimp only` / `simp only` | R17 |
| expand the Schrödinger operator | `rw [schrodingerOperator_eq_ξ]` | R18 |
| unfold the eigenvalue | `rw [eigenValue]` | R19 |
| `↑r ^ n → ↑(r ^ n)` | `rw [← Complex.ofReal_pow]` | R20 |
| `ξ ^ 2 → ℏ / (m ω)` (in `ℝ`) | `rw [ξ_sq]` | R21 |
| casts inward | `push_cast` | R22 |
| identical-looking sides left open | `rfl` | Traps |
