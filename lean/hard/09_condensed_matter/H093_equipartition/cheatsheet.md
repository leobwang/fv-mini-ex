# H093 · Equipartition: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `rw`, `simp`, `have`, `ring`, `norm_num`,
anonymous functions `fun x => …`. **New here:** Mathlib's Lebesgue integral on `ℝ` (`∫ x, f x`, integrals over
`(0, ∞)`), the Gaussian integral, the Gamma function, real powers `x ^ (y : ℝ)` (`rpow`) and `Real.sqrt`;
physlib's `CanonicalEnsemble` on a continuous state space, `Temperature` and Boltzmann's constant `kB`; the
tactics `positivity`, `field_simp`, `ring_nf`. (`funext` and `show` are from E021–E022; here they act on
integrands and on the measure.)

**The physics, in symbols.** One classical degree of freedom: position `x ∈ ℝ`, energy $E(x) = \kappa x^2/2$
with stiffness $\kappa > 0$. At temperature $T > 0$ put $\beta = 1/(k_B T)$ ($k_B$ Boltzmann's constant) and
$a = \beta\kappa/2 > 0$, so the Boltzmann weight is the Gaussian $e^{-\beta E(x)} = e^{-a x^2}$. The mean energy
is
$$\langle E\rangle = \frac{\int E\,e^{-\beta E}\,dx}{\int e^{-\beta E}\,dx}
= \frac{\kappa}{2}\cdot\frac{\int x^2 e^{-a x^2}\,dx}{\int e^{-a x^2}\,dx}.$$
The second moment: the integrand is even, so $\int_{\mathbb R} x^2 e^{-ax^2}dx = 2\int_0^\infty x^2 e^{-ax^2}dx$,
and the Gamma formula $\int_0^\infty x^q e^{-b x^p}dx = b^{-(q+1)/p}\,\tfrac1p\,\Gamma\!\big(\tfrac{q+1}{p}\big)$
(here $p = q = 2$, $b = a$) gives $a^{-3/2}\,\Gamma(3/2) = a^{-3/2}\sqrt\pi/2$, using $\Gamma(s+1) = s\Gamma(s)$ and
$\Gamma(1/2) = \sqrt\pi$. The Gaussian integral is $\int e^{-a x^2}dx = \sqrt{\pi/a}$. So
$\int x^2 e^{-ax^2} = \tfrac{1}{2a}\int e^{-ax^2}$ (milestone `moment2`), and
$\langle E\rangle = \tfrac{\kappa}{2}\cdot\tfrac{1}{2a} = \tfrac{1}{2\beta} = \tfrac{k_B T}{2}$: each quadratic
degree of freedom carries $k_B T/2$.

**How physlib encodes it.** `CanonicalEnsemble ι` is a structure: a type of microstates `ι` with a σ-algebra
(`[MeasurableSpace ι]`), `energy : ι → ℝ`, `dof : ℕ` and `phaseSpaceunit : ℝ` (they make the partition function
dimensionless; they cancel in `⟨E⟩`), a proof `energy_measurable` that `energy` is measurable (the spec proves
it with `fun_prop`, a tactic that proves measurability or continuity of a formula piece by piece; you never call
it), and a measure `μ` on `ι`. A field left out of a `where` definition takes its default: `phaseSpaceunit := 1`
(with its proof `hPos : 0 < phaseSpaceunit`) and `μ := volume` (Lebesgue measure on `ℝ`).
`𝓒.meanEnergy T` is defined as an integral against the Boltzmann probability measure; R19 turns it into the
ratio above. `Temperature` is a structure with one field `val : ℝ≥0`; `T.toReal = ↑T.val`, and
`T.β : ℝ≥0` is `1 / (kB * T.toReal)`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before and
after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` with `g : … → G` is an arbitrary goal for entries that only add a fact.
- Placeholders are written as Lean binders. All of them are real numbers or real functions here, as in the
  exercise. `{ι : Type} [MeasurableSpace ι]` is any type of microstates with a σ-algebra (the bracket is a
  *type class* requirement; `ℝ` meets it with the Borel sets).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `∫ (x : ℝ), f x` | the Lebesgue integral of `f` over all of `ℝ` (`MeasureTheory.integral volume f`). It is `0` when `f` is not integrable |
| `∫ (x : ℝ), f x ∂μ` | the same against the measure `μ`; no `∂…` means `∂volume` |
| `∫ (x : ℝ) in Set.Ioi 0, f x` | the integral over the half-line `(0, ∞)` (`Set.Ioi 0 = {x \| 0 < x}`, "interval open, to infinity") |
| `rexp x` | `Real.exp x`, the real exponential |
| `√x`, `π` | `Real.sqrt x` (it is `0` for `x < 0`), `Real.pi` |
| `Gamma s` | `Real.Gamma s`, Euler's Γ function: `Γ(s) = ∫₀^∞ t^(s-1) e^(-t) dt` for `s > 0` |
| `x ^ 2` | EITHER the natural power `x ^ (2 : ℕ)` (repeated multiplication) OR the real power `x ^ (2 : ℝ)` (`Real.rpow`, `= exp (2 log x)` for `x > 0`). They print the same; R2 converts |
| `a ^ (-(2 + 1) / 2)`, `a ^ (1 / 2)` | real powers: the exponent is a real number |
| `\|x\|` | absolute value |
| `(harmonic κ).energy x`, `(harmonic κ).μ` | the fields of the exercise's ensemble; `simp only [harmonic]` (R17) or `show` (R22) unfolds them |
| `𝓒.meanEnergy T` | the mean energy `⟨E⟩` at temperature `T` (R19) |
| `ℝ≥0` | `NNReal`, the nonnegative reals: a real number bundled with a proof that it is `≥ 0` |
| `T.val`, `T.β` | the temperature and `β = 1/(k_B T)`, both in `ℝ≥0` |
| `↑T.β` | `(T.β : ℝ)`, the cast `ℝ≥0 → ℝ` (it forgets the proof) |
| `T.toReal` | `↑T.val`, the temperature as a real number |
| `kB` | `Constants.kB`, Boltzmann's constant, a positive real (R31) |
| `inst✝ : MeasurableSpace ι` | an unnamed instance argument from `[MeasurableSpace ι]` |
| `(fun x => B x) x` | a function applied to `x`, not yet simplified; Lean treats it as `B x` |

---

## Part 1 · `moment2` (milestone)

Statement: for `0 < a`, `∫ x, x ^ 2 * rexp (-a * x ^ 2) = 1 / (2 * a) * ∫ x, rexp (-a * x ^ 2)` (natural
powers). Fold the even integrand onto `(0, ∞)`, apply the Gamma formula and the Gaussian integral, then evaluate
`Γ(3/2)` and `a ^ (-3/2)` as two `have`s and clear the denominators.

### Folding onto the half-line

**R1 · `rw [← integral_comp_abs]`** changes the **goal**. The lemma is
`integral_comp_abs : ∫ x, f |x| = 2 * ∫ x in Set.Ioi 0, f x` (for every `f : ℝ → ℝ`); right to left it turns the
half-line integral back into an integral of `f |x|` over `ℝ`. Placeholders: `(f : ℝ → ℝ)`. In the exercise
write the function explicitly, `rw [← integral_comp_abs (f := fun x : ℝ => …)]` (a *named argument*: `f := …`
fills the implicit argument `f`), and state the half-line side with real powers so that R4 matches it later.

Before, then after (a block, since `|x|` cannot sit in a table cell):

```lean-goal
⊢ P (2 * ∫ (x : ℝ) in Set.Ioi 0, f x)
⊢ P (∫ (x : ℝ), f |x|)
```

**R2 · `Real.rpow_two`** changes the **goal**: `x ^ (2 : ℝ) = x ^ 2`, real power to natural power. Both sides
print as `x ^ 2`, so the table looks like nothing happened; the infoview's hover shows `HPow ℝ ℝ ℝ` before and
`HPow ℝ ℕ ℝ` after. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (x ^ 2)` (real power) | `⊢ P (x ^ 2)` (natural power) |

**R3 · `sq_abs`** changes the **goal**: `|a| ^ 2 = a ^ 2`. Placeholders: `(a : ℝ)`.

Before, then after:

```lean-goal
⊢ P (|a| ^ 2)
⊢ P (a ^ 2)
```

R1 then `simp only [Real.rpow_two, sq_abs]` proves the folding fact; W1 does it for the Gaussian itself:

```lean-goal
⊢ ∫ (x : ℝ), rexp (-b * x ^ 2) = 2 * ∫ (x : ℝ) in Set.Ioi 0, rexp (-b * x ^ 2)
⊢ ∫ (x : ℝ), rexp (-b * x ^ 2) = ∫ (x : ℝ), rexp (-b * |x| ^ 2)
```

The second line has a natural power on the left and a real power on the right; `simp only` makes them the same
and closes the goal.

### Gamma formula and Gaussian

**R4 · `rw [integral_rpow_mul_exp_neg_mul_rpow hp hq hb]`** changes the **goal**. The lemma is
`0 < p → -1 < q → 0 < b → ∫ x in Set.Ioi 0, x ^ q * rexp (-b * x ^ p) = b ^ (-(q + 1) / p) * (1 / p) * Gamma ((q + 1) / p)`,
with real powers throughout. In the exercise `p = q = 2`: pass `(by norm_num) (by norm_num) ha`.
Placeholders: `(p q b : ℝ) (hp : 0 < p) (hq : -1 < q) (hb : 0 < b)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ) in Set.Ioi 0, x ^ q * rexp (-b * x ^ p))` | `⊢ P (b ^ (-(q + 1) / p) * (1 / p) * Gamma ((q + 1) / p))` |

**R5 · `rw [integral_gaussian]`** changes the **goal**. The lemma is
`integral_gaussian b : ∫ x, rexp (-b * x ^ 2) = √(π / b)` with a natural power `^ 2`. It has no hypothesis on
`b`: for `b ≤ 0` both sides are `0` by Mathlib's conventions. Placeholders: `(b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ), rexp (-b * x ^ 2))` | `⊢ P √(π / b)` |

### Evaluating `Γ(3/2)`

**R6 · `rw [show A = B by norm_num]`** changes the **goal**: `show A = B by norm_num` is a proof of `A = B`
made on the spot, and `rw` uses it. Use it to put a numeral expression into the form a lemma needs, here
`(2 + 1) / 2` → `1 / 2 + 1` for R7. Write the type, `((2 : ℝ) + 1) / 2`, or the numerals default to `ℕ`.
Placeholders: `(f : ℝ → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (f ((4 + 1) / 2))` | `⊢ P (f (3 / 2 + 1))` |

**R7 · `rw [Real.Gamma_add_one hs]`** changes the **goal**. The lemma is
`Real.Gamma_add_one : s ≠ 0 → Gamma (s + 1) = s * Gamma s`; for a numeral `s` write `(by norm_num)` for `hs`.
Placeholders: `(s : ℝ) (hs : s ≠ 0)`.

| Before | After |
|---|---|
| `⊢ P (Gamma (s + 1))` | `⊢ P (s * Gamma s)` |

**R8 · `rw [Real.Gamma_one_half_eq]`** changes the **goal**: `Gamma (1 / 2) = √π`.

| Before | After |
|---|---|
| `⊢ P (Gamma (1 / 2))` | `⊢ P √π` |

W2 chains R6, R7 twice and R8 for `Γ(5/2)`, then `ring`:

```lean-goal
⊢ Gamma ((4 + 1) / 2) = 3 / 4 * √π
⊢ Gamma (3 / 2 + 1) = 3 / 4 * √π
⊢ 3 / 2 * Gamma (3 / 2) = 3 / 4 * √π
⊢ (1 / 2 + 1) * Gamma (1 / 2 + 1) = 3 / 4 * √π
⊢ (1 / 2 + 1) * (1 / 2 * Gamma (1 / 2)) = 3 / 4 * √π
⊢ (1 / 2 + 1) * (1 / 2 * √π) = 3 / 4 * √π
```

### Evaluating `a ^ (-3/2)`

**R9 · `rw [Real.rpow_neg ha.le]`** changes the **goal**. The lemma is
`Real.rpow_neg : 0 ≤ x → ∀ y, x ^ (-y) = (x ^ y)⁻¹`. From `ha : 0 < a`, `ha.le : 0 ≤ a` is the weak inequality.
Placeholders: `(a y : ℝ) (ha : 0 < a)`.

| Before | After |
|---|---|
| `⊢ P (a ^ (-y))` | `⊢ P (a ^ y)⁻¹` |

**R10 · `rw [Real.rpow_add ha]`** changes the **goal**. The lemma is
`Real.rpow_add : 0 < x → ∀ y z, x ^ (y + z) = x ^ y * x ^ z`. Placeholders: `(a y z : ℝ) (ha : 0 < a)`.

| Before | After |
|---|---|
| `⊢ P (a ^ (y + z))` | `⊢ P (a ^ y * a ^ z)` |

**R11 · `rw [Real.rpow_one]`** changes the **goal**: `x ^ (1 : ℝ) = x`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a ^ 1)` | `⊢ P a` |

**R12 · `rw [← Real.sqrt_eq_rpow]`** changes the **goal**. The lemma is `Real.sqrt_eq_rpow x : √x = x ^ (1 / 2)`;
right to left it turns the real power `1 / 2` into a square root. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a ^ (1 / 2))` | `⊢ P √a` |

W3 chains R6, R9, R10, R11, R12 for `a ^ (-5/2)`, then `ring` (the exercise needs `-(1 + 1 / 2)`, one `rpow_add`):

```lean-goal
⊢ a ^ (-(4 + 1) / 2) = 1 / (a * a * √a)
⊢ a ^ (-(1 + 1 + 1 / 2)) = 1 / (a * a * √a)
⊢ (a ^ (1 + 1 + 1 / 2))⁻¹ = 1 / (a * a * √a)
⊢ (a * a * a ^ (1 / 2))⁻¹ = 1 / (a * a * √a)
⊢ (a * a * √a)⁻¹ = 1 / (a * a * √a)
```

### Finishing

**R13 · `have hsa : 0 < √a := Real.sqrt_pos.mpr ha`** changes the **context**. The lemma is
`Real.sqrt_pos : 0 < √x ↔ 0 < x`; `.mpr` is its right-to-left direction. `field_simp` (R15) needs this fact to
clear the denominator `√a`. Placeholders: `(a : ℝ) (ha : 0 < a)`.

| Before | After |
|---|---|
| `ha : 0 < a ⊢ G` | `hsa : 0 < √a ⊢ G` |

**R14 · `rw [Real.sqrt_div' _ ha.le]`** changes the **goal**. The lemma is
`Real.sqrt_div' x : 0 ≤ y → √(x / y) = √x / √y`; `_` lets `rw` find `x`. Placeholders: `(x a : ℝ) (ha : 0 < a)`.

| Before | After |
|---|---|
| `⊢ P √(x / a)` | `⊢ P (√x / √a)` |

**R15 · `field_simp`** **closes** (or simplifies) an equation of fractions: it multiplies out every denominator
it can prove nonzero (from `0 < d` or `d ≠ 0` in the context, and numerals), then normalises with `ring_nf`.
Placeholders: `(a s : ℝ) (ha : 0 < a) (hs : 0 < s)`.

| Before | After |
|---|---|
| `ha : 0 < a, hs : 0 < s ⊢ 3 * (1 / (a * s) * (1 / 3)) = 1 / a * (1 / s)` | no goals |

In the exercise, after `rw [hG, hpow]` and R14 the goal is
`2 * (1 / (a * √a) * (1 / 2) * (√π / 2)) = 1 / (2 * a) * (√π / √a)`, which `field_simp` closes with `ha`, `hsa`.

---

## Part 2 · `weight_eq` (milestone)

Statement: `(fun x => rexp (-β * (harmonic κ).energy x)) = fun x => rexp (-(β * κ / 2) * x ^ 2)`, an equation
of **functions**: the Boltzmann weight is a Gaussian with `a = βκ/2`.

**R16 · `funext x`** changes the **goal and the context**: two functions are equal when they agree at every
point. Placeholders: `(f g : ℝ → ℝ)`.

| Before | After |
|---|---|
| `⊢ f = g` | `x : ℝ ⊢ f x = g x` |

**R17 · `simp only [D]`** on a structure defined with `where` changes the **goal**: `(D c).energy x` becomes the
body of the `energy` field. In the exercise `D = harmonic`. Placeholders: `quartic c` (guide toy ensemble,
energy `c * x ^ 4`), `(c x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((quartic c).energy x)` | `⊢ P (c * x ^ 4)` |

**R18 · `ring_nf`** **closes** `f A = f B` when `A` and `B` are equal as ring expressions: it normalises every
ring subexpression, also inside `rexp (…)`, and equal normal forms close the goal. Placeholders: `(b c x : ℝ)`.

| Before | After |
|---|---|
| `⊢ c * x ^ 4 * rexp (-b * (c * x ^ 4)) = c * (x ^ 4 * rexp (-(b * c) * x ^ 4))` | no goals |

R16, R17, R18 in that order prove the milestone.

---

## Part 3 · `integrand_eq` (milestone)

Statement: `(fun x => E x * rexp (-β * E x)) = fun x => κ / 2 * (x ^ 2 * rexp (-(β * κ / 2) * x ^ 2))` with
`E = (harmonic κ).energy`: the numerator's integrand is `κ/2` times the second-moment integrand. The same three
steps as Part 2: R16, R17, R18 (the R18 example is exactly this shape, for `c x⁴`).

---

## Part 4 · `equipartition`

Statement: for `0 < κ` and `0 < T.val`, `(harmonic κ).meanEnergy T = kB * T.toReal / 2`. Prove the three
milestones first: `integrand_eq` and `weight_eq` rewrite the two integrands, `moment2` replaces the numerator.

### The ratio of integrals

**R19 · `rw [meanEnergy_eq_ratio_of_integrals]`** changes the **goal**. The lemma is
`CanonicalEnsemble.meanEnergy_eq_ratio_of_integrals 𝓒 T : 𝓒.meanEnergy T = (∫ i, 𝓒.energy i * rexp (-↑T.β * 𝓒.energy i) ∂𝓒.μ) / ∫ i, rexp (-↑T.β * 𝓒.energy i) ∂𝓒.μ`.
Placeholders: `{ι : Type} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (T : Temperature)`.

| Before | After |
|---|---|
| `⊢ P (𝓒.meanEnergy T)` | `⊢ P ((∫ (i : ι), 𝓒.energy i * rexp (-↑T.β * 𝓒.energy i) ∂𝓒.μ) / ∫ (i : ι), rexp (-↑T.β * 𝓒.energy i) ∂𝓒.μ)` |

**R20 · `have hβ : 0 < (T.β : ℝ) := Temperature.beta_pos T hT`** changes the **context**. The lemma is
`Temperature.beta_pos T : 0 < T.val → 0 < ↑T.β`. Placeholders: `(T : Temperature) (hT : 0 < T.val)`.

| Before | After |
|---|---|
| `hT : 0 < T.val ⊢ G` | `hβ : 0 < ↑T.β ⊢ G` |

**R21 · `positivity`** **closes** a goal `0 < e` or `0 ≤ e` when `e` is built from `*`, `/`, `+`, `√`, `rexp`,
`π`, numerals and atoms `x` with `0 < x` in the context. Use it for `ha : 0 < ↑T.β * κ / 2` (needs `hβ`, `hκ`)
and, after R5, for `0 < √(π / (↑T.β * κ / 2))`. Placeholders: `(b c : ℝ) (hb : 0 < b) (hc : 0 < c)`.

| Before | After |
|---|---|
| `hb : 0 < b, hc : 0 < c ⊢ 0 < √(π / (b * c / 2))` | no goals |

**R22 · `show G'`** changes the **goal** to `G'`, which must be equal to it *by definition* (Lean checks by
unfolding). After R19 the integrals are against `(harmonic κ).μ`, which is `volume` only by definition, so
`rw [moment2 _ ha]` (stated with `volume`) would not match. Restate the goal with `∂volume`; `_` stands for the
right-hand side you do not retype. Placeholders: `quartic c`, `(f : ℝ → ℝ) (y : ℝ)`.

| Before | After |
|---|---|
| `⊢ ∫ (x : ℝ), f x ∂(quartic c).μ = y` | `⊢ ∫ (x : ℝ), f x = y` |

W5 does R19 then R22 on the toy ensemble:

```lean-goal
⊢ (quartic c).meanEnergy T = y
⊢ (∫ (i : ℝ), (quartic c).energy i * rexp (-↑T.β * (quartic c).energy i) ∂(quartic c).μ) / ∫ (i : ℝ), rexp (-↑T.β * (quartic c).energy i) ∂(quartic c).μ = y
⊢ (∫ (x : ℝ), (quartic c).energy x * rexp (-↑T.β * (quartic c).energy x)) / ∫ (x : ℝ), rexp (-↑T.β * (quartic c).energy x) = y
```

### Rewriting the integrands

**R23 · `rw [hfg]` with an equation of functions** changes the **goal**. `∫ x, B x` is
`integral volume (fun x => B x)`, so the integrand is a literal `fun`, and a milestone of the form
`(fun x => B x) = fun x => C x` (Parts 2, 3) replaces it whole. A pointwise fact `∀ x, B x = C x` would not work
with `rw` here: the `x` inside `∫` is bound. Placeholders: `(c : ℝ)`,
`hfg : (fun x => c * x ^ 4) = fun x => x ^ 4 * c`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ), c * x ^ 4)` | `⊢ P (∫ (x : ℝ), x ^ 4 * c)` |

In the exercise, `rw [integrand_eq, weight_eq]` turns the two integrands into
`κ / 2 * (x ^ 2 * rexp (-(↑T.β * κ / 2) * x ^ 2))` and `rexp (-(↑T.β * κ / 2) * x ^ 2)`.

**R24 · `rw [integral_const_mul]`** changes the **goal**. The lemma is
`integral_const_mul r f : ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ` (no integrability needed). Placeholders:
`(r : ℝ) (f : ℝ → ℝ)`. The bound variable is renamed `a`; that changes nothing.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ), r * f x)` | `⊢ P (r * ∫ (a : ℝ), f a)` |

Then `rw [moment2 _ ha]` replaces the second moment by `1 / (2 * (↑T.β * κ / 2)) * Z`, where
`Z = ∫ x, rexp (-(↑T.β * κ / 2) * x ^ 2)`.

### Cancelling `Z`

Prove `hZ : 0 < Z` first: `rw [integral_gaussian]` (R5), then `positivity` (R21).

**R25 · `rw [← mul_assoc]`** changes the **goal**. The lemma is `mul_assoc : a * b * c = a * (b * c)` (`*`
groups to the left: `a * b * c` is `(a * b) * c`); right to left it regroups. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a * (b * c))` | `⊢ P (a * b * c)` |

**R26 · `rw [mul_div_assoc]`** changes the **goal**: `mul_div_assoc : a * b / c = a * (b / c)`. Placeholders:
`(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a * b / c)` | `⊢ P (a * (b / c))` |

**R27 · `rw [div_self hZ.ne']`** changes the **goal**: `div_self : a ≠ 0 → a / a = 1`. From `hZ : 0 < Z`,
`hZ.ne' : Z ≠ 0` (`ne` would give `0 ≠ Z`; the prime flips it). Placeholders: `(Z : ℝ) (hZ : 0 < Z)`.

| Before | After |
|---|---|
| `⊢ P (Z / Z)` | `⊢ P 1` |

**R28 · `rw [mul_one]`** changes the **goal**: `a * 1 = a`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a * 1)` | `⊢ P a` |

W4 chains R25–R28:

```lean-goal
⊢ c * (d * Z) / Z = c * d
⊢ c * d * Z / Z = c * d
⊢ c * d * (Z / Z) = c * d
⊢ c * d * 1 = c * d
```

### Temperature, `kB`, and the last algebra

**R29 · `rw [Temperature.β_toReal]`** changes the **goal**. The lemma is
`Temperature.β_toReal T : ↑T.β = 1 / (kB * T.toReal)`. Placeholders: `(T : Temperature)`.

| Before | After |
|---|---|
| `⊢ P ↑T.β` | `⊢ P (1 / (kB * T.toReal))` |

**R30 · `have hT' : (0 : ℝ) < T.toReal := hT`** changes the **context**. `T.toReal` is `↑T.val` by definition,
and `<` on `ℝ≥0` is by definition `<` of the real casts, so `hT : 0 < T.val` itself proves the real inequality.
`field_simp` needs it (it cannot see through `ℝ≥0`). Placeholders: `(T : Temperature) (hT : 0 < T.val)`.

| Before | After |
|---|---|
| `hT : 0 < T.val ⊢ G` | `hT' : 0 < T.toReal ⊢ G` |

**R31 · `have := kB_pos`** changes the **context**: `Constants.kB_pos : 0 < kB`. A `have` without a name calls
the fact `this`.

| Before | After |
|---|---|
| `⊢ G` | `this : 0 < kB ⊢ G` |

With `hκ`, `hT'` and `this` in the context, `field_simp` (R15) closes the final goal
`κ / 2 * (1 / (2 * (1 / (kB * T.toReal) * κ / 2))) = kB * T.toReal / 2`.

---

## Traps

- `x ^ 2` with a real exponent (`Real.rpow`) and with a natural exponent print the same but are different terms.
  R4 needs real powers, R5 and the exercise's statements use natural ones; `rw` fails on the wrong kind
  without telling you why. Convert with `Real.rpow_two` (R2), and write `(2 : ℝ)` in `have` statements.
- Numerals default to `ℕ`: in `show (2 + 1) / 2 = …` Lean computes in `ℕ` (where `3 / 2 = 1`). Write
  `((2 : ℝ) + 1) / 2` (R6).
- `(harmonic κ).μ` is `volume` and `(harmonic κ).energy x` is `κ * x ^ 2 / 2` only *by definition*: `rw` does not
  see either. Use `show … ∂volume …` (R22) and `simp only [harmonic]` (R17).
- `rw` cannot rewrite under `∫ x, …` with a pointwise `∀ x, …` fact; that is why `weight_eq` and `integrand_eq`
  are equations of functions (R23).
- `integral_gaussian` and `∫` itself never complain: a non-integrable function has integral `0`. The proof stays
  correct, but positivity of `Z` must come from `√(π / a)` with `0 < a` (R5, R21).
- `field_simp` needs every denominator's positivity or `≠ 0` fact in the context: `√a` (R13), `T.toReal` (R30),
  `kB` (R31), `κ`. Without them the fractions stay.
- `↑T.β` is a cast from `ℝ≥0`: `positivity` knows `0 ≤ ↑T.β` but needs `hβ : 0 < ↑T.β` (R20) for `<`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| even integrand → `2 * ∫ in Ioi 0` | `rw [← integral_comp_abs (f := fun x : ℝ => …)]` | R1 |
| real `x ^ (2:ℝ)` ↔ natural `x ^ 2`; drop `\|x\|` | `simp only [Real.rpow_two, sq_abs]` | R2, R3 |
| `∫₀^∞ x^q e^{-b x^p}` | `rw [integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hb]` | R4 |
| `∫ e^{-b x²}` | `rw [integral_gaussian]` | R5 |
| reshape a numeral | `rw [show ((2 : ℝ) + 1) / 2 = 1 / 2 + 1 by norm_num]` | R6 |
| `Γ(s + 1)`, `Γ(1/2)` | `rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]` | R7, R8 |
| `a ^ (-y)`, `a ^ (y + z)`, `a ^ 1` | `rw [Real.rpow_neg ha.le, Real.rpow_add ha, Real.rpow_one]` | R9–R11 |
| `a ^ (1/2)` → `√a` | `rw [← Real.sqrt_eq_rpow]` | R12 |
| `0 < √a` | `Real.sqrt_pos.mpr ha` | R13 |
| `√(x / a)` | `rw [Real.sqrt_div' _ ha.le]` | R14 |
| clear denominators and close | `field_simp` | R15 |
| function equation → pointwise | `funext x` | R16 |
| unfold `(harmonic κ).energy x` | `simp only [harmonic]` | R17 |
| `rexp A = rexp B`, `A`, `B` ring-equal | `ring_nf` | R18 |
| `⟨E⟩` → ratio of integrals | `rw [meanEnergy_eq_ratio_of_integrals]` | R19 |
| `0 < ↑T.β` | `Temperature.beta_pos T hT` | R20 |
| `0 < e` from the shape of `e` | `positivity` | R21 |
| `∂(harmonic κ).μ` → `∂volume` | `show (∫ x, … ∂volume) / (∫ x, … ∂volume) = _` | R22 |
| replace an integrand | `rw [integrand_eq, weight_eq]` | R23 |
| constant out of `∫` | `rw [integral_const_mul]` | R24 |
| cancel `Z / Z` | `rw [← mul_assoc, mul_div_assoc, div_self hZ.ne', mul_one]` | R25–R28 |
| `↑T.β` → `1 / (kB * T.toReal)` | `rw [Temperature.β_toReal]` | R29 |
| `0 < T.toReal`, `0 < kB` | `have hT' : (0 : ℝ) < T.toReal := hT`, `have := kB_pos` | R30, R31 |
| see the state | infoview | |
