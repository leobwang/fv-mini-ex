# H068 · Trapezoid rule error: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `intro`, `exact`, `apply`, `refine`, `rw`, `simp`,
`have`, `obtain`, `calc`, `·` focusing, bounded quantifiers `∀ x ∈ s, …`.
**New here:** Mathlib's real numbers `ℝ`, derivatives as the predicate `HasDerivAt`, continuity
(`Continuous`, `ContinuousAt`), interval integrals `∫ x in a..b, g x` with integrability side conditions
(`IntervalIntegrable`), intervals `Icc`, `uIcc`, absolute value `|·|`, pointwise arithmetic on functions, and
the tactics `fun_prop`, `push_cast`, `linarith`.

**The maths.** Write `T = (b − a)/2 · (f(a) + f(b))` (trapezoid rule) and `w(t) = (t − a)(b − t)/2` (the
*Peano kernel*). Then `w(a) = w(b) = 0`, `w′(t) = (a + b − 2t)/2`, `w″ = −1`, and `w ≥ 0` on `[a, b]`.
Integration by parts, `∫ₐᵇ u v′ = u(b)v(b) − u(a)v(a) − ∫ₐᵇ u′ v`, twice:

- `u = w`, `v = f′`: `∫ w f″ = 0 − 0 − ∫ w′ f′` (boundary terms vanish since `w(a) = w(b) = 0`);
- `u = w′`, `v = f`: `∫ w′ f′ = w′(b) f(b) − w′(a) f(a) − ∫ (−1) f = −T + ∫ f`, since `w′(b) = −(b − a)/2`,
  `w′(a) = (b − a)/2`.

So `∫ f − T = −∫ w f″` (MILESTONE `peano`). Then, with `|f″| ≤ M` on `[a, b]` and `a ≤ b`:
`|∫ w f″| ≤ ∫ |w f″| = ∫ w |f″| ≤ ∫ M w = M (b − a)³/12`, the last step by the fundamental theorem of calculus
with antiderivative `F(t) = −(t − a)³/6 + (b − a)(t − a)²/4` of `w` (MILESTONE `kernel_integral`).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`exact`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before and
after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal that the step does not touch; `k` is a hypothesis
  that finishes the example once the new fact is in the context.
- Placeholders are written as Lean binders: `(u v : ℝ → ℝ)` are real functions, `(d e x c : ℝ)` reals,
  `(n : ℕ)` a natural number. Every library lemma here is stated for general fields or normed spaces; the
  guide uses them at `ℝ`, which meets every type-class requirement they have.
- States containing `|` (absolute value) are shown in a ```` ```lean-goal ```` block (first line before,
  second after), because `|` would break a table.
- Every `⊢` cell and goal line is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ`, `ℕ` | Mathlib's real numbers; the natural numbers (exponents of `^` are in `ℕ`) |
| `(b - a) ^ 3` | the power `(b − a)³`; the exponent `3 : ℕ` is a natural number, not a real |
| `HasDerivAt u d x` | `u : ℝ → ℝ` is differentiable at `x` with derivative `u′(x) = d` (`d` is a number) |
| `Continuous g`, `ContinuousAt g x` | `g` is continuous everywhere / at the point `x` |
| `∫ (x : ℝ) in a..b, g x` | the interval integral `∫ₐᵇ g(x) dx` (oriented: it is `−∫ᵇₐ` when `b < a`) |
| `MeasureTheory.volume` | Lebesgue measure on `ℝ`, i.e. ordinary `dx` |
| `IntervalIntegrable g MeasureTheory.volume a b` | `g` is integrable on the interval between `a` and `b`; every continuous `g` is (R14) |
| `Icc a b` | the closed interval `[a, b] = {x \| a ≤ x ∧ x ≤ b}` (`Set.Icc`, `open Set` drops the prefix) |
| `uIcc a b` | `[min a b, max a b]`: the closed interval whichever of `a`, `b` is larger |
| `\|x\|` | absolute value of the real `x` (`abs x`) |
| `\|(-p)\|` | `\|-p\|`; Lean prints the parentheses |
| `u - v`, `u * v`, `u ^ n`, `-u` with `u v : ℝ → ℝ` | functions, defined pointwise: `(u * v) x = u x * v x` (R11 for `-`) |
| `(fun x => x - a) * ((fun x => b) - fun x => x)` | the function `t ↦ (t − a)(b − t)`, as R5–R7 build it |
| `(fun x => c) t` | a function applied to an argument; `simp only` reduces it to `c` (beta reduction) |
| `↑3`, `↑n` | the natural number `3` (or `n : ℕ`) cast into `ℝ` (R19, R21) |
| `(t - a) ^ (3 - 1)` | the exponent is a natural number: `3 - 1` is computed in `ℕ` (R21 evaluates it) |
| `a✝` | an inaccessible hypothesis (from `intro t _`); you cannot type its name |
| `case hf`, `case hg`, `case h` | the three goals of R28: integrability of the left, of the right, pointwise bound |
| `case ha`, `case hb`, `case hbc` | the goals of R24 / R32, named after the lemma's hypotheses |

---

## Part 1 · `peano` (MILESTONE 1)

Statement: `(∫ t in a..b, f t) - (b - a) / 2 * (f a + f b) = -∫ t in a..b, (t - a) * (b - t) / 2 * f'' t`,
given `hf : ∀ t, HasDerivAt f (f' t) t`, `hf' : ∀ t, HasDerivAt f' (f'' t) t`, `hcont : Continuous f''`.
Used in step 1 of Part 4.

### Continuity from a derivative

**R1 · `rw [continuous_iff_continuousAt]`** changes the **goal**. The lemma is
`continuous_iff_continuousAt : Continuous g ↔ ∀ x, ContinuousAt g x`. Placeholders: `(g : ℝ → ℝ)`.
In term mode `continuous_iff_continuousAt.mpr` (the `←` direction of the `↔`) takes a proof of the right side.

| Before | After |
|---|---|
| `⊢ Continuous g` | `⊢ ∀ (x : ℝ), ContinuousAt g x` |

**R2 · `HasDerivAt.continuousAt`** changes the **context**: differentiable at `x` implies continuous at `x`.
Statement: `HasDerivAt g d x → ContinuousAt g x`, written with dot notation `hg.continuousAt`. Placeholders:
`(g : ℝ → ℝ) (d x : ℝ) (hg : HasDerivAt g d x)`. With R1:
`have cg : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt` for
`hg : ∀ x, HasDerivAt g (g' x) x`. You need `Continuous f'` for an integrability side condition of the
second R12 (`v' = f'` there); `Continuous f` is never needed, and `f''` is continuous by `hcont`.

| Before | After |
|---|---|
| `⊢ G` | `hc : ContinuousAt g x ⊢ G` |

### Building a derivative

`HasDerivAt` facts are built **forward**, from the identity and constants, one operation at a time (R3–R9,
plus R19, R20 in Part 2), then the derivative is put in the form you want (R10, R11). Each lemma is used with
dot notation: `hu.sub hv`, `(hasDerivAt_id' t).sub_const a`. Placeholders: `(u v : ℝ → ℝ) (d e x c : ℝ)`,
`hu : HasDerivAt u d x`, `hv : HasDerivAt v e x`.

**R3 · `hasDerivAt_id' x`** changes the **context**: the identity `fun x => x` has derivative `1`.
(`hasDerivAt_id` without the prime states the same for `id`; the primed form prints as `fun x => x`, which
reads like your goal.)

| Before | After |
|---|---|
| `⊢ G` | `h : HasDerivAt (fun x => x) 1 x ⊢ G` |

**R4 · `hasDerivAt_const x c`** changes the **context**: a constant function has derivative `0`.

| Before | After |
|---|---|
| `⊢ G` | `h : HasDerivAt (fun x => c) 0 x ⊢ G` |

**R5 · `hu.sub_const c`** changes the **context**: subtracting a constant keeps the derivative.
Statement: `HasDerivAt u d x → HasDerivAt (fun x => u x - c) d x`. (`add_const` is the same with `+`.)

| Before | After |
|---|---|
| `⊢ G` | `h : HasDerivAt (fun x => u x - c) d x ⊢ G` |

**R6 · `hu.sub hv`, `hu.add hv`** change the **context**: derivative of a difference / sum. The function is
printed as `u - v`, a pointwise difference of functions (see R11).

| Before | After `have h₁ := hu.sub hv` | After `have h₂ := hu.add hv` |
|---|---|---|
| `⊢ G` | `h₁ : HasDerivAt (u - v) (d - e) x ⊢ G` | `h₂ : HasDerivAt (u + v) (d + e) x ⊢ G` |

**R7 · `hu.mul hv`** (product rule) changes the **context**: `(uv)′ = u′v + uv′`, with `u x`, `v x` the values
at the point.

| Before | After |
|---|---|
| `⊢ G` | `h : HasDerivAt (u * v) (d * v x + u x * e) x ⊢ G` |

**R8 · `hu.const_mul c`** changes the **context**: `(c·u)′ = c·u′`.

| Before | After |
|---|---|
| `⊢ G` | `h : HasDerivAt (fun y => c * u y) (c * d) x ⊢ G` |

**R9 · `hu.div_const c`** changes the **context**: `(u/c)′ = u′/c`.

| Before | After |
|---|---|
| `⊢ G` | `h : HasDerivAt (fun x => u x / c) (d / c) x ⊢ G` |

**R10 · `refine hu.congr_deriv ?_`** changes the **goal**. Statement:
`HasDerivAt.congr_deriv : HasDerivAt u d x → d = e → HasDerivAt u e x`. The built derivative (R3–R9) is a
mess like `(1 * ((fun x => b) - fun x => x) t + (t - a) * (0 - 1)) / 2`; this leaves the equation "mess =
the form you want". The **function** in `hu` need not be written like the goal's: Lean accepts
`(fun x => x - a) * ((fun x => b) - fun x => x)` for `fun t => (t - a) * (b - t)` because both unfold to the
same thing. Placeholders: `(u : ℝ → ℝ) (d e x : ℝ) (hu : HasDerivAt u d x)`. One-line form:
`exact this.congr_deriv (by ring)`.

| Before | After |
|---|---|
| `⊢ HasDerivAt u e x` | `⊢ d = e` |

**R11 · `simp only [Pi.sub_apply]`** changes the **goal**. The lemma is `Pi.sub_apply : (u - v) x = u x - v x`;
`simp only` also beta-reduces `(fun x => c) t` to `c`. `ring` cannot see through `((fun x => b) - fun x => x) t`,
so do this before `ring` whenever R6 was applied to two functions. Placeholders: `(c t : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (((fun x => c) - fun y => y) t)` | `⊢ P (c - t)` |

**W1 (on `t ↦ t(1 − t)`, not the exercise's kernel).** `have hd := (hasDerivAt_id' x).mul ((hasDerivAt_const x 1).sub (hasDerivAt_id' x))`
(R3, R4, R6, R7), then R10, R11, `ring`:

```lean-goal
⊢ HasDerivAt (fun t => t * (1 - t)) (1 - 2 * x) x
⊢ 1 * ((fun x => 1) - fun x => x) x + x * (0 - 1) = 1 - 2 * x
⊢ 1 * (1 - x) + x * (0 - 1) = 1 - 2 * x
```

### Integration by parts and integrability

**R12 · `rw [integral_mul_deriv_eq_deriv_mul hu hv hu' hv']`** changes the **goal**. The lemma
(`intervalIntegral.integral_mul_deriv_eq_deriv_mul`) is integration by parts:

`(∀ x ∈ uIcc a b, HasDerivAt u (u' x) x) → (∀ x ∈ uIcc a b, HasDerivAt v (v' x) x) →
IntervalIntegrable u' volume a b → IntervalIntegrable v' volume a b →
∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x`.

Placeholders: `(u v u' v' : ℝ → ℝ) (a b : ℝ)`. `rw` rewrites the integral whose integrand has the shape
`u x * v' x` with **your** `u`, `v'`: the kernel must be the left factor and the derivative the right one,
exactly as in the goal. The boundary values come out unsimplified, e.g. `(b - a) * (b - b) / 2 * f' b`;
`ring` clears them at the end.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ) in a..b, u x * v' x)` | `⊢ P (u b * v b - u a * v a - ∫ (x : ℝ) in a..b, u' x * v x)` |

**R13 · `fun x _ => hq x`** **closes** `∀ x ∈ s, Q x` from `hq : ∀ x, Q x`: the `_` ignores the membership
proof. Use it for R12's and R22's first arguments: `(fun t _ => hw t)`. Placeholders: `(s : Set ℝ) (Q : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ x ∈ s, Q x` | no goals |

**R14 · `hg.intervalIntegrable a b`** **closes** an integrability goal. Statement:
`Continuous.intervalIntegrable : Continuous g → ∀ a b, IntervalIntegrable g volume a b`. Write `_ _` for
`a b` inside a `rw [...]` argument. Placeholders: `(g : ℝ → ℝ) (hg : Continuous g) (a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ IntervalIntegrable g MeasureTheory.volume a b` | no goals |

**R15 · `fun_prop`** **closes** `Continuous fun t => …` when the body is built from `+ - * /` (by a constant),
`|·|`, powers, constants, `t` itself, and functions whose continuity is a hypothesis in the context. With
R14: `(by fun_prop : Continuous fun t : ℝ => (a + b - 2 * t) / 2).intervalIntegrable _ _`. The type
ascription `t : ℝ` matters when the body alone does not fix the type. Placeholders: `(c : ℝ) (g : ℝ → ℝ)
(hg : Continuous g)`. Before (after: no goals):

```lean-goal
⊢ Continuous fun t => |c * g t - t ^ 2 / 3|
```

**R16 · `intervalIntegrable_const`** **closes** integrability of a constant function, e.g. of `w″ = -1` in the
second integration by parts. Placeholders: `(c a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ IntervalIntegrable (fun x => c) MeasureTheory.volume a b` | no goals |

**R17 · `simp only [neg_one_mul]`** changes the **goal**. The lemma is `neg_one_mul : -1 * a = -a`; `simp only`
rewrites under `∫` too, where `rw` cannot reach the bound `x`. Placeholders: `(g : ℝ → ℝ) (a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ) in a..b, -1 * g x)` | `⊢ P (∫ (x : ℝ) in a..b, -g x)` |

**R18 · `intervalIntegral.integral_neg`** changes the **goal**: `∫ x in a..b, -g x = -∫ x in a..b, g x`. Put it
in the same `simp only [neg_one_mul, integral_neg]`; after that both sides mention only `∫ f`, and `ring`
closes the goal. Placeholders: `(g : ℝ → ℝ) (a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ) in a..b, -g x)` | `⊢ P (-∫ (x : ℝ) in a..b, g x)` |

**W3 (one integration by parts with `u = id`, not the exercise's).** `rw [integral_mul_deriv_eq_deriv_mul
(fun x _ => hasDerivAt_id' x) (fun x _ => hg x) intervalIntegrable_const (hc.intervalIntegrable _ _)]`
(R12 with R13, R3, R16, R14) leaves `u' = 1` inside the integral; `simp only [one_mul]` closes it:

```lean-goal
⊢ b * g b - a * g a - ∫ (x : ℝ) in a..b, 1 * g x = b * g b - a * g a - ∫ (x : ℝ) in a..b, g x
```

---

## Part 2 · `kernel_integral` (MILESTONE 2)

Statement: `∫ t in a..b, (t - a) * (b - t) / 2 = (b - a) ^ 3 / 12`. Used in the last `calc` step of Part 4.
Prove `HasDerivAt F (w t) t` for the antiderivative `F` (see *The maths*) with R3, R5, R19, R20, R8, R9, R6,
then apply the fundamental theorem of calculus (R22).

**R19 · `hu.pow n`** changes the **context**: `(uⁿ)′ = n·uⁿ⁻¹·u′`. `↑n` is `n : ℕ` cast into `ℝ` and `n - 1` is
subtraction in `ℕ`; for a numeral `n` R21 cleans up both. Placeholders: `(u : ℝ → ℝ) (d x : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ G` | `h : HasDerivAt (u ^ n) (↑n * u x ^ (n - 1) * d) x ⊢ G` |

**R20 · `hu.neg`** changes the **context**: `(−u)′ = −u′`. Written `hu.neg`, or in a chain `(…).neg`.

| Before | After |
|---|---|
| `⊢ G` | `h : HasDerivAt (-u) (-d) x ⊢ G` |

**R21 · `push_cast`** changes the **goal**: it moves casts `↑` inward and evaluates casts of numerals
(`↑4` → `4`), and it also computes numeral arithmetic in `ℕ` such as `4 - 1` → `3`. After R10 on a
derivative built with R19, `push_cast` turns `↑3 * (t - a) ^ (3 - 1)` into `3 * (t - a) ^ 2`, so you can read
the equation before `ring` closes it (`ring` evaluates these numerals too, but when it fails the leftover
goal is easier to debug after `push_cast`). Placeholders: `(y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (↑4 * y ^ (4 - 1))` | `⊢ P (4 * y ^ 3)` |

**R22 · `rw [integral_eq_sub_of_hasDerivAt hF hg]`** changes the **goal**. The lemma
(`intervalIntegral.integral_eq_sub_of_hasDerivAt`) is the fundamental theorem of calculus:
`(∀ x ∈ uIcc a b, HasDerivAt F (g x) x) → IntervalIntegrable g volume a b → ∫ x in a..b, g x = F b - F a`.
State `hF` with `∀ t ∈ uIcc a b` (and `intro t _`), or build it from a `∀ t` fact with R13. The integrand
in the goal must be literally `g x` for the `g` in `hF`. Placeholders: `(F g : ℝ → ℝ) (a b : ℝ)`. After the
rewrite `F b - F a` appears with `F` substituted; `ring` finishes.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ) in a..b, g x)` | `⊢ P (F b - F a)` |

**W2 (`∫₀¹ t² = 1/3`, not the exercise's integral).** `hF` from `((hasDerivAt_id' t).pow 3).div_const 3`
(R3, R19, R9) with R10, R21, `ring`; then R22 with R15 → R14, then `norm_num`:

```lean-goal
⊢ ∫ (t : ℝ) in 0..1, t ^ 2 = 1 / 3
⊢ 1 ^ 3 / 3 - 0 ^ 3 / 3 = 1 / 3
```

---

## Part 3 · `kernel_nonneg` (MILESTONE 3)

Statement: `t ∈ Icc a b → 0 ≤ (t - a) * (b - t) / 2`. Used twice in the pointwise step of Part 4 (to drop the
absolute value of `w t`, and as the sign condition of R32).

**R23 · `obtain ⟨h₁, h₂⟩ := hx`** changes the **context**. `x ∈ Icc a b` unfolds to `a ≤ x ∧ x ≤ b`
(`Set.mem_Icc`), so it destructs like an `∧`. Placeholders: `(a b x : ℝ) (hx : x ∈ Icc a b)`.

| Before | After |
|---|---|
| `hx : x ∈ Icc a b ⊢ G` | `h₁ : a ≤ x, h₂ : x ≤ b ⊢ G` |

**R24 · `apply mul_nonneg`** changes the **goal list**. Statement: `mul_nonneg : 0 ≤ p → 0 ≤ q → 0 ≤ p * q`.
Placeholders: `(p q : ℝ)`. Term form: `mul_nonneg (by linarith) (by linarith)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ p * q` | `⊢ 0 ≤ p`, `⊢ 0 ≤ q` |

**R25 · `linarith`** **closes** a linear (in)equality that follows from linear hypotheses in the context
(it adds them with nonnegative coefficients). Division by a numeral is fine; a product of two variables is
not linear, which is why R24 comes first. Placeholders: `(a x : ℝ)`.

| Before | After |
|---|---|
| `h₁ : a ≤ x ⊢ 0 ≤ (x - a) / 2` | no goals |

---

## Part 4 · `trapezoid_error` (the spec theorem)

Statement: with `hab : a ≤ b`, `hf`, `hf'`, `hcont` as in Part 1 and `hM : ∀ t ∈ Icc a b, |f'' t| ≤ M`,
`|(∫ t in a..b, f t) - (b - a) / 2 * (f a + f b)| ≤ M * (b - a) ^ 3 / 12`. Rewrite with MILESTONE 1 (it is an
equation, so `rw [peano f f' f'' a b hf hf' hcont]` works), drop the minus sign (R26), then a three-step `calc`.

**R26 · `rw [abs_neg]`** changes the **goal**. The lemma is `abs_neg : |-p| = |p|`. Placeholders: `(p : ℝ)`.
Before and after:

```lean-goal
⊢ P |(-p)|
⊢ P |p|
```

**R27 · `abs_integral_le_integral_abs hab`** **closes** the first `calc` step. The lemma
(`intervalIntegral.abs_integral_le_integral_abs`) is `a ≤ b → |∫ x in a..b, g x| ≤ ∫ x in a..b, |g x|`. It
needs `a ≤ b` (for `b < a` the oriented integral flips sign). Placeholders: `(g : ℝ → ℝ) (a b : ℝ)
(hab : a ≤ b)`. Before (after: no goals):

```lean-goal
⊢ |∫ (x : ℝ) in a..b, g x| ≤ ∫ (x : ℝ) in a..b, |g x|
```

**R28 · `apply integral_mono_on hab`** changes the **goal list**: to compare two integrals, compare the
integrands on `[a, b]`. The lemma (`intervalIntegral.integral_mono_on`) is
`a ≤ b → IntervalIntegrable g volume a b → IntervalIntegrable k volume a b → (∀ x ∈ Icc a b, g x ≤ k x) →
∫ x in a..b, g x ≤ ∫ x in a..b, k x`. Close the two integrability goals with R15 → R14; start the third
with `intro t ht`. Placeholders: `(g k : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)`. With concrete integrands the
integrability goals print the integrand as a lambda, e.g. `IntervalIntegrable (fun u => …) MeasureTheory.volume a b`.

| Before | After |
|---|---|
| `⊢ ∫ (x : ℝ) in a..b, g x ≤ ∫ (x : ℝ) in a..b, k x` | `⊢ IntervalIntegrable g MeasureTheory.volume a b`, `⊢ IntervalIntegrable k MeasureTheory.volume a b`, `⊢ ∀ x ∈ Icc a b, g x ≤ k x` |

**R29 · `rw [abs_mul]`** changes the **goal**. The lemma is `abs_mul : |p * q| = |p| * |q|`. Placeholders:
`(p q : ℝ)`. Before and after:

```lean-goal
⊢ P |p * q|
⊢ P (|p| * |q|)
```

**R30 · `rw [abs_of_nonneg hp]`** changes the **goal**. The lemma is `abs_of_nonneg : 0 ≤ p → |p| = p`; give the
proof `hp` (here `kernel_nonneg a b t ht`) so `rw` knows which `|·|` to remove. Placeholders:
`(p : ℝ) (hp : 0 ≤ p)`. Before and after:

```lean-goal
⊢ P |p|
⊢ P p
```

**R31 · `rw [mul_comm]`** changes the **goal**. The lemma is `mul_comm : p * q = q * p`. Without arguments `rw`
takes the **first** product it meets (in the infoview's left-to-right order, outermost first) and swaps every
copy of exactly that product; `rw [mul_comm p q]` picks one. Here it brings the pointwise goal to the
shape `|f'' t| * w ≤ M * w` that R32 wants. Placeholders: `(p q r : ℝ) (P : ℝ → ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (p * q) (r * p)` | `⊢ P (q * p) (r * p)` |

**R32 · `apply mul_le_mul_of_nonneg_right`** changes the **goal list**. Statement:
`mul_le_mul_of_nonneg_right : q ≤ r → 0 ≤ p → q * p ≤ r * p` (multiply an inequality on the right by a
nonnegative factor). Term form: `exact mul_le_mul_of_nonneg_right (hM t ht) (kernel_nonneg a b t ht)`.
Placeholders: `(p q r : ℝ)`.

| Before | After |
|---|---|
| `⊢ q * p ≤ r * p` | `⊢ q ≤ r`, `⊢ 0 ≤ p` |

**R33 · `rw [integral_const_mul]`** changes the **goal**. The lemma (`intervalIntegral.integral_const_mul`) is
`∫ x in a..b, c * g x = c * ∫ x in a..b, g x`. Then `rw [kernel_integral]` and `ring`. Placeholders:
`(c a b : ℝ) (g : ℝ → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ) in a..b, c * g x)` | `⊢ P (c * ∫ (x : ℝ) in a..b, g x)` |

**W4 (a pointwise bound with weight `x²`, not the exercise's).** `apply integral_mono_on hab` (R28), the two
integrability goals by R15 → R14, then `intro x hx` and `exact mul_le_mul_of_nonneg_right (h1 x hx) (sq_nonneg x)`
(R32). The third goal is:

```lean-goal
⊢ ∀ x ∈ Icc a b, |g x| * x ^ 2 ≤ 1 * x ^ 2
```

---

## Traps

- **Name collisions with the exercise.** The exercise uses `f'` and `f''` as *variable names*; they are
  ordinary functions with `HasDerivAt` hypotheses, not Mathlib's `deriv f`. Never rewrite with `deriv`.
- **`rw` cannot see under `∫`.** `rw [neg_one_mul]` fails on `∫ x in a..b, -1 * f x` (the `x` is bound); use
  `simp only [...]` (R17). Library rewrites whose left side is a whole integral (R12, R18, R22, R33) are fine.
- **The IBP integrand must match literally.** R12 rewrites `∫ u x * v' x`: the kernel is the **left** factor.
  The exercise's right-hand side is already `w t * f'' t`; the second IBP applies to `∫ w' x * f' x`.
- **`ring` cannot read `((fun x => b) - fun x => x) t`.** After R10 on a derivative built with R6 from two
  functions, run R11 first. After R19, R21 makes the equation readable.
- **The kernel derivative signs.** `w′(t) = (a + b - 2 * t) / 2`, `w″ = -1`. With `hw'` stated as
  `HasDerivAt (fun t => (a + b - 2 * t) / 2) (-1) t`, R12's second use leaves `∫ -1 * f x` (R17, R18).
- **`a ≤ b` is needed** by R27 and R28, never by R12 or R22 (those work on `uIcc`).
- `have h : T := by …` needs its proof indented further than `have` (TACTIC_STATES, "Adding facts").
- `calc` steps: the first term is the goal's left side **after** `rw [peano …, abs_neg]`, written out in full;
  each step is `_ ≤ … := proof` and the last right side must be the goal's right side `M * (b - a) ^ 3 / 12`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `Continuous g` from `∀ x, HasDerivAt g (g' x) x` | `continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt` | R1, R2 |
| derivative of `x`, of `c` | `hasDerivAt_id' x`, `hasDerivAt_const x c` | R3, R4 |
| derivative of `u - c`, `u ± v`, `u * v`, `c * u`, `u / c`, `u ^ n`, `-u` | `hu.sub_const c`, `hu.sub hv` / `hu.add hv`, `hu.mul hv`, `hu.const_mul c`, `hu.div_const c`, `hu.pow n`, `hu.neg` | R5–R9, R19, R20 |
| fix the derivative's form | `refine h.congr_deriv ?_` (or `h.congr_deriv (by ring)`) | R10 |
| clean `(u - v) t`, `(fun x => c) t` | `simp only [Pi.sub_apply]` | R11 |
| clean `↑3`, `3 - 1` | `push_cast` | R21 |
| integration by parts | `rw [integral_mul_deriv_eq_deriv_mul hu hv hu' hv']` | R12 |
| `∀ x ∈ uIcc a b, …` from `∀ x, …` | `fun x _ => h x` | R13 |
| integrable (continuous) | `(by fun_prop : Continuous fun t : ℝ => …).intervalIntegrable _ _` | R14, R15 |
| integrable (constant) | `intervalIntegrable_const` | R16 |
| `∫ -1 * g` → `-∫ g` | `simp only [neg_one_mul, integral_neg]` | R17, R18 |
| FTC | `rw [integral_eq_sub_of_hasDerivAt hF hint]` | R22 |
| use `t ∈ Icc a b` | `obtain ⟨h₁, h₂⟩ := ht` | R23 |
| `0 ≤ p * q` | `mul_nonneg (by linarith) (by linarith)` | R24, R25 |
| linear inequality | `linarith` | R25 |
| `\|-p\|` → `\|p\|` | `rw [abs_neg]` | R26 |
| `\|∫ g\| ≤ ∫ \|g\|` | `abs_integral_le_integral_abs hab` | R27 |
| compare integrals pointwise | `apply integral_mono_on hab` | R28 |
| `\|p * q\|`, `\|p\|` with `0 ≤ p` | `rw [abs_mul, abs_of_nonneg hp]` | R29, R30 |
| swap a product | `rw [mul_comm]` / `rw [mul_comm p q]` | R31 |
| `q * p ≤ r * p` | `mul_le_mul_of_nonneg_right hqr hp` | R32 |
| pull a constant out of `∫` | `rw [integral_const_mul]` | R33 |
| see the state | infoview | |
