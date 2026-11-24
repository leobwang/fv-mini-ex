# M113 · Simpson's rule is exact for cubics: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ`, the interval
integral `∫ x in a..b, f x`, integrability, the power rule `integral_pow`,
scalar multiplication `•`, and the `fun_prop` and `ring` tactics.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders: `(f g : ℝ → ℝ)` are real functions, `(a b : ℝ)` the interval's
  endpoints, `(n : ℕ)` a natural-number exponent. The library lemmas are stated for any normed vector space
  `E` (written `{E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]`); here `E = ℝ` always, so the guide
  states them on `ℝ`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers (`Real`); every variable in the statement is real |
| `∫ (x : ℝ) in a..b, f x` | the interval integral $\int_a^b f(x)\,dx$ (Mathlib: `intervalIntegral`). For `b < a` it is $-\int_b^a$, so no `a ≤ b` is needed |
| `∫ x in a..b, f x ∂μ` | the same integral against a measure `μ`; without `∂μ` it is Lebesgue measure |
| `MeasureTheory.volume` | Lebesgue measure on `ℝ` (length of intervals); the `μ` you meet here |
| `IntervalIntegrable f μ a b` | `f` is integrable on the interval between `a` and `b`. Mathlib's integral returns the junk value `0` for non-integrable `f`, so linearity lemmas demand this |
| `Continuous fun x => c * x ^ n` | the function $x \mapsto c x^n$ is continuous on all of `ℝ` |
| `(∫ … , f x) + ∫ … , g x` | a sum of two integrals; Lean adds the parentheses because `∫` extends as far right as possible |
| `r • c` | scalar multiplication (`HSMul`); for `r c : ℝ` it equals `r * c` (R10) |
| `↑2`, `↑n` | the natural number `2` / `n` cast into `ℝ` (`Nat.cast`) |
| `2 + 1` in an exponent | a natural number `n + 1` that `integral_pow` produced; `ring` evaluates it |
| `x ^ n` | power with natural exponent `n : ℕ` (`Monoid.npow`), not `x ^ (n : ℝ)` |
| `case hf`, `case hg` | the two integrability side goals that `rw [intervalIntegral.integral_add]` leaves when you pass no proofs (R6) |

---

## Part 1 · `simpson_exact`

Statement: for every cubic $f(x) = c_0 + c_1 x + c_2 x^2 + c_3 x^3$ with real coefficients $c_i$ and
endpoints $a, b \in \mathbb{R}$,
$\int_a^b f = \frac{b-a}{6}\bigl(f(a) + 4 f(\tfrac{a+b}{2}) + f(b)\bigr)$. Plan: compute the left side in
closed form (split, pull out constants, power rule), then both sides are polynomials in $a, b, c_i$ and
`ring` checks they agree.

### Setting up

**R1 · `unfold D`** changes the **goal**: the defined name `D` is replaced by its body everywhere, also under
the `∫` binder. Placeholders: `D` defined by `def sq (x : ℝ) : ℝ := x * x`, `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ) in a..b, sq x)` | `⊢ P (∫ (x : ℝ) in a..b, x * x)` |

**R2 · `have i : ∀ (n : ℕ) (c : ℝ), T n c := fun n c => …`** changes the **context**: it adds a whole family
of facts at once. Afterwards `i 3 c` is a proof of `T 3 c` for any `c`; you pass it where a lemma wants that
fact. Placeholders: `(T : ℕ → ℝ → Prop)`, a proof `t : ∀ n c, T n c` standing for the `fun n c => …` body.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, with `i : ∀ (n : ℕ) (c : ℝ), T n c` added |

### Integrability

**R3 · `Continuous.intervalIntegrable`** changes the **goal**: integrability on `[a, b]` is reduced to
continuity on `ℝ`. Statement: `Continuous u → ∀ (a b : ℝ), IntervalIntegrable u μ a b` for any locally finite
measure `μ` (Lebesgue `volume` is one). Placeholders: `(f : ℝ → ℝ) (a b : ℝ) (hf : Continuous f)`. As a term:
`Continuous.intervalIntegrable hf a b`, or `Continuous.intervalIntegrable (by fun_prop) a b`.

| Before | After `apply Continuous.intervalIntegrable` |
|---|---|
| `⊢ IntervalIntegrable f MeasureTheory.volume a b` | `⊢ Continuous f` |

**R4 · `fun_prop`** **closes** a goal `Continuous (fun x => …)` whose body is built from continuous pieces
(`+`, `*`, `^ n`, constants, `x`). Placeholders: `(c : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ Continuous fun x => c * x ^ n` | no goals |

**R5 · `intervalIntegrable_const`** **closes** integrability of a constant function. Statement:
`IntervalIntegrable (fun _ => c) μ a b`. Placeholders: `(c a b : ℝ)`. It is a term: pass it straight to R6.

| Before | After `exact intervalIntegrable_const` |
|---|---|
| `⊢ IntervalIntegrable (fun x => c) MeasureTheory.volume a b` | no goals |

### Splitting and evaluating integrals

**R6 · `rw [intervalIntegral.integral_add hf hg]`** changes the **goal**: the integral of a sum becomes a sum
of integrals. Statement:
`IntervalIntegrable f μ a b → IntervalIntegrable g μ a b → ∫ x in a..b, f x + g x ∂μ = (∫ x in a..b, f x ∂μ) + ∫ x in a..b, g x ∂μ`.
Placeholders: `(f g : ℝ → ℝ) (a b : ℝ)`, `hf`, `hg` the two integrability facts (R3–R5). The proofs you pass
fix `f` and `g`, hence which `+` is split. Without them, `rw` splits the first `+` it finds and leaves the two
integrability facts as new goals.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ) in a..b, f x + g x)` | `⊢ P ((∫ (x : ℝ) in a..b, f x) + ∫ (x : ℝ) in a..b, g x)` |

**R7 · `intervalIntegral.integral_const_mul`** changes the **goal**: a constant factor moves out of the
integral. Statement: `∫ x in a..b, r * f x ∂μ = r * ∫ x in a..b, f x ∂μ`. Placeholders:
`(r : ℝ) (f : ℝ → ℝ) (a b : ℝ)`. `simp only` applies it only when the integrand is visibly `r * (f x)` with
`f x` not just `x` (W1); use `rw` for `∫ r * x`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ) in a..b, r * f x)` | `⊢ P (r * ∫ (x : ℝ) in a..b, f x)` |

**R8 · `integral_pow`** changes the **goal**: the power rule. Statement:
`∫ x in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (↑n + 1)`, i.e.
$\int_a^b x^n\,dx = \frac{b^{n+1}-a^{n+1}}{n+1}$. Placeholders: `(n : ℕ) (a b : ℝ)`. For a literal `n = 2` the
result shows as `(b ^ (2 + 1) - a ^ (2 + 1)) / (↑2 + 1)`; leave that to R12.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ) in a..b, x ^ n)` | `⊢ P ((b ^ (n + 1) - a ^ (n + 1)) / (↑n + 1))` |

**R9 · `intervalIntegral.integral_const`** changes the **goal**: the integral of a constant. Statement:
`∫ x in a..b, c = (b - a) • c`. Placeholders: `(c a b : ℝ)`. The `•` is there because the lemma is stated for
vector-valued `c`; follow with R10.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ) in a..b, c)` | `⊢ P ((b - a) • c)` |

**R10 · `smul_eq_mul`** changes the **goal**: a scalar action of a ring on itself is multiplication.
Statement: `a • b = a * b`. Placeholders: `(r c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (r • c)` | `⊢ P (r * c)` |

**R11 · `integral_id`** changes the **goal**: $\int_a^b x\,dx = \frac{b^2 - a^2}{2}$. Statement:
`∫ x in a..b, x = (b ^ 2 - a ^ 2) / 2`. Placeholders: `(a b : ℝ)`. This is the `n = 1` case that
`integral_pow` does not match, because the integrand is `x`, not `x ^ 1`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ) in a..b, x)` | `⊢ P ((b ^ 2 - a ^ 2) / 2)` |

### Closing

**R12 · `ring`** **closes** an equation that holds in every commutative ring, after normalizing both sides.
It handles division by numerals (`/ 6`), numeric exponents (`2 + 1`) and casts of numerals (`↑2`). It does not
look inside `∫`, so every integral must be gone first. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ (b ^ (2 + 1) - a ^ (2 + 1)) / (↑2 + 1) = (b - a) * (a ^ 2 + a * b + b ^ 2) / 3` | no goals |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: `simp only` skips `∫ e * x`.** On `(∫ d * x ^ 2) + ∫ e * x`, `simp only [R7, R8]` evaluates the first
integral and leaves the second; `rw [R7, R11]` finishes it, then `ring`:

```lean-goal
⊢ (∫ (x : ℝ) in a..b, d * x ^ 2) + ∫ (x : ℝ) in a..b, e * x = d * ((b ^ 3 - a ^ 3) / 3) + e * ((b ^ 2 - a ^ 2) / 2)
⊢ d * ((b ^ (2 + 1) - a ^ (2 + 1)) / (↑2 + 1)) + ∫ (x : ℝ) in a..b, e * x = d * ((b ^ 3 - a ^ 3) / 3) + e * ((b ^ 2 - a ^ 2) / 2)
⊢ d * ((b ^ (2 + 1) - a ^ (2 + 1)) / (↑2 + 1)) + e * ((b ^ 2 - a ^ 2) / 2) = d * ((b ^ 3 - a ^ 3) / 3) + e * ((b ^ 2 - a ^ 2) / 2)
```

**W2: the trapezoid rule is exact for lines.** $\int_a^b (d + e x)\,dx = \frac{b-a}{2}\bigl(f(a) + f(b)\bigr)$:
R6 with R5 and R3 + R4, then `simp only [R9, R10]`, then `rw [R7, R11]`, then R12:

```lean-goal
⊢ ∫ (x : ℝ) in a..b, d + e * x = (b - a) / 2 * (d + e * a + (d + e * b))
⊢ (∫ (x : ℝ) in a..b, d) + ∫ (x : ℝ) in a..b, e * x = (b - a) / 2 * (d + e * a + (d + e * b))
⊢ (b - a) * d + ∫ (x : ℝ) in a..b, e * x = (b - a) / 2 * (d + e * a + (d + e * b))
⊢ (b - a) * d + e * ((b ^ 2 - a ^ 2) / 2) = (b - a) / 2 * (d + e * a + (d + e * b))
```

**W3: split the last `+` first.** `+` groups to the left, so `p + q + r` is `(p + q) + r` and the outermost
split is `f = fun x => p + q`, `g = fun x => r`:

```lean-goal
⊢ ∫ (x : ℝ) in a..b, d * x + e * x ^ 2 + x ^ 3 = (∫ (x : ℝ) in a..b, d * x + e * x ^ 2) + ∫ (x : ℝ) in a..b, x ^ 3
```

---

## Traps

- `simp only [intervalIntegral.integral_const_mul]` leaves `∫ x in a..b, c * x` alone: `simp` cannot read the
  bare `x` as `f x`. Use `rw [intervalIntegral.integral_const_mul, integral_id]` for that term (W1).
- `integral_add` needs **both** summands integrable, including the left one, which is itself a sum: prove it
  continuous with `Continuous.intervalIntegrable (by fun_prop) a b` (R3, R4). The last split has a constant on
  the left: `intervalIntegrable_const` (R5).
- `c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3` is `((c₀ + c₁ * x) + c₂ * x ^ 2) + c₃ * x ^ 3`: split the outermost
  (last) `+` first, three times (W3).
- `integral_pow` does not fire on `∫ x` (no `^`): that term needs `integral_id` (R11).
- `i 1 c₁` does not fit the summand `c₁ * x`: `x ^ 1` and `x` are different terms to `rw`, so
  `integral_add … (i 1 c₁)` fails with "did not find an occurrence". Use
  `Continuous.intervalIntegrable (by fun_prop) a b` there (R3, R4).
- `∫ c` gives `(b - a) • c`; `ring` treats `•` as unknown until `smul_eq_mul` turns it into `*` (R9, R10).
- `ring` fails while any `∫` is left in the goal; check the infoview before calling it.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unfold the spec function | `unfold cubic` | R1 |
| integrability of every `c * x ^ n` once | `have i : ∀ (n : ℕ) (c : ℝ), IntervalIntegrable (fun x : ℝ => c * x ^ n) MeasureTheory.volume a b := fun n c => …` | R2 |
| integrable from continuous | `Continuous.intervalIntegrable (by fun_prop) a b` | R3, R4 |
| constant is integrable | `intervalIntegrable_const` | R5 |
| $\int (f + g) = \int f + \int g$ | `rw [intervalIntegral.integral_add hf hg]` | R6 |
| $\int r f = r \int f$ | `intervalIntegral.integral_const_mul` | R7 |
| $\int_a^b x^n = \frac{b^{n+1}-a^{n+1}}{n+1}$ | `integral_pow` | R8 |
| $\int_a^b c = (b-a)\,c$ | `intervalIntegral.integral_const`, then `smul_eq_mul` | R9, R10 |
| $\int_a^b x = \frac{b^2-a^2}{2}$ | `integral_id` | R11 |
| many integrals at once | `simp only [intervalIntegral.integral_const_mul, integral_pow, intervalIntegral.integral_const, smul_eq_mul]` | R7–R10 |
| leftover `∫ c * x` | `rw [intervalIntegral.integral_const_mul, integral_id]` | R7, R11 |
| polynomial identity | `ring` | R12 |
| see the state | infoview | |
