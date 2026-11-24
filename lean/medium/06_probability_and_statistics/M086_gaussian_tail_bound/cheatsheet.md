# M086 · Gaussian tail bound: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's measure-theoretic probability
(`Measure`, `μ.real`, `HasLaw`, `gaussianReal`, `mgf`, `Integrable`), the nonnegative reals `ℝ≥0` and their
cast into `ℝ`, the Chernoff bound, and the tactics `set`, `calc`, `congr 1`, `field_simp`.

**The maths.** A probability space is a set `Ω` of outcomes with a *measure* `μ` assigning each (measurable)
event `A ⊆ Ω` a probability `μ A ∈ [0, 1]`. A random variable is a function `X : Ω → ℝ`. Its *moment
generating function* (mgf) is $M(t) = \mathbb E[e^{tX}] = \int_\Omega e^{t X(\omega)}\,d\mu(\omega)$. For
$t \ge 0$, Markov's inequality applied to $e^{tX}$ gives the **Chernoff bound**
$\mu\{X \ge \varepsilon\} \le e^{-t\varepsilon} M(t)$. For $X \sim N(0, v)$ (mean 0, variance $v$),
$M(t) = e^{v t^2/2}$, so the bound is $e^{-t\varepsilon + v t^2/2}$. The exponent is a parabola in $t$,
minimised at $t = \varepsilon / v$, where it equals $-\varepsilon^2/(2v)$.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`apply`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before and
after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- `G : Prop` with `g : T → G` is a placeholder goal: the entry adds a fact `T` to the context and `g` uses it.
- Placeholders are written as Lean binders. `{Ω : Type}` is any type. A bracket such as `[IsFiniteMeasure μ]`
  is a requirement (a *type class* instance); each entry says what it means and where it comes from.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `{Ω : Type*}`, printed `Ω : Type u_1` | `Ω` is any type; `*` / `u_1` is a universe level you can ignore |
| `ℝ≥0` (also printed `NNReal`) | the nonnegative reals `{x : ℝ // 0 ≤ x}`; needs `open scoped NNReal` for the notation |
| `↑v` | the cast of `v : ℝ≥0` into `ℝ` (`NNReal.toReal v`); `(v : ℝ)` in source code |
| `Measure Ω` | a measure on `Ω`; here a probability distribution `μ` on the outcomes |
| `[MeasurableSpace Ω]`, `inst✝¹ : MeasurableSpace Ω` | the σ-algebra of events of `Ω`; `inst✝`, `inst✝¹` are unnamed instances (the `[…]` binders) |
| `IsProbabilityMeasure μ` | `μ Ω = 1`; it also gives `IsFiniteMeasure μ` and `NeZero μ`, which R11 and R8 need |
| `{ω \| ε ≤ X ω}` | the event `X ≥ ε`, a `Set Ω` |
| `μ.real A` | the probability of `A` as a real number (`μ A` itself lives in `[0, ∞]`) |
| `gaussianReal m v` | the normal distribution `N(m, v)` on `ℝ`: mean `m : ℝ`, variance `v : ℝ≥0` |
| `HasLaw X ν μ` | `X` has distribution `ν` under `μ` (`X ~ ν`) |
| `Measure.map X μ` (source: `μ.map X`) | the pushforward of `μ` along `X`: the distribution of `X` |
| `mgf X μ t` | the mgf `∫ exp (t * X ω) dμ`, a real number |
| `Integrable f μ` | `f` is measurable and `∫ \|f\| dμ < ∞` |
| `fun ω => Real.exp (t * X ω)` | the function `ω ↦ e^{t X(ω)}` |
| `Real.exp x` | `e^x` for `x : ℝ` |
| `t : ℝ := ε / ↑v` (inside a nested `by`: `t : ℝ := ⋯`) | a local definition made by `set` (R2): `t` is a name for `ε / ↑v`; `⋯` only hides the value |

---

## Part 1 · `gaussian_tail`

Statement: for a probability measure `μ`, a random variable `X` with `X ~ N(0, v)`, `v > 0` and `ε ≥ 0`,
`μ.real {ω | ε ≤ X ω} ≤ Real.exp (-ε ^ 2 / (2 * ↑v))`, that is $P(X \ge \varepsilon) \le e^{-\varepsilon^2/(2v)}$.

### Facts about the numbers

**R1 · `have hv' : (0 : ℝ) < v := hv`** changes the **context**: it restates `hv : 0 < v` (an inequality in
`ℝ≥0`) as `0 < ↑v` (in `ℝ`). The lemma behind it is `NNReal.coe_pos : 0 < ↑r ↔ 0 < r`; both sides unfold to
the same thing, so `hv` itself is accepted. Write the type `(0 : ℝ)`: it is what makes `v` print as `↑v`.
Placeholders: `(v : ℝ≥0) (hv : 0 < v)`.

| Before | After |
|---|---|
| `hv : 0 < v ⊢ G` | `hv' : 0 < ↑v ⊢ G` |

**R2 · `set t : ℝ := e with ht`** changes the **context and the goal**: it adds a local definition `t := e`
and the equation `ht : t = e`, and replaces every `e` in the goal by `t`. Later `rw [ht]` turns `t` back into
`e`. Placeholders: `(a b : ℝ)`, with `e := a / b`.

| Before | After |
|---|---|
| `⊢ P (a / b)` | `t : ℝ := a / b, ht : t = a / b ⊢ P t` |

**R3 · `div_nonneg`** changes the **context** (used in a `have`). The lemma is
`div_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a / b`. It holds in any ordered field; `ℝ` qualifies. Placeholders:
`(a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)`.

| Before | After |
|---|---|
| `ha : 0 ≤ a, hb : 0 ≤ b ⊢ G` | `hab : 0 ≤ a / b ⊢ G` |

**R4 · `h.le`** changes the **context**. `h.le` is `LT.lt.le h : a ≤ b` for `h : a < b` (dot notation: the
type of `h` is `a < b`, i.e. `LT.lt a b`, so `h.le` finds `LT.lt.le`). Placeholders: `(a b : ℝ) (h : a < b)`.

| Before | After |
|---|---|
| `h : a < b ⊢ G` | `h' : a ≤ b ⊢ G` |

### The mgf of a Gaussian

**R5 · `hX.map_eq`** changes the **context**. The lemma is `HasLaw.map_eq : HasLaw X ν μ → Measure.map X μ = ν`:
"`X ~ ν`" written as an equation of measures, the form R6 takes. Placeholders:
`{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (ν : Measure ℝ) (hX : HasLaw X ν μ)`.

| Before | After |
|---|---|
| `hX : HasLaw X ν μ ⊢ G` | `hmap : Measure.map X μ = ν ⊢ G` |

**R6 · `rw [mgf_gaussianReal hmap]`** changes the **goal**. The lemma is
`mgf_gaussianReal : Measure.map X μ = gaussianReal m v → ∀ t, mgf X μ t = Real.exp (m * t + ↑v * t ^ 2 / 2)`
(the mgf of `N(m, v)` is $e^{mt + vt^2/2}$). Given `hmap`, `rw` finds `t` in the goal itself. Placeholders:
`(m : ℝ) (v : ℝ≥0) (hmap : Measure.map X μ = gaussianReal m v) (t : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (mgf X μ t)` | `⊢ P (Real.exp (m * t + ↑v * t ^ 2 / 2))` |

**R7 · `simp`** (it uses `zero_mul : 0 * a = 0` and `zero_add : 0 + a = a`) changes the **goal**. With mean
`m = 0`, R6 leaves `0 * t + …`; `simp` removes it, and then closes an equation whose two sides have become
equal. Placeholders: `(t c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (0 * t + c)` | `⊢ P c` |

**R8 · `apply mgf_pos_iff.mp`** changes the **goal**. The lemma is
`mgf_pos_iff : 0 < mgf X μ t ↔ Integrable (fun ω => Real.exp (t * X ω)) μ` (it needs `[NeZero μ]`, which
`IsProbabilityMeasure μ` provides). `.mp` is the `→` direction; `apply` works backwards from the goal:
to prove integrability it suffices to prove the mgf is positive. As a term: `mgf_pos_iff.mp hpos`.
Placeholders: `[IsProbabilityMeasure μ] (X : Ω → ℝ) (t : ℝ)`.

| Before | After |
|---|---|
| `⊢ Integrable (fun ω => Real.exp (t * X ω)) μ` | `⊢ 0 < mgf X μ t` |

**R9 · `exact Real.exp_pos x`** **closes** the goal. The lemma is `Real.exp_pos : ∀ x, 0 < Real.exp x`. Write
`Real.exp_pos _` to let Lean find `x`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 < Real.exp x` | no goals |

### The Chernoff bound

**R10 · `calc`** changes the **goal list**: it proves `A ≤ C` by a chain `A ≤ B`, `B = C`, each step with its
own proof after `:=`. A step proved by `?_` becomes a new goal after the `calc`. Write the first line in
full, start the next ones with `_` (the previous right-hand side), and indent them under the first.
Placeholders: `(A B C : ℝ) (h1 : A ≤ B)`.

| Before | After |
|---|---|
| `⊢ A ≤ C` | `⊢ B = C` |

**R11 · `apply measure_ge_le_exp_mul_mgf a ht`** (Chernoff) changes the **goal**: the tail bound becomes
the integrability it needs. The lemma is
`measure_ge_le_exp_mul_mgf (ε : ℝ) : 0 ≤ t → Integrable (fun ω => Real.exp (t * X ω)) μ → μ.real {ω | ε ≤ X ω} ≤ Real.exp (-t * ε) * mgf X μ t`,
with `[IsFiniteMeasure μ]` (`μ Ω < ∞`; a probability measure is one). `ε` is explicit; `t` is read off
`ht` or the integrability proof. With both arguments, `measure_ge_le_exp_mul_mgf a ht hint` is a complete
proof, e.g. of the first step of a `calc` (R10). Placeholders: `[IsFiniteMeasure μ] (X : Ω → ℝ) (a t : ℝ)
(ht : 0 ≤ t) (hint : Integrable (fun ω => Real.exp (t * X ω)) μ)`.

Before (the goal contains `|`, so it is shown as a block):

```lean-goal
⊢ μ.real {ω | a ≤ X ω} ≤ Real.exp (-t * a) * mgf X μ t
```

| Before | After |
|---|---|
| the goal above | `⊢ Integrable (fun ω => Real.exp (t * X ω)) μ` |

### The exponent

**R12 · `rw [← Real.exp_add]`** changes the **goal**. The lemma is `Real.exp_add : exp (x + y) = exp x * exp y`;
right to left it merges a product of exponentials. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (Real.exp x * Real.exp y)` | `⊢ P (Real.exp (x + y))` |

**R13 · `congr 1`** changes the **goal**: `f a = f b` becomes `a = b` (same function on both sides; here
`f = Real.exp`). It closes the new goal by itself when it is `rfl` or a hypothesis. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ Real.exp (a + b) = Real.exp (b + a)` | `⊢ a + b = b + a` |

**R14 · `field_simp`** changes the **goal**: it multiplies out every denominator, leaving an equation without
`/`, which `ring` (TACTIC_STATES) then closes. It must know each denominator is nonzero: it looks for
hypotheses such as `hb : b ≠ 0` or `hb : 0 < b` in the context. With no such fact the denominator stays.
Placeholders: `(a b : ℝ) (hb : 0 < b)`.

| Before | After |
|---|---|
| `hb : 0 < b ⊢ a / (3 * b) + a / b = 4 * a / (3 * b)` | `⊢ a * (1 + 3) = a * 4` |

### Worked combinations (on objects that are not the exercise's)

**W1: an optimised exponent.** For an mgf `exp (c t²)` the Chernoff exponent `-t a + c t²` is minimised at
`t = a / (2c)`. With `hc : 0 < c` in context, `field_simp` then `ring`:

```lean-goal
⊢ -(a / (2 * c)) * a + c * (a / (2 * c)) ^ 2 = -a ^ 2 / (4 * c)
⊢ a ^ 2 * (-2 + 1) * 4 = -(a ^ 2 * 2 ^ 2)
```

**W2: Chernoff at the fixed value `t = 1` for `Y ~ N(m, w)`.** `hmgf` from R5 + R6, `hint` from R8 + `rw [hmgf]`
+ R9, then a `calc` (R10) whose first step is R11 (with `zero_le_one : 0 ≤ 1`) and whose second step is left
as `?_`. That goal, then after `rw [hmgf, ← Real.exp_add]` (R12), then after `congr 1` (R13); `ring` closes it:

```lean-goal
⊢ Real.exp (-1 * a) * mgf Y μ 1 = Real.exp (-a + m + ↑w / 2)
⊢ Real.exp (-1 * a + (m * 1 + ↑w * 1 ^ 2 / 2)) = Real.exp (-a + m + ↑w / 2)
⊢ -1 * a + (m * 1 + ↑w * 1 ^ 2 / 2) = -a + m + ↑w / 2
```

The exercise differs in two ways: `t` is the optimised `ε / ↑v` (so you need `0 ≤ t` from R3, R4, and
`field_simp` (R14) before `ring`), and the mean is `0` (R7).

---

## Traps

- `hv : 0 < v` is about `ℝ≥0`; `field_simp` and `div_nonneg` work in `ℝ` and want facts about `↑v`. State
  `have hv' : (0 : ℝ) < v := hv` (R1) early.
- Chernoff (R11) needs integrability of `ω ↦ exp (t X ω)` as a separate argument. Do not try to prove it from
  the definition of `Integrable`: get it from the mgf being positive (R8, R9).
- Prove `hmgf : mgf X μ t = Real.exp (↑v * t ^ 2 / 2)` once, as a `have`; you use it twice (for `hint` and
  in the last `calc` step).
- `t` from `set` is a local definition: `ring` and `field_simp` treat it as an unknown. `rw [ht]` (with
  `ht : t = ε / ↑v`) before `field_simp`, otherwise the exponent identity is false for a general `t`.
- `-t * ε` is `(-t) * ε`, and `-ε ^ 2` is `-(ε ^ 2)`: `^` binds tighter than unary `-`.
- `μ.map X` and `Measure.map X μ` are the same term; the infoview prints the second form.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `0 < ↑v` in `ℝ` from `0 < v` in `ℝ≥0` | `have hv' : (0 : ℝ) < v := hv` | R1 |
| name the optimal parameter | `set t : ℝ := ε / v with ht` | R2 |
| `0 ≤ a / b` | `div_nonneg ha hb` | R3 |
| `a ≤ b` from `a < b` | `h.le` | R4 |
| `X ~ ν` as `Measure.map X μ = ν` | `hX.map_eq` | R5 |
| mgf of `N(m, v)` | `rw [mgf_gaussianReal hX.map_eq]` | R5, R6 |
| drop `0 * t + …` | `simp` | R7 |
| integrability of `exp (t X)` | `mgf_pos_iff.mp (by rw [hmgf]; exact Real.exp_pos _)` | R8, R9 |
| chain `≤` and `=` | `calc A ≤ B := p₁`, next line `_ = C := p₂` (or `?_`) | R10 |
| Chernoff: $P(X \ge a) \le e^{-ta} M(t)$ | `measure_ge_le_exp_mul_mgf a ht hint` | R11 |
| `exp x * exp y → exp (x + y)` | `rw [← Real.exp_add]` | R12 |
| `exp a = exp b` → `a = b` | `congr 1` | R13 |
| clear denominators | `field_simp` (nonzero facts in context) | R14 |
| polynomial identity | `ring` | TACTIC_STATES |
| optimal `t` for $e^{-t\varepsilon + v t^2/2}$ | $t = \varepsilon / v$, exponent $-\varepsilon^2 / (2v)$ | |
