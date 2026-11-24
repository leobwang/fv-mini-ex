# M162 · Fermi–Dirac occupation: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real exponential `Real.exp`,
order tactics (`positivity`, `linarith`, `gcongr`), `field_simp`, the predicate `Antitone`, and limits
written with filters (`Filter.Tendsto`, `atTop`, `atBot`, `𝓝`).

The function: `fermi β μ ε = 1 / (exp (β * (ε - μ)) + 1)`, the mean occupation of a single-particle level
of energy `ε` at inverse temperature `β = 1 / (k_B T)` (`k_B` Boltzmann's constant, `T` temperature) and
chemical potential `μ`. All four variables are real numbers (`ℝ`).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`simp`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. `G : Prop` is a goal the step does not touch (used when only the context
  changes).
- Placeholders are written as Lean binders. `{α : Type}` is any type. Each entry says which familiar types
  meet a type-class bracket.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `rexp x` | `Real.exp x` = $e^x$ (the infoview prints `Real.exp` as `rexp`; with `open Real`, as in the exercise, you may also type `rexp` yourself) |
| `x⁻¹` | the inverse `1 / x` (for `x = 0` Lean defines `0⁻¹ = 0`) |
| `this` | the name `have := …` gives a fact when you give none |
| `Antitone f` | `∀ ⦃a b⦄, a ≤ b → f b ≤ f a`: `f` is non-increasing |
| `∀ ⦃a b⦄, …` | strict-implicit binders: `a b` are filled in only once a later explicit argument (here `a ≤ b`) is given; `intro a b hab` still introduces them |
| `fermi β μ` | `fermi` with two arguments given: the function `ε ↦ fermi β μ ε` |
| `Filter α` | a *filter* on `α`: a family of sets read as "eventually"; it encodes a limit point |
| `atTop` / `atBot` | the filters "for all large enough `t`" (`t → +∞`) / "for all small enough `t`" (`t → -∞`) |
| `𝓝 L` | the neighborhood filter of the point `L` ("arbitrarily close to `L`") |
| `Tendsto f l₁ l₂` | `f` maps `l₁` into `l₂`; `Tendsto f atTop (𝓝 L)` is $\lim_{t\to\infty} f(t) = L$, `Tendsto f atTop atBot` is $f(t) \to -\infty$ as $t \to \infty$ |
| `fun x => c` | the constant function with value `c` |
| `k ∘ f` | composition `fun x => k (f x)` |
| `f / k` (`f k` functions) | the pointwise quotient `fun x => f x / k x` |
| `t * -3` | `t * (-3)`; Lean drops the parentheses |
| `case refine_1`, `case refine_2`, `case a`, `case ha` | names `refine ⟨?_, ?_⟩` and `gcongr` give the goals they leave; ignore them |

---

## Part 1 · `fermi_bounds`

Statement: `0 < fermi β μ ε ∧ fermi β μ ε < 1` for all real `β μ ε`. After unfolding, both halves are about
`1 / (e + 1)` with `e = rexp (β * (ε - μ)) > 0`. Split with `refine ⟨?_, ?_⟩` (TACTIC_STATES).

**R1 · `unfold g`** changes the **goal**: every occurrence of the defined name `g` is replaced by its body.
In the exercise, `unfold fermi`. Placeholders: `def g (a t : ℝ) : ℝ := a * t + 1`, `(a t : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (g a t)` | `⊢ P (a * t + 1)` |

**R2 · `have := Real.exp_pos x`** changes the **context**: it adds `this : 0 < rexp x`. The lemma is
`Real.exp_pos : ∀ x : ℝ, 0 < rexp x`. The argument `x` must be the exact expression inside `rexp` in your
goal, so that `linarith` (R5) sees the same atom. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `this : 0 < rexp x ⊢ G` |

**R3 · `positivity`** **closes** a goal `0 < e`, `0 ≤ e` or `e ≠ 0` by looking at the shape of `e`: it knows
`rexp _ > 0`, numerals, and that `+`, `*`, `/` of positive things are positive. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `x : ℝ ⊢ 0 < 1 / (rexp x + 1)` | no goals |

**R4 · `rw [div_lt_one hb]`** changes the **goal**. The lemma is
`div_lt_one : 0 < b → (a / b < 1 ↔ a < b)`; `rw` with an `↔` replaces one side by the other. It holds in
any ordered field (`ℝ`, `ℚ`). Write `rw [div_lt_one (by positivity)]` to prove `0 < b` in place.
Placeholders: `(a b : ℝ) (hb : 0 < b)`.

| Before | After |
|---|---|
| `⊢ a / b < 1` | `⊢ a < b` |

**R5 · `linarith`** **closes** a goal that is a linear consequence (`<`, `≤`, `=`, sums, numeric multiples)
of context hypotheses. Any non-linear piece such as `rexp x` is treated as an unknown. Placeholders:
`(x : ℝ) (hx : 0 < rexp x)`.

| Before | After |
|---|---|
| `hx : 0 < rexp x ⊢ 1 < rexp x + 1` | no goals |

**W1** chains R2, R4 (side goal by R3), R5 on `rexp t / (rexp t + 1) < 1`:

```lean-goal
⊢ rexp t / (rexp t + 1) < 1
⊢ rexp t < rexp t + 1
```

---

## Part 2 · `particle_hole`

Statement: `fermi β μ (μ + x) + fermi β μ (μ - x) = 1`. With `y = β * (μ + x - μ)`, the second exponent is
`-y` up to ring arithmetic, and $\frac{1}{e^y+1} + \frac{1}{e^{-y}+1} = 1$. Plan: prove
`h : rexp (β * (μ - x - μ)) = (rexp (β * (μ + x - μ)))⁻¹` first, `rw [h]`, then clear denominators.

**R6 · `rw [← Real.exp_neg]`** changes the **goal**. The lemma is `Real.exp_neg : rexp (-x) = (rexp x)⁻¹`;
`←` uses it right to left, turning an inverse of `rexp` into `rexp` of a negation. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (rexp x)⁻¹` | `⊢ P (rexp (-x))` |

**R7 · `ring_nf`** **closes** (or simplifies) the **goal**: it puts every ring expression into a normal form,
including arguments of functions such as `rexp`. If both sides of an equation then read the same, it closes
it. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ rexp (c * (a - b)) = rexp (-(c * (b - a)))` | no goals |

**R8 · `field_simp`** changes the **goal**: it multiplies out every denominator it can prove nonzero and
leaves an equation with no `/` or `⁻¹`. It proves nonzero-ness from context facts (`0 < a`, `a ≠ 0`) or by
`positivity`; `rexp _ + 1` and `rexp _` are handled automatically. The exact form it leaves (which side, which
order) is not predictable: finish with R9. Placeholders: `(a b c : ℝ) (ha : 0 < a) (hb : 0 < b)`.

| Before | After |
|---|---|
| `⊢ 1 / a + 1 / b = c` | `⊢ b + a = a * b * c` |

**R9 · `ring`** **closes** an identity of commutative rings, treating `rexp x` as an unknown. Placeholders:
`(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ (rexp x + 1) * (1 + rexp x) = 1 + rexp x + rexp x * (rexp x + 1)` | no goals |

**W2** uses R6 left to right, then R8 closes the goal by itself:

```lean-goal
⊢ rexp (-t) * rexp t = 1
⊢ (rexp t)⁻¹ * rexp t = 1
```

---

## Part 3 · `fermi_antitone`

Statement: with `hβ : 0 ≤ β`, `Antitone (fermi β μ)`: a higher level is less occupied.

**R10 · `intro a b hab`** changes the **context and the goal**: `Antitone f` unfolds to
`∀ ⦃a b⦄, a ≤ b → f b ≤ f a`, so `intro` introduces the two points and the order hypothesis. Then
`unfold fermi` (R1). Placeholders: `(f : ℝ → ℝ)`.

| Before | After |
|---|---|
| `⊢ Antitone f` | `a b : ℝ, hab : a ≤ b ⊢ f b ≤ f a` |

**R11 · `gcongr`** ("generalized congruence") changes the **goal list**. On `lhs ≤ rhs` where both sides have
the same shape, it peels the shape off layer by layer: `1 / _` is decreasing on positives (positivity of the
denominators is checked automatically), `_ + 1` and `rexp` are increasing, `c * _` is increasing when
`0 ≤ c`. It closes each remaining goal from a context hypothesis if one matches; otherwise the goal stays.
Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ 1 / (rexp y + 1) ≤ 1 / (rexp x + 1)` | `⊢ x ≤ y` |

**R12 · `gcongr` side goal** changes the **goal list**: going through `c * _` needs `0 ≤ c`. If a hypothesis
`hc : 0 ≤ c` is in the context, `gcongr` uses it silently (this is why `hβ` matters in the exercise);
otherwise `0 ≤ c` is left for you. Placeholders: `(c x y : ℝ) (h : x ≤ y)`.

| Before | After |
|---|---|
| `⊢ rexp (c * x) ≤ rexp (c * y)` | `⊢ 0 ≤ c` |

**W3** (`q c t = rexp (-(c * t))`, `hc : 0 ≤ c`): R10, R1, then `gcongr` closes everything:

```lean-goal
⊢ Antitone (q c)
⊢ q c b ≤ q c a
⊢ rexp (-(c * b)) ≤ rexp (-(c * a))
```

---

## Part 4 · `fermi_zero_T`

Statement: with `h : ε < μ`, `Tendsto (fun β => fermi β μ ε) atTop (𝓝 1)`, i.e.
$\lim_{\beta\to\infty} f(\varepsilon) = 1$: at zero temperature levels below `μ` are full. Build the limit
inside out as `have` facts (each entry below adds one to the **context**):

$$\beta(\varepsilon-\mu) \to -\infty \;\Rightarrow\; e^{\beta(\varepsilon-\mu)} \to 0 \;\Rightarrow\;
e^{\beta(\varepsilon-\mu)} + 1 \to 0 + 1 \;\Rightarrow\; \frac{1}{e^{\beta(\varepsilon-\mu)}+1} \to \frac{1}{0+1}.$$

**R13 · `tendsto_id`**: `Tendsto id l l`. With `l = atTop`, the identity `t ↦ t` tends to `+∞`. **Closes**:

| Before | After |
|---|---|
| `⊢ Tendsto (fun t => t) atTop atTop` | no goals |

**R14 · `tendsto_const_nhds`**: `Tendsto (fun _ => c) l (𝓝 c)`, a constant tends to itself. Its arguments are
implicit; `(x := c)` names the constant when Lean cannot infer it. Changes the **context**. Placeholders:
`{α : Type} (l : Filter α) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `h : Tendsto (fun x => c) l (𝓝 c) ⊢ G` |

**R15 · `Filter.Tendsto.atTop_mul_neg`**:
`C < 0 → Tendsto f l atTop → Tendsto k l (𝓝 C) → Tendsto (fun x => f x * k x) l atBot` ($+\infty$ times a
negative limit is $-\infty$). Dot notation: `hf.atTop_mul_neg hC hk` puts `hf` into the first explicit
argument whose type is a `Tendsto`. Changes the **context**. It holds in any ordered field (`ℝ`).
Placeholders: `{α : Type} {l : Filter α} (f k : α → ℝ) (C : ℝ) (hC : C < 0)`.

| Before | After |
|---|---|
| `⊢ G` | `h : Tendsto (fun x => f x * k x) l atBot ⊢ G` |

**R16 · `Real.tendsto_exp_atBot`**: `Tendsto rexp atBot (𝓝 0)`, $e^t \to 0$ as $t \to -\infty$. **Context**:

| Before | After |
|---|---|
| `⊢ G` | `h : Tendsto rexp atBot (𝓝 0) ⊢ G` |

**R17 · `Filter.Tendsto.comp`**: `Tendsto k y z → Tendsto f x y → Tendsto (k ∘ f) x z` (limits compose:
the outer function's limit is taken at the inner function's target). **Context**. Placeholders:
`{α β γ : Type} (f : α → β) (k : β → γ) (x : Filter α) (y : Filter β) (z : Filter γ)`.

| Before | After |
|---|---|
| `⊢ G` | `h : Tendsto (k ∘ f) x z ⊢ G` |

**R18 · `Filter.Tendsto.add_const`**: `(b : ℝ) → Tendsto f l (𝓝 a) → Tendsto (fun x => f x + b) l (𝓝 (a + b))`
(stated for `ℝ`; Mathlib's version works in any type `M` with a topology and a continuous `+`);
written `hf.add_const b`. **Context**. Placeholders: `{α : Type} {l : Filter α} (f : α → ℝ) (a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `h : Tendsto (fun x => f x + b) l (𝓝 (a + b)) ⊢ G` |

**R19 · `Filter.Tendsto.div`**: `Tendsto f l (𝓝 a) → Tendsto k l (𝓝 b) → b ≠ 0 → Tendsto (f / k) l (𝓝 (a / b))`;
written `hf.div hk hb`. The `b ≠ 0` argument for `b = 0 + 1` is `(by norm_num)`. **Context**. It holds in any
field with a topology where `*` and `⁻¹` are continuous (`ℝ`, `ℂ`). Placeholders:
`{α : Type} {l : Filter α} (f k : α → ℝ) (a b : ℝ) (hb : b ≠ 0)`.

| Before | After |
|---|---|
| `⊢ G` | `h : Tendsto (f / k) l (𝓝 (a / b)) ⊢ G` |

**R20 · `simp only [Function.comp_def] at h`** changes the **context**: inside `h`, `(k ∘ f) x` becomes
`k (f x)`. `Function.comp_def : k ∘ f = fun x => k (f x)`. Placeholders: `(f k : ℝ → ℝ)`,
`P : (ℝ → ℝ) → Prop`.

| Before | After |
|---|---|
| `h : P fun x => (k ∘ f) x + 1 ⊢ P fun x => k (f x) + 1` | `h : P fun x => k (f x) + 1 ⊢ P fun x => k (f x) + 1` |

**R21 · `simp only [zero_add, div_one] at h`** changes the **context**: `zero_add : 0 + a = a`,
`div_one : a / 1 = a`, so `1 / (0 + 1)` becomes `1`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `h : P (a / (0 + 1)) ⊢ P a` | `h : P a ⊢ P a` |

**R22 · `exact h` up to unfolding** **closes** the goal when `h`'s type is the goal once definitions are
unfolded and `fun`s are applied. So `h3 : Tendsto ((fun x => 1) / fun x => rexp (x * (ε - μ)) + 1) …` closes
`Tendsto (fun β => fermi β μ ε) …` with no rewriting: `f / k` is pointwise and `fermi` unfolds. Placeholders:
`def g (a t : ℝ) : ℝ := a * t + 1`.

| Before | After |
|---|---|
| `h : P (a * t + 1) ⊢ P (g a t)` | no goals |

**W4** (`Tendsto (fun t => rexp (t * (-3)) + 2) atTop (𝓝 2)`): R13 and R14 into R15 give
`h1 : Tendsto (fun t => t * -3) atTop atBot`; R16, R17, R18 give
`h2 : Tendsto (fun x => (rexp ∘ fun t => t * -3) x + 2) atTop (𝓝 (0 + 2))`; R20 and R21 turn it into
`h2 : Tendsto (fun x => rexp (x * -3) + 2) atTop (𝓝 2)`. The goal stays

```lean-goal
⊢ Tendsto (fun t => rexp (t * -3) + 2) atTop (𝓝 2)
```

throughout, and `exact h2` closes it.

---

## Traps

- `have := Real.exp_pos (β * (ε - μ))` must name the exponent exactly as it appears in the goal (after
  `unfold fermi`), or `linarith` treats the two `rexp` terms as different unknowns.
- `exp_neg` gives `(rexp y)⁻¹`, not `1 / rexp y`. State your `have` with `⁻¹` so `rw [← Real.exp_neg]` applies.
- In `particle_hole` the exponent is `β * (μ - x - μ)`, not `β * (-x)`: Lean does not simplify it. `rw [h]`
  needs `h`'s left side to match that text exactly; let `ring_nf` (R7) do the arithmetic inside `rexp`.
- `field_simp` output has no fixed shape; always follow it with `ring`, never with a hand-written `rw`.
- `fermi_antitone`: keep `hβ` in the context before `gcongr`; without it `gcongr` leaves `0 ≤ β` (R12).
- `Antitone f` is `f b ≤ f a` for `a ≤ b`: the sides are swapped relative to `Monotone`.
- In `(tendsto_const_nhds (x := (1 : ℝ))).div …` spell out the constant and its type, so Lean knows the
  numerator is the real constant `1` before it reads the rest.
- The `Tendsto` facts come out as `(rexp ∘ fun β => …) x` and `𝓝 (1 / (0 + 1))`; clean them with R20, R21
  in the hypothesis (`at h3`), then `exact h3` (R22).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| replace `fermi` by its body | `unfold fermi` | R1 |
| `0 < rexp y` as a fact | `have := Real.exp_pos y` | R2 |
| `0 < 1 / (rexp y + 1)`, `0 < rexp y + 1` | `positivity` | R3 |
| `a / b < 1` → `a < b` | `rw [div_lt_one (by positivity)]` | R4 |
| linear goal from facts | `linarith` | R5 |
| `(rexp y)⁻¹` → `rexp (-y)` | `rw [← Real.exp_neg]` | R6 |
| `rexp u = rexp v` with `u = v` by algebra | `ring_nf` | R7 |
| clear denominators | `field_simp` | R8 |
| finish a ring identity | `ring` | R9 |
| open `Antitone f` | `intro a b hab` | R10 |
| compare two same-shape sides | `gcongr` (keep `0 ≤ c` facts in context) | R11, R12 |
| `t → ∞` | `tendsto_id` | R13 |
| constant limit | `tendsto_const_nhds (x := c)` | R14 |
| `(+∞) · (C < 0) → -∞` | `hf.atTop_mul_neg hC hk` | R15 |
| `exp → 0` at `-∞` | `Real.tendsto_exp_atBot` | R16 |
| compose limits | `hk.comp hf` | R17 |
| `f + b` | `hf.add_const b` | R18 |
| `f / k` | `hf.div hk (by norm_num)` | R19 |
| clean `∘`, `0 + _`, `_ / 1` in a hypothesis | `simp only [Function.comp_def, zero_add, div_one] at h` | R20, R21 |
| hypothesis equals goal after unfolding | `exact h` | R22 |
| see the state | infoview | |
