# M111 · Forward difference via Taylor: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`refine ⟨x, ?_⟩`, `have`, `rw [h]`, `exact`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real analysis: smoothness classes
(`ContDiff`), derivatives (`deriv`, `derivWithin`, `iteratedDeriv`), Taylor polynomials
(`taylorWithinEval`) and Taylor's theorem with Lagrange remainder; intervals (`Set.Icc`, `Set.uIcc`);
absolute values; and the tactics `linarith`, `field_simp`, `linear_combination`, `gcongr`.

The mathematics. Taylor's theorem of degree 1 at `x` with Lagrange remainder: for some `ξ` strictly
between `x` and `x + h`, $f(x+h) - (f(x) + h f'(x)) = f''(\xi)\,h^2/2$. Divide by `h > 0`:
$\frac{f(x+h)-f(x)}{h} - f'(x) = f''(\xi)\,h/2$, and $|f''(\xi)| \le M$ gives the bound $M h/2$.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`apply`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal.
- Placeholders are written as Lean binders: `(f : ℝ → ℝ)`, `(a b : ℝ)`, `(s : Set ℝ)`, `(n : ℕ)`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that. States
  containing an absolute value `|…|` are shown in a `lean-goal` block instead of a table (a `|` would split
  the table cell).

## Reading the goals

| You see | It means |
|---|---|
| `ContDiff ℝ k f` | `f : ℝ → ℝ` is `k` times continuously differentiable on all of `ℝ` |
| `ContDiffOn ℝ k f s` | the same, but only on the set `s` |
| `k : WithTop ℕ∞` | the smoothness order: a natural number, `∞` (smooth) or `ω` (analytic). The `2` in `ContDiff ℝ 2 f` lives here |
| `Differentiable ℝ f`, `DifferentiableAt ℝ f x` | `f` is differentiable everywhere / at the point `x`. The first is `∀ x, DifferentiableAt ℝ f x` |
| `deriv f x` | $f'(x)$ (Mathlib defines it as `0` where `f` is not differentiable) |
| `iteratedDeriv n f y` | $f^{(n)}(y)$, the `n`-th derivative; `iteratedDeriv 2 f y` is $f''(y)$ |
| `derivWithin f s x` | the derivative of `f` at `x` using only points of `s` (a one-sided derivative at an endpoint of an interval) |
| `iteratedDerivWithin n f s x` | the `n`-th derivative within `s` |
| `UniqueDiffWithinAt ℝ s x` | `s` is fat enough near `x` that a derivative within `s` is unique (true for `[a, b]` with `a < b`) |
| `UniqueDiffOn ℝ s` | `∀ x ∈ s, UniqueDiffWithinAt ℝ s x` |
| `Set.Icc a b` | the closed interval $[a, b]$; `x ∈ Set.Icc a b` is `a ≤ x ∧ x ≤ b` |
| `Set.uIcc a b` | the closed interval between `a` and `b` in either order: $[\min(a,b), \max(a,b)]$ |
| `Set.uIoo a b` | the open interval between `a` and `b` in either order |
| `taylorWithinEval f n s x₀ x` | the degree-`n` Taylor polynomial of `f` at `x₀` (derivatives taken within `s`), evaluated at `x` |
| `n.factorial`, `Nat.factorial 0` | $n!$, a natural number |
| `↑n`, `↑(n + 1).factorial` | a natural number cast into `ℝ` |
| `c • d` | scalar times vector; for `c d : ℝ` it is just `c * d` |
| `c⁻¹` | the inverse $1/c$ (in `ℝ`, `0⁻¹ = 0`) |
| `↑0 + 1`, `0 + 1`, `1 + 1`, `(1 + 1).factorial` | numerals Lean has not computed yet; `norm_num` computes them (R13) |
| `ξ`, `hξ` | the intermediate point given by Taylor's theorem and its equation (names you choose in `obtain`) |
| `\|a\|` | the absolute value of `a` |
| `∃ y ∈ S, Q y` | `∃ y, y ∈ S ∧ Q y` |
| `∀ (y : ℝ), Q y` | how Lean prints `∀ y, Q y` (the hypothesis `hM`); `hM ξ : Q ξ` |
| `lemma (n := 1) (x₀ := a)` | named arguments: fill the lemma's implicit variables `n`, `x₀` by name (R2) |
| `hab.le`, `hh.ne'` | from `hab : a < b`: `a ≤ b`; from `hh : 0 < h`: `h ≠ 0` (dot notation on a `<` fact) |
| `case hbc` | a goal `gcongr` left over (the name is internal) |

---

## Part 1 · `taylor_one` (milestone)

Statement: `∃ ξ, f (x + h) - (f x + h * deriv f x) = iteratedDeriv 2 f ξ * h ^ 2 / 2`. This is Taylor's
theorem of degree 1 with its coefficients read off. Mathlib gives it as a degree-`n` Taylor polynomial
with derivatives *within* the interval; the work is to turn that into `f x + h * deriv f x`.

### Getting Taylor's theorem into the context

**R1 · `obtain ⟨y, -, hy⟩ := h`** changes the **context**: `h : ∃ y ∈ S, Q y` is replaced by a witness `y`
and `hy : Q y`. The `-` throws away the part `y ∈ S`. For a plain `∃ y, Q y`, write `obtain ⟨y, hy⟩ := h`.
Placeholders: `{α : Type} (S : Set α) (Q : α → Prop) (G : Prop)`.

| Before (`h : ∃ y ∈ S, Q y` in the context) | After (`h` is gone) |
|---|---|
| `⊢ G` | `y : α, hy : Q y ⊢ G` |

**R2 · `taylor_mean_remainder_lagrange_iteratedDeriv`** changes the **context** (used with R1). The lemma:

```
taylor_mean_remainder_lagrange_iteratedDeriv {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} :
  x₀ ≠ x → ContDiffOn ℝ (↑n + 1) f (Set.uIcc x₀ x) →
  ∃ x' ∈ Set.uIoo x₀ x,
    f x - taylorWithinEval f n (Set.uIcc x₀ x) x₀ x
      = iteratedDeriv (n + 1) f x' * (x - x₀) ^ (n + 1) / ↑(n + 1).factorial
```

`x₀` is the expansion point and `x` the evaluation point. The lemma's own variable names clash with yours,
so pass them by name: `(n := n) (x₀ := a) (x := b)`. Placeholders: `(f : ℝ → ℝ) (a b : ℝ) (n : ℕ)
(hne : a ≠ b) (hf : ContDiffOn ℝ (↑n + 1) f (Set.uIcc a b))`.

| Before | After `obtain ⟨ξ, -, hξ⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := n) (x₀ := a) (x := b) hne hf` |
|---|---|
| `hne : a ≠ b ⊢ G` | `ξ : ℝ, hξ : f b - taylorWithinEval f n (Set.uIcc a b) a b = iteratedDeriv (n + 1) f ξ * (b - a) ^ (n + 1) / ↑(n + 1).factorial ⊢ G` |

**R3 · `hf.contDiffOn`** (lemma `ContDiff.contDiffOn`) **closes** a goal `ContDiffOn ℝ k f s` from
`hf : ContDiff ℝ k f`: smooth everywhere implies smooth on any `s`. Use it as the second argument of R2.
Placeholders: `(f : ℝ → ℝ) (k : WithTop ℕ∞) (s : Set ℝ)`. Lean accepts `hf : ContDiff ℝ 2 f` where
`ContDiffOn ℝ (↑1 + 1) f _` is asked, because `↑1 + 1` computes to `2`.

| Before | After |
|---|---|
| `hf : ContDiff ℝ k f ⊢ ContDiffOn ℝ k f s` | closed by `exact hf.contDiffOn` |

**R4 · `linarith`** **closes** a goal that follows linearly from the hypotheses: `<`, `≤`, `=`, and also `≠`.
Use it for the first argument of R2 (`x ≠ x + h` from `0 < h`) and the side goals of R6 and R9. Placeholders:
`(a t : ℝ) (ht : 0 < t)`, goal `a ≠ a + t`.

### The one coefficient: `iteratedDerivWithin 1 f (Set.uIcc x (x + h)) x = deriv f x`

The Taylor coefficient is a derivative within the interval. At the endpoint `x` it equals `deriv f x`,
because `f` is differentiable at `x` and `[x, x + h]` is a genuine interval. Prove this as a fact
`hd` with `have` (TACTIC_STATES, "Adding facts"), using R5 → R6 → R8 with R7, R9, R10.

**R5 · `rw [iteratedDerivWithin_one]`** changes the **goal**. Lemma: `iteratedDerivWithin 1 f s =
derivWithin f s`. Placeholders: `(f : ℝ → ℝ) (s : Set ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (iteratedDerivWithin 1 f s a)` | `⊢ P (derivWithin f s a)` |

**R6 · `rw [Set.uIcc_of_le]`** changes the **goal list**. Lemma: `a ≤ b → Set.uIcc a b = Set.Icc a b`. The goal
is rewritten and a side goal `a ≤ b` is added; `rw [Set.uIcc_of_le (by linarith)]` closes it on the spot.
Needed because R9 is about `Set.Icc`. Placeholders: `(a b : ℝ) (P : Set ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (Set.uIcc a b)` | `⊢ P (Set.Icc a b)`, `⊢ a ≤ b` |

**R7 · `hf.differentiable`** (lemma `ContDiff.differentiable : ContDiff 𝕜 k f → k ≠ 0 → Differentiable 𝕜 f`)
changes the **goal**: `apply` leaves the side goal `k ≠ 0` in `WithTop ℕ∞`, which `norm_num` closes. As a term,
`hf.differentiable (by norm_num) x : DifferentiableAt ℝ f x` (a `Differentiable` fact applied to a point).
`𝕜` is the scalar field, here `ℝ`. Placeholders: `(f : ℝ → ℝ) (hf : ContDiff ℝ 3 f)`.

| Before | After `apply hf.differentiable` |
|---|---|
| `⊢ Differentiable ℝ f` | `⊢ 3 ≠ 0` |

**R8 · `apply hd.derivWithin`** (lemma `DifferentiableAt.derivWithin : DifferentiableAt 𝕜 f x →
UniqueDiffWithinAt 𝕜 s x → derivWithin f s x = deriv f x`) changes the **goal**: the equation becomes the
uniqueness condition on `s`. Placeholders: `(f : ℝ → ℝ) (s : Set ℝ) (x : ℝ) (hd : DifferentiableAt ℝ f x)`.

| Before | After |
|---|---|
| `⊢ derivWithin f s x = deriv f x` | `⊢ UniqueDiffWithinAt ℝ s x` |

**R9 · `apply uniqueDiffOn_Icc hab`** (lemma `uniqueDiffOn_Icc : a < b → UniqueDiffOn ℝ (Set.Icc a b)`)
changes the **goal** to the membership `x ∈ Set.Icc a b`, because `UniqueDiffOn ℝ s` is
`∀ x ∈ s, UniqueDiffWithinAt ℝ s x`. As a term: `uniqueDiffOn_Icc hab x hx`. Placeholders:
`(a b x : ℝ) (hab : a < b)`.

| Before | After |
|---|---|
| `⊢ UniqueDiffWithinAt ℝ (Set.Icc a b) x` | `⊢ x ∈ Set.Icc a b` |

**R10 · `refine ⟨le_rfl, ?_⟩`** changes the **goal**: `a ∈ Set.Icc a b` is the pair `a ≤ a ∧ a ≤ b`; `le_rfl`
proves `a ≤ a`. As a term: `⟨le_rfl, hab⟩`, or `⟨le_rfl, by linarith⟩`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ∈ Set.Icc a b` | `⊢ a ≤ b` |

### Reading off the Taylor polynomial in `hξ`

**R11 · `rw [taylorWithinEval_succ]`** changes the **goal** (or, with `at hξ`, the hypothesis). Lemma:
`taylorWithinEval f (n + 1) s x₀ x = taylorWithinEval f n s x₀ x + (((↑n + 1) * ↑n.factorial)⁻¹ * (x - x₀) ^ (n + 1)) • iteratedDerivWithin (n + 1) f s x₀`.
It also rewrites `taylorWithinEval f 1 …`, reading `1` as `0 + 1`. Placeholders:
`(f : ℝ → ℝ) (n : ℕ) (s : Set ℝ) (a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (taylorWithinEval f (n + 1) s a b)` | `⊢ P (taylorWithinEval f n s a b + (((↑n + 1) * ↑n.factorial)⁻¹ * (b - a) ^ (n + 1)) • iteratedDerivWithin (n + 1) f s a)` |

**R12 · `rw [taylor_within_zero_eval] at h`** changes the **context**: `rw … at h` rewrites the hypothesis
`h` instead of the goal. Lemma: `taylorWithinEval f 0 s x₀ x = f x₀` (degree 0 is the value). Placeholders:
`(f : ℝ → ℝ) (s : Set ℝ) (a b : ℝ)`.

| Before | After |
|---|---|
| `h : P (taylorWithinEval f 0 s a b) ⊢ P (f a)` | `h : P (f a) ⊢ P (f a)` |

After R11, R12 and `rw [hd] at hξ`, the hypothesis still has `0 + 1`, `Nat.factorial 0`, `1 + 1` and `•`.

**R13 · `norm_num at h`** changes the **context**: it computes the numerals in `h` (`↑0 + 1 = 1`, `0! = 1`,
`(1 + 1)! = 2`, `x + h - x = h`) and turns `c • d` into `c * d`. After it, `hξ` is the milestone's
statement exactly. Placeholders: `(a b d : ℝ)`.

| Before | After |
|---|---|
| `h : P ((((↑0 + 1) * ↑(Nat.factorial 0))⁻¹ * (a + b - a) ^ (0 + 1)) • d) ⊢ P (b * d)` | `h : P (b * d) ⊢ P (b * d)` |

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: the degree-2 polynomial.** `rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval]`
(R11 twice, then R12 on the goal), then `norm_num` (R13 on the goal; it also applies R5 by itself):

```lean-goal
⊢ taylorWithinEval f 2 s a b = c
⊢ f a + (((↑0 + 1) * ↑(Nat.factorial 0))⁻¹ * (b - a) ^ (0 + 1)) • iteratedDerivWithin (0 + 1) f s a + (((↑1 + 1) * ↑(Nat.factorial 1))⁻¹ * (b - a) ^ (1 + 1)) • iteratedDerivWithin (1 + 1) f s a = c
⊢ f a + (b - a) * derivWithin f s a + 1 / 2 * (b - a) ^ 2 * iteratedDerivWithin 2 f s a = c
```

**W2: the right endpoint.** For `hf : ContDiff ℝ 1 f` and `hab : a < b`, `derivWithin f (Set.Icc a b) b =
deriv f b`: `apply (hf.differentiable (by norm_num) b).derivWithin` (R7, R8), then
`exact uniqueDiffOn_Icc hab b ⟨hab.le, le_rfl⟩` (R9, with the membership pair of R10 reversed):

```lean-goal
⊢ derivWithin f (Set.Icc a b) b = deriv f b
⊢ UniqueDiffWithinAt ℝ (Set.Icc a b) b
```

---

## Part 2 · `forward_difference_error`

Statement: `|(f (x + h) - f x) / h - deriv f x| ≤ M * h / 2`, given `hf : ContDiff ℝ 2 f`, `hh : 0 < h` and
`hM : ∀ y, |iteratedDeriv 2 f y| ≤ M`. Get `ξ` and `hξ` from the milestone with `obtain ⟨ξ, hξ⟩` (R1 without
the `-`), prove the exact error `e : … = iteratedDeriv 2 f ξ * h / 2` (R14, R15), rewrite with it, then
bound (R16–R20).

**R14 · `field_simp`** changes the **goal**: it multiplies out the denominators of an equation. It needs each
denominator nonzero and finds `b ≠ 0` from `hb : 0 < b` in the context. Its output form is not predictable in
advance: look at the infoview. Placeholders: `(a b c d : ℝ) (hb : 0 < b)`.

| Before | After |
|---|---|
| `⊢ a / b - c = d / 3` | `⊢ (a - b * c) * 3 = b * d` |

**R15 · `linear_combination k * h`** **closes** a goal `L = R` when `L - R - k * (lhs - rhs)` is `0` by `ring`,
where `h : lhs = rhs`. You only choose the coefficient `k`. Placeholders: `(a b : ℝ) (h : a = 2 * b)`, goal
`3 * a = 6 * b`, closed by `linear_combination 3 * h`.

**R16 · `rw [abs_div]`** changes the **goal**. Lemma: `|a / b| = |a| / |b|`. Placeholders: `(a b : ℝ)`.
Before and after:

```lean-goal
⊢ P |a / b|
⊢ P (|a| / |b|)
```

**R17 · `rw [abs_mul]`** changes the **goal**. Lemma: `|a * b| = |a| * |b|`. Placeholders: `(a b : ℝ)`.

```lean-goal
⊢ P |a * b|
⊢ P (|a| * |b|)
```

**R18 · `rw [abs_of_pos ha]`** changes the **goal**. Lemma: `0 < a → |a| = a`. Placeholders: `(a : ℝ) (ha : 0 < a)`.

```lean-goal
⊢ P |a|
⊢ P a
```

**R19 · `rw [abs_two]`** changes the **goal**. Lemma: `|2| = 2`. Placeholders: none (`2 : ℝ`).

```lean-goal
⊢ P |2|
⊢ P 2
```

**R20 · `gcongr`** changes the **goal**: for an inequality whose two sides have the same shape, it matches the
common parts and leaves the differing pieces (`u ≤ v` from `u * c / d ≤ v * c / d`). Side goals such as
`0 ≤ c` are closed from hypotheses (`hc : 0 < c`); a leftover goal that is a hypothesis is closed too.
Placeholders: `(g : ℝ → ℝ) (K c y : ℝ) (hc : 0 < c)`.

| Before | After |
|---|---|
| `⊢ g y * c / 2 ≤ K * c / 2` | `⊢ g y ≤ K` |

Then `exact hM ξ` instantiates the `∀` hypothesis.

### Worked combinations (W3–W4)

**W3: an exact difference quotient.** From `hk : 0 < k` and `h : g (t + k) - g t = 3 * k + k ^ 2`:
`field_simp` (R14), then `linear_combination h` (R15):

```lean-goal
⊢ (g (t + k) - g t) / k - 3 = k
⊢ g (t + k) - g t - k * 3 = k ^ 2
```

**W4: a bound through absolute values.** From `ht : 0 < t` and `hc : |c| ≤ K`:
`rw [abs_div, abs_mul, abs_of_pos ht, abs_of_pos (by norm_num : (0 : ℝ) < 3)]` (R16, R17, R18 twice), then
`gcongr` (R20), which closes the leftover `|c| ≤ K` with `hc`:

```lean-goal
⊢ |c * t / 3| ≤ K * t / 3
⊢ |c| * t / 3 ≤ K * t / 3
```

---

## Traps

- The Taylor lemma's own variables are called `x` and `x₀`, as are yours. Pass them by name,
  `(x₀ := x) (x := x + h)`: the left `x` is the lemma's, the right is yours. Give `(n := 1)` too, or Lean cannot
  guess the degree.
- The lemma speaks of `Set.uIcc`, but `uniqueDiffOn_Icc` is about `Set.Icc`. Rewrite with `Set.uIcc_of_le`
  (R6) before R9.
- `hd` must be stated with `Set.uIcc x (x + h)` (not `Set.Icc`: R6 rewrites only inside `hd`'s own proof)
  and with the expansion point `x`, as in `hξ` after R11, or `rw [hd] at hξ` finds nothing. `hξ` shows
  `iteratedDerivWithin (0 + 1)`; `rw` still matches `hd`'s `1` there. Do R11 and R12 before `rw [hd]`.
- `hf.differentiable` needs `2 ≠ 0` in `WithTop ℕ∞`: pass `(by norm_num)` (R7).
- `field_simp` must see `h ≠ 0`; keep `hh : 0 < h` in the context (or add `have := hh.ne'`).
- `rw [e]` needs the left side of `e` literally in the goal: state `e` with exactly
  `(f (x + h) - f x) / h - deriv f x`.
- `ring` cannot use `hξ`; `linear_combination` (R15) can.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unpack `∃ y ∈ S, Q y` / `∃ y, Q y` | `obtain ⟨y, -, hy⟩ := h` / `obtain ⟨y, hy⟩ := h` | R1 |
| Taylor with Lagrange remainder, degree `n` | `taylor_mean_remainder_lagrange_iteratedDeriv (n := n) (x₀ := a) (x := b) hne hf` | R2 |
| `ContDiffOn` from `ContDiff` | `hf.contDiffOn` | R3 |
| linear fact (`<`, `≤`, `=`, `≠`) | `linarith` | R4 |
| `iteratedDerivWithin 1` → `derivWithin` | `rw [iteratedDerivWithin_one]` | R5 |
| `Set.uIcc a b` → `Set.Icc a b` | `rw [Set.uIcc_of_le (by linarith)]` | R6 |
| differentiable at `x` from `ContDiff ℝ 2 f` | `hf.differentiable (by norm_num) x` | R7 |
| `derivWithin f s x = deriv f x` | `hd.derivWithin hu` | R8 |
| uniqueness on `[a, b]` at `x` | `uniqueDiffOn_Icc hab x hx` | R9 |
| `a ∈ Set.Icc a b` | `⟨le_rfl, by linarith⟩` | R10 |
| degree `n + 1` Taylor polynomial → degree `n` + term | `rw [taylorWithinEval_succ] at hξ` | R11 |
| degree 0 → `f x₀` | `rw [taylor_within_zero_eval] at hξ` | R12 |
| clean the numerals in a hypothesis | `norm_num at hξ` | R13 |
| clear denominators | `field_simp` | R14 |
| equation from a hypothesis times a constant | `linear_combination k * h` | R15 |
| split `\|a / b\|`, `\|a * b\|` | `rw [abs_div, abs_mul]` | R16, R17 |
| `\|a\| → a` for `0 < a`, `\|2\| → 2` | `rw [abs_of_pos ha, abs_two]` | R18, R19 |
| strip common factors of an inequality | `gcongr` | R20 |
| see the state | infoview | |
